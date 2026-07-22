#include "tls13_hacl_stubs.h"

#include <limits.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl_AEAD_Chacha20Poly1305.h"
#if TLS13_HACL_HAS_SIMD256
#include "Hacl_AEAD_Chacha20Poly1305_Simd256.h"
#endif
#include "Hacl_Curve25519_51.h"
#include "Hacl_HMAC.h"
#include "Hacl_Hash_SHA2.h"
#include "Lib_RandomBuffer_System.h"

#ifndef TLS13_HACL_HAS_ACCEL
#define TLS13_HACL_HAS_ACCEL 0
#endif

#if TLS13_HACL_HAS_ACCEL
#include "EverCrypt_AutoConfig2.h"
#include "Hacl_Curve25519_64.h"
#include "internal/EverCrypt_HMAC.h"
#include "internal/EverCrypt_Hash.h"
#endif

static bool fits_u32(size_t len) {
  return len <= UINT32_MAX;
}

#if TLS13_HACL_HAS_ACCEL
static atomic_uint tls13_hacl_accel_init_state = ATOMIC_VAR_INIT(0);

static void tls13_hacl_init_acceleration(void) {
  unsigned int state =
      atomic_load_explicit(&tls13_hacl_accel_init_state, memory_order_acquire);
  if (state == 2) {
    return;
  }

  unsigned int expected = 0;
  if (atomic_compare_exchange_strong_explicit(
          &tls13_hacl_accel_init_state,
          &expected,
          1,
          memory_order_acq_rel,
          memory_order_acquire)) {
    EverCrypt_AutoConfig2_init();
    atomic_store_explicit(&tls13_hacl_accel_init_state, 2, memory_order_release);
    return;
  }

  while (atomic_load_explicit(&tls13_hacl_accel_init_state, memory_order_acquire) != 2) {
  }
}
#endif

#if TLS13_HACL_HAS_SIMD256
static bool tls13_hacl_has_simd256(void) {
  return __builtin_cpu_supports("avx2");
}
#endif

bool tls13_hacl_random_bytes(uint8_t *out, size_t out_len) {
  if (out_len != 0 && out == NULL) {
    return false;
  }
  if (!fits_u32(out_len)) {
    return false;
  }
  return Lib_RandomBuffer_System_randombytes(out, (uint32_t)out_len);
}

bool tls13_hacl_sha256(uint8_t out[32], const uint8_t *input, size_t input_len) {
  if (out == NULL || (input_len != 0 && input == NULL) || !fits_u32(input_len)) {
    return false;
  }
#if TLS13_HACL_HAS_ACCEL
  uint8_t empty = 0;
  tls13_hacl_init_acceleration();
  EverCrypt_Hash_Incremental_hash_256(
      out, (uint8_t *)(input_len == 0 ? &empty : input), (uint32_t)input_len);
#else
  uint8_t empty = 0;
  Hacl_Hash_SHA2_hash_256(
      out, (uint8_t *)(input_len == 0 ? &empty : input), (uint32_t)input_len);
#endif
  return true;
}

bool tls13_hacl_hmac_sha256(
    uint8_t out[32],
    const uint8_t *key,
    size_t key_len,
    const uint8_t *input,
    size_t input_len) {
  if (out == NULL || (key_len != 0 && key == NULL) ||
      (input_len != 0 && input == NULL) || !fits_u32(key_len) ||
      !fits_u32(input_len)) {
    return false;
  }
#if TLS13_HACL_HAS_ACCEL
  uint8_t empty = 0;
  tls13_hacl_init_acceleration();
  EverCrypt_HMAC_compute_sha2_256(
      out,
      (uint8_t *)(key_len == 0 ? &empty : key),
      (uint32_t)key_len,
      (uint8_t *)(input_len == 0 ? &empty : input),
      (uint32_t)input_len);
#else
  uint8_t empty = 0;
  Hacl_HMAC_compute_sha2_256(
      out,
      (uint8_t *)(key_len == 0 ? &empty : key),
      (uint32_t)key_len,
      (uint8_t *)(input_len == 0 ? &empty : input),
      (uint32_t)input_len);
#endif
  return true;
}

bool tls13_hacl_hkdf_extract_sha256(
    uint8_t out[32],
    const uint8_t *salt,
    size_t salt_len,
    const uint8_t *ikm,
    size_t ikm_len) {
  if (out == NULL || (salt_len != 0 && salt == NULL) ||
      (ikm_len != 0 && ikm == NULL) || !fits_u32(salt_len) || !fits_u32(ikm_len)) {
    return false;
  }
  return tls13_hacl_hmac_sha256(out, salt, salt_len, ikm, ikm_len);
}

bool tls13_hacl_hkdf_expand_sha256(
    uint8_t *out,
    size_t out_len,
    const uint8_t prk[32],
    const uint8_t *info,
    size_t info_len) {
  if ((out_len != 0 && out == NULL) || prk == NULL ||
      (info_len != 0 && info == NULL) || !fits_u32(out_len) || !fits_u32(info_len)) {
    return false;
  }
  if (out_len > 255u * 32u) {
    return false;
  }
  if (out_len == 0) {
    return true;
  }
  if (info_len > SIZE_MAX - 33) {
    return false;
  }

  enum { TLS13_HKDF_LABEL_INFO_MAX = 514 };
  uint8_t stack_input[32 + TLS13_HKDF_LABEL_INFO_MAX + 1];
  size_t input_capacity = 32 + info_len + 1;
  uint8_t *hmac_input =
      info_len <= TLS13_HKDF_LABEL_INFO_MAX ? stack_input : malloc(input_capacity);
  if (hmac_input == NULL) {
    return false;
  }

  if (info_len != 0) {
    memcpy(hmac_input + 32, info, info_len);
  }
  uint8_t previous[32];
  size_t produced = 0;
  uint8_t counter = 1;
  while (produced < out_len) {
    size_t prefix_len = produced == 0 ? 0 : sizeof previous;
    if (prefix_len != 0) {
      memcpy(hmac_input, previous, sizeof previous);
    }
    uint8_t *block_input = prefix_len == 0 ? hmac_input + 32 : hmac_input;
    hmac_input[32 + info_len] = counter;
    if (!tls13_hacl_hmac_sha256(
            previous, prk, 32, block_input, prefix_len + info_len + 1)) {
      if (hmac_input != stack_input) {
        free(hmac_input);
      }
      return false;
    }
    size_t remaining = out_len - produced;
    size_t block_len = remaining < sizeof previous ? remaining : sizeof previous;
    memcpy(out + produced, previous, block_len);
    produced += block_len;
    counter++;
  }

  if (hmac_input != stack_input) {
    free(hmac_input);
  }
  return true;
}

bool tls13_hacl_hkdf_expand_label_sha256(
    uint8_t *out,
    size_t out_len,
    const uint8_t prk[32],
    const uint8_t *label,
    size_t label_len,
    const uint8_t *context,
    size_t context_len) {
  static const uint8_t prefix[] = {'t', 'l', 's', '1', '3', ' '};
  uint8_t info[2 + 1 + sizeof prefix + 255 + 1 + 255];
  size_t full_label_len = sizeof prefix + label_len;
  size_t info_len = 2 + 1 + full_label_len + 1 + context_len;

  if ((out_len != 0 && out == NULL) || prk == NULL ||
      (label_len != 0 && label == NULL) || (context_len != 0 && context == NULL) ||
      out_len > UINT16_MAX || label_len > 249 || context_len > 255 ||
      !fits_u32(out_len)) {
    return false;
  }

  info[0] = (uint8_t)(out_len >> 8);
  info[1] = (uint8_t)out_len;
  info[2] = (uint8_t)full_label_len;
  memcpy(&info[3], prefix, sizeof prefix);
  if (label_len != 0) {
    memcpy(&info[3 + sizeof prefix], label, label_len);
  }
  info[3 + full_label_len] = (uint8_t)context_len;
  if (context_len != 0) {
    memcpy(&info[4 + full_label_len], context, context_len);
  }

  return tls13_hacl_hkdf_expand_sha256(out, out_len, prk, info, info_len);
}

bool tls13_hacl_x25519_public_from_private(uint8_t out[32], const uint8_t sk[32]) {
  if (out == NULL || sk == NULL) {
    return false;
  }
#if TLS13_HACL_HAS_ACCEL
  tls13_hacl_init_acceleration();
  if (EverCrypt_AutoConfig2_has_bmi2() && EverCrypt_AutoConfig2_has_adx()) {
    Hacl_Curve25519_64_secret_to_public(out, (uint8_t *)sk);
    return true;
  }
#endif
  Hacl_Curve25519_51_secret_to_public(out, (uint8_t *)sk);
  return true;
}

bool tls13_hacl_x25519_shared(uint8_t out[32], const uint8_t sk[32], const uint8_t pk[32]) {
  if (out == NULL || sk == NULL || pk == NULL) {
    return false;
  }
#if TLS13_HACL_HAS_ACCEL
  tls13_hacl_init_acceleration();
  if (EverCrypt_AutoConfig2_has_bmi2() && EverCrypt_AutoConfig2_has_adx()) {
    return Hacl_Curve25519_64_ecdh(out, (uint8_t *)sk, (uint8_t *)pk);
  }
#endif
  return Hacl_Curve25519_51_ecdh(out, (uint8_t *)sk, (uint8_t *)pk);
}

bool tls13_record_nonce(uint8_t out[12], const uint8_t static_iv[12], uint64_t sequence_number) {
  if (out == NULL || static_iv == NULL) {
    return false;
  }
  memcpy(out, static_iv, 12);
  for (size_t i = 0; i < 8; ++i) {
    uint8_t seq_byte = (uint8_t)(sequence_number >> (56 - 8 * i));
    out[4 + i] ^= seq_byte;
  }
  return true;
}

static bool tls13_hacl_chacha20_poly1305_seal(
    uint8_t *ciphertext,
    uint8_t tag[16],
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    size_t plaintext_len) {
  if ((plaintext_len != 0 && (ciphertext == NULL || plaintext == NULL)) ||
      (aad_len != 0 && aad == NULL) || tag == NULL || key == NULL || nonce == NULL ||
      !fits_u32(aad_len) || !fits_u32(plaintext_len)) {
    return false;
  }
#if TLS13_HACL_HAS_SIMD256
  if (tls13_hacl_has_simd256()) {
    Hacl_AEAD_Chacha20Poly1305_Simd256_encrypt(
        ciphertext,
        tag,
        (uint8_t *)plaintext,
        (uint32_t)plaintext_len,
        (uint8_t *)aad,
        (uint32_t)aad_len,
        (uint8_t *)key,
        (uint8_t *)nonce);
  } else
#endif
  {
    Hacl_AEAD_Chacha20Poly1305_encrypt(
        ciphertext,
        tag,
        (uint8_t *)plaintext,
        (uint32_t)plaintext_len,
        (uint8_t *)aad,
        (uint32_t)aad_len,
        (uint8_t *)key,
        (uint8_t *)nonce);
  }
  return true;
}

static bool tls13_hacl_chacha20_poly1305_open(
    uint8_t *plaintext,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *ciphertext,
    size_t ciphertext_len,
    const uint8_t tag[16]) {
  if ((ciphertext_len != 0 && (plaintext == NULL || ciphertext == NULL)) ||
      (aad_len != 0 && aad == NULL) || tag == NULL || key == NULL || nonce == NULL ||
      !fits_u32(aad_len) || !fits_u32(ciphertext_len)) {
    return false;
  }
#if TLS13_HACL_HAS_SIMD256
  if (tls13_hacl_has_simd256()) {
    return Hacl_AEAD_Chacha20Poly1305_Simd256_decrypt(
               plaintext,
               (uint8_t *)ciphertext,
               (uint32_t)ciphertext_len,
               (uint8_t *)aad,
               (uint32_t)aad_len,
               (uint8_t *)key,
               (uint8_t *)nonce,
               (uint8_t *)tag) == 0;
  }
#endif
  return Hacl_AEAD_Chacha20Poly1305_decrypt(
           plaintext,
           (uint8_t *)ciphertext,
           (uint32_t)ciphertext_len,
           (uint8_t *)aad,
           (uint32_t)aad_len,
           (uint8_t *)key,
           (uint8_t *)nonce,
           (uint8_t *)tag) == 0;
}

bool tls13_hacl_chacha20_poly1305_seal_combined(
    uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    size_t plaintext_len) {
  if (plaintext_len > SIZE_MAX - 16 || ciphertext_and_tag_len != plaintext_len + 16) {
    return false;
  }
  return tls13_hacl_chacha20_poly1305_seal(
      ciphertext_and_tag,
      ciphertext_and_tag + plaintext_len,
      key,
      nonce,
      aad,
      aad_len,
      plaintext,
      plaintext_len);
}

bool tls13_hacl_chacha20_poly1305_open_combined(
    uint8_t *plaintext,
    size_t plaintext_len,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len) {
  if (plaintext_len > SIZE_MAX - 16 || ciphertext_and_tag_len != plaintext_len + 16) {
    return false;
  }
  return tls13_hacl_chacha20_poly1305_open(
      plaintext,
      key,
      nonce,
      aad,
      aad_len,
      ciphertext_and_tag,
      plaintext_len,
      ciphertext_and_tag + plaintext_len);
}
