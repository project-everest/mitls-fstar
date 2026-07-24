#include "tls13_hacl_stubs.h"

#include <limits.h>
#include <stdatomic.h>
#include <string.h>

#include "Hacl_AEAD_Chacha20Poly1305.h"
#if TLS13_HACL_HAS_SIMD256
#include "Hacl_AEAD_Chacha20Poly1305_Simd256.h"
#endif
#include "Hacl_Curve25519_51.h"
#include "Hacl_HKDF.h"
#include "Hacl_HMAC.h"
#include "Hacl_Hash_SHA2.h"
#include "Lib_RandomBuffer_System.h"

#ifndef TLS13_HACL_HAS_ACCEL
#define TLS13_HACL_HAS_ACCEL 0
#endif

#if TLS13_HACL_HAS_ACCEL
#include "EverCrypt_AutoConfig2.h"
#include "EverCrypt_Curve25519.h"
#include "EverCrypt_HKDF.h"
#include "internal/EverCrypt_HMAC.h"
#include "internal/EverCrypt_Hash.h"
#endif

static uint8_t empty_input;

static bool fits_u32(size_t len) {
  return len <= UINT32_MAX;
}

static uint8_t *read_ptr(const uint8_t *p, size_t len) {
  return (uint8_t *)(len == 0 ? &empty_input : p);
}

static uint8_t *write_ptr(uint8_t *p, size_t len) {
  return len == 0 ? &empty_input : p;
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
  if ((out_len != 0 && out == NULL) || !fits_u32(out_len)) {
    return false;
  }
  return Lib_RandomBuffer_System_randombytes(write_ptr(out, out_len), (uint32_t)out_len);
}

bool tls13_hacl_sha256(uint8_t out[32], const uint8_t *input, size_t input_len) {
  if (out == NULL || (input_len != 0 && input == NULL) || !fits_u32(input_len)) {
    return false;
  }
#if TLS13_HACL_HAS_ACCEL
  tls13_hacl_init_acceleration();
  EverCrypt_Hash_Incremental_hash_256(
      out, read_ptr(input, input_len), (uint32_t)input_len);
#else
  Hacl_Hash_SHA2_hash_256(out, read_ptr(input, input_len), (uint32_t)input_len);
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
      input_len > UINT32_MAX - 64u) {
    return false;
  }
#if TLS13_HACL_HAS_ACCEL
  tls13_hacl_init_acceleration();
  EverCrypt_HMAC_compute_sha2_256(
#else
  Hacl_HMAC_compute_sha2_256(
#endif
      out,
      read_ptr(key, key_len),
      (uint32_t)key_len,
      read_ptr(input, input_len),
      (uint32_t)input_len);
  return true;
}

bool tls13_hacl_hkdf_extract_sha256(
    uint8_t out[32],
    const uint8_t *salt,
    size_t salt_len,
    const uint8_t *ikm,
    size_t ikm_len) {
  if (out == NULL || (salt_len != 0 && salt == NULL) ||
      (ikm_len != 0 && ikm == NULL) || !fits_u32(salt_len) ||
      ikm_len > UINT32_MAX - 64u) {
    return false;
  }
#if TLS13_HACL_HAS_ACCEL
  tls13_hacl_init_acceleration();
  EverCrypt_HKDF_extract(
      Spec_Hash_Definitions_SHA2_256,
#else
  Hacl_HKDF_extract_sha2_256(
#endif
      out,
      read_ptr(salt, salt_len),
      (uint32_t)salt_len,
      read_ptr(ikm, ikm_len),
      (uint32_t)ikm_len);
  return true;
}

bool tls13_hacl_hkdf_expand_sha256(
    uint8_t *out,
    size_t out_len,
    const uint8_t prk[32],
    const uint8_t *info,
    size_t info_len) {
  if ((out_len != 0 && out == NULL) || prk == NULL ||
      (info_len != 0 && info == NULL) || out_len > 255u * 32u ||
      info_len > UINT32_MAX - 97u) {
    return false;
  }
#if TLS13_HACL_HAS_ACCEL
  tls13_hacl_init_acceleration();
  EverCrypt_HKDF_expand(
      Spec_Hash_Definitions_SHA2_256,
#else
  Hacl_HKDF_expand_sha2_256(
#endif
      write_ptr(out, out_len),
      (uint8_t *)prk,
      32u,
      read_ptr(info, info_len),
      (uint32_t)info_len,
      (uint32_t)out_len);
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
      out_len > UINT16_MAX || label_len > 249 || context_len > 255) {
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
  EverCrypt_Curve25519_secret_to_public(out, (uint8_t *)sk);
#else
  Hacl_Curve25519_51_secret_to_public(out, (uint8_t *)sk);
#endif
  return true;
}

bool tls13_hacl_x25519_shared(uint8_t out[32], const uint8_t sk[32], const uint8_t pk[32]) {
  if (out == NULL || sk == NULL || pk == NULL) {
    return false;
  }
#if TLS13_HACL_HAS_ACCEL
  tls13_hacl_init_acceleration();
  return EverCrypt_Curve25519_ecdh(out, (uint8_t *)sk, (uint8_t *)pk);
#else
  return Hacl_Curve25519_51_ecdh(out, (uint8_t *)sk, (uint8_t *)pk);
#endif
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

bool tls13_hacl_chacha20_poly1305_seal_combined(
    uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    size_t plaintext_len) {
  if (plaintext_len > UINT32_MAX || aad_len > UINT32_MAX ||
      plaintext_len > SIZE_MAX - 16 ||
      ciphertext_and_tag_len != plaintext_len + 16 ||
      ciphertext_and_tag == NULL || key == NULL || nonce == NULL ||
      (aad_len != 0 && aad == NULL) || (plaintext_len != 0 && plaintext == NULL)) {
    return false;
  }
#if TLS13_HACL_HAS_SIMD256
  if (tls13_hacl_has_simd256()) {
    Hacl_AEAD_Chacha20Poly1305_Simd256_encrypt(
        ciphertext_and_tag,
        ciphertext_and_tag + plaintext_len,
        read_ptr(plaintext, plaintext_len),
        (uint32_t)plaintext_len,
        read_ptr(aad, aad_len),
        (uint32_t)aad_len,
        (uint8_t *)key,
        (uint8_t *)nonce);
    return true;
  }
#endif
  Hacl_AEAD_Chacha20Poly1305_encrypt(
      ciphertext_and_tag,
      ciphertext_and_tag + plaintext_len,
      read_ptr(plaintext, plaintext_len),
      (uint32_t)plaintext_len,
      read_ptr(aad, aad_len),
      (uint32_t)aad_len,
      (uint8_t *)key,
      (uint8_t *)nonce);
  return true;
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
  if (plaintext_len > UINT32_MAX || aad_len > UINT32_MAX ||
      plaintext_len > SIZE_MAX - 16 ||
      ciphertext_and_tag_len != plaintext_len + 16 ||
      (plaintext_len != 0 && plaintext == NULL) || key == NULL || nonce == NULL ||
      (aad_len != 0 && aad == NULL) || ciphertext_and_tag == NULL) {
    return false;
  }
#if TLS13_HACL_HAS_SIMD256
  if (tls13_hacl_has_simd256()) {
    return Hacl_AEAD_Chacha20Poly1305_Simd256_decrypt(
               write_ptr(plaintext, plaintext_len),
               (uint8_t *)ciphertext_and_tag,
               (uint32_t)plaintext_len,
               read_ptr(aad, aad_len),
               (uint32_t)aad_len,
               (uint8_t *)key,
               (uint8_t *)nonce,
               (uint8_t *)(ciphertext_and_tag + plaintext_len)) == 0;
  }
#endif
  return Hacl_AEAD_Chacha20Poly1305_decrypt(
             write_ptr(plaintext, plaintext_len),
             (uint8_t *)ciphertext_and_tag,
             (uint32_t)plaintext_len,
             read_ptr(aad, aad_len),
             (uint32_t)aad_len,
             (uint8_t *)key,
             (uint8_t *)nonce,
             (uint8_t *)(ciphertext_and_tag + plaintext_len)) == 0;
}
