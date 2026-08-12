#include "tls13_hacl_stubs.h"

#include <limits.h>
#include <threads.h>

#include "Hacl_AEAD_Chacha20Poly1305.h"
#if TLS13_HACL_HAS_SIMD256
#include "Hacl_AEAD_Chacha20Poly1305_Simd256.h"
#endif
#include "Hacl_Curve25519_51.h"
#include "Hacl_HKDF.h"
#include "Hacl_HMAC.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_P256.h"
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

/* AES-128-GCM is provided by EverCrypt, which on x86_64 dispatches to the Vale
   verified assembly in aesgcm-x86_64-linux.S.  That code path requires AES-NI
   and PCLMULQDQ; EverCrypt_AEAD_create_in reports UnsupportedAlgorithm when
   they are absent, which tls13_hacl_aes128_gcm_available() surfaces so the
   ClientHello can drop TLS_AES_128_GCM_SHA256 from its offer rather than
   negotiating a suite we cannot run. */
#ifndef TLS13_HACL_HAS_AESGCM
#define TLS13_HACL_HAS_AESGCM 0
#endif

#if TLS13_HACL_HAS_AESGCM
#include "EverCrypt_AEAD.h"
#include "EverCrypt_Error.h"
#include "Hacl_Spec.h"
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
static once_flag tls13_hacl_accel_init_once = ONCE_FLAG_INIT;

static void tls13_hacl_init_acceleration(void) {
  call_once(&tls13_hacl_accel_init_once, EverCrypt_AutoConfig2_init);
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

/* secp256r1 (NIST P-256) ECDH.

   TLS 1.3 puts the peer's share on the wire in the uncompressed SEC1 encoding,
   0x04 || X || Y, so 65 bytes; HACL* works with the 64-byte raw X || Y form,
   hence the conversions.  RFC 8446 section 7.4.2 takes the shared secret to be
   the 32-byte X coordinate only, so the low 32 bytes of the 64-byte HACL*
   output are what feeds the key schedule. */
bool tls13_hacl_p256_public_from_private(uint8_t out[65], const uint8_t sk[32]) {
  uint8_t raw[64];
  if (out == NULL || sk == NULL) {
    return false;
  }
  if (!Hacl_P256_dh_initiator(raw, (uint8_t *)sk)) {
    return false;
  }
  Hacl_P256_raw_to_uncompressed(raw, out);
  return true;
}

bool tls13_hacl_p256_shared(uint8_t out[32], const uint8_t sk[32],
                            const uint8_t pk[65]) {
  uint8_t their_raw[64];
  uint8_t shared[64];
  if (out == NULL || sk == NULL || pk == NULL) {
    return false;
  }
  if (!Hacl_P256_uncompressed_to_raw((uint8_t *)pk, their_raw)) {
    return false;
  }
  if (!Hacl_P256_validate_public_key(their_raw)) {
    return false;
  }
  if (!Hacl_P256_dh_responder(shared, their_raw, (uint8_t *)sk)) {
    return false;
  }
  memcpy(out, shared, 32);
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

/* ── AES-128-GCM ───────────────────────────────────────────────────────────
   EverCrypt owns the key schedule, so each call expands the key.  TLS record
   protection installs a traffic key once and then uses it for many records;
   the expansion is a handful of AES rounds against a per-record cost that is
   linear in the record size, so this stays off the hot path's critical term
   while keeping the stub stateless (and therefore trivially thread-safe).  */

bool tls13_hacl_aes128_gcm_available(void) {
#if TLS13_HACL_HAS_AESGCM
  EverCrypt_AEAD_state_s *st = NULL;
  uint8_t probe_key[16] = {0};
  tls13_hacl_init_acceleration();
  if (EverCrypt_AEAD_create_in(Spec_Agile_AEAD_AES128_GCM, &st, probe_key) !=
      EverCrypt_Error_Success) {
    return false;
  }
  EverCrypt_AEAD_free(st);
  return true;
#else
  return false;
#endif
}

bool tls13_hacl_aes128_gcm_seal_combined(
    uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len,
    const uint8_t key[16],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    size_t plaintext_len) {
#if TLS13_HACL_HAS_AESGCM
  EverCrypt_AEAD_state_s *st = NULL;
  EverCrypt_Error_error_code rc;
  if (plaintext_len > UINT32_MAX || aad_len > UINT32_MAX ||
      plaintext_len > SIZE_MAX - 16 ||
      ciphertext_and_tag_len != plaintext_len + 16 ||
      ciphertext_and_tag == NULL || key == NULL || nonce == NULL ||
      (aad_len != 0 && aad == NULL) || (plaintext_len != 0 && plaintext == NULL)) {
    return false;
  }
  tls13_hacl_init_acceleration();
  if (EverCrypt_AEAD_create_in(Spec_Agile_AEAD_AES128_GCM, &st, (uint8_t *)key) !=
      EverCrypt_Error_Success) {
    return false;
  }
  rc = EverCrypt_AEAD_encrypt(
      st,
      (uint8_t *)nonce,
      12U,
      read_ptr(aad, aad_len),
      (uint32_t)aad_len,
      read_ptr(plaintext, plaintext_len),
      (uint32_t)plaintext_len,
      ciphertext_and_tag,
      ciphertext_and_tag + plaintext_len);
  EverCrypt_AEAD_free(st);
  return rc == EverCrypt_Error_Success;
#else
  (void)ciphertext_and_tag; (void)ciphertext_and_tag_len; (void)key;
  (void)nonce; (void)aad; (void)aad_len; (void)plaintext; (void)plaintext_len;
  return false;
#endif
}

bool tls13_hacl_aes128_gcm_open_combined(
    uint8_t *plaintext,
    size_t plaintext_len,
    const uint8_t key[16],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len) {
#if TLS13_HACL_HAS_AESGCM
  EverCrypt_AEAD_state_s *st = NULL;
  EverCrypt_Error_error_code rc;
  if (plaintext_len > UINT32_MAX || aad_len > UINT32_MAX ||
      plaintext_len > SIZE_MAX - 16 ||
      ciphertext_and_tag_len != plaintext_len + 16 ||
      (plaintext_len != 0 && plaintext == NULL) || key == NULL || nonce == NULL ||
      (aad_len != 0 && aad == NULL) || ciphertext_and_tag == NULL) {
    return false;
  }
  tls13_hacl_init_acceleration();
  if (EverCrypt_AEAD_create_in(Spec_Agile_AEAD_AES128_GCM, &st, (uint8_t *)key) !=
      EverCrypt_Error_Success) {
    return false;
  }
  rc = EverCrypt_AEAD_decrypt(
      st,
      (uint8_t *)nonce,
      12U,
      read_ptr(aad, aad_len),
      (uint32_t)aad_len,
      (uint8_t *)ciphertext_and_tag,
      (uint32_t)plaintext_len,
      (uint8_t *)(ciphertext_and_tag + plaintext_len),
      write_ptr(plaintext, plaintext_len));
  EverCrypt_AEAD_free(st);
  return rc == EverCrypt_Error_Success;
#else
  (void)plaintext; (void)plaintext_len; (void)key; (void)nonce;
  (void)aad; (void)aad_len; (void)ciphertext_and_tag; (void)ciphertext_and_tag_len;
  return false;
#endif
}
