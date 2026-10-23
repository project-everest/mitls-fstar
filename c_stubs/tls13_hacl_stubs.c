#include "tls13_hacl_stubs.h"

#include <string.h>

#include "Hacl.h"
#include "Hacl_Random.h"

/* hacl-pulse (dist/Hacl.c) is extracted from Pulse, and its entry points do no
   argument checking of their own: each one assumes the precondition of its
   Pulse signature.  The guards below establish those preconditions -- buffer
   lengths, the 2^61 hash-input bound, the AEAD message bounds -- and Pulse's
   separation logic also requires every buffer written to be disjoint from the
   others, which our callers guarantee.  CPU feature dispatch (AES-NI, SHA
   extensions, AVX2) happens inside Hacl.c at run time. */

#define TLS13_HACL_HASH_MAX_INPUT ((uint64_t)1 << 61)
#define TLS13_HACL_SHA256_BLOCK 64u
#define TLS13_HACL_AEAD_MAX_PLAIN ((size_t)UINT32_MAX)

static uint8_t empty_input;

static bool hash_input_ok(size_t len, size_t extra) {
  return (uint64_t)len < TLS13_HACL_HASH_MAX_INPUT - extra &&
         len <= SIZE_MAX - extra;
}

static uint8_t *read_ptr(const uint8_t *p, size_t len) {
  return (uint8_t *)(len == 0 ? &empty_input : p);
}

static uint8_t *write_ptr(uint8_t *p, size_t len) {
  return len == 0 ? &empty_input : p;
}

bool tls13_hacl_random_bytes(uint8_t *out, size_t out_len) {
  if (out_len != 0 && out == NULL) {
    return false;
  }
  return Hacl_Random_bytes(write_ptr(out, out_len), out_len);
}

bool tls13_hacl_sha256(uint8_t out[32], const uint8_t *input, size_t input_len) {
  if (out == NULL || (input_len != 0 && input == NULL) ||
      !hash_input_ok(input_len, 0)) {
    return false;
  }
  Hacl_Hash_SHA2_sha256(out, read_ptr(input, input_len), input_len);
  return true;
}

bool tls13_hacl_hmac_sha256(
    uint8_t out[32],
    const uint8_t *key,
    size_t key_len,
    const uint8_t *input,
    size_t input_len) {
  if (out == NULL || (key_len != 0 && key == NULL) ||
      (input_len != 0 && input == NULL) || !hash_input_ok(key_len, 0) ||
      !hash_input_ok(input_len, TLS13_HACL_SHA256_BLOCK)) {
    return false;
  }
  Hacl_HMAC_hmac_sha256(
      out,
      read_ptr(key, key_len),
      key_len,
      read_ptr(input, input_len),
      input_len);
  return true;
}

bool tls13_hacl_hkdf_extract_sha256(
    uint8_t out[32],
    const uint8_t *salt,
    size_t salt_len,
    const uint8_t *ikm,
    size_t ikm_len) {
  if (out == NULL || (salt_len != 0 && salt == NULL) ||
      (ikm_len != 0 && ikm == NULL) || !hash_input_ok(salt_len, 0) ||
      !hash_input_ok(ikm_len, TLS13_HACL_SHA256_BLOCK)) {
    return false;
  }
  Hacl_HKDF_extract_sha256(
      out,
      read_ptr(salt, salt_len),
      salt_len,
      read_ptr(ikm, ikm_len),
      ikm_len);
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
      !hash_input_ok(info_len, TLS13_HACL_SHA256_BLOCK + 32u + 1u)) {
    return false;
  }
  Hacl_HKDF_expand_sha256(
      write_ptr(out, out_len),
      out_len,
      (uint8_t *)prk,
      32u,
      read_ptr(info, info_len),
      info_len);
  return true;
}

bool tls13_hacl_x25519_public_from_private(uint8_t out[32], const uint8_t sk[32]) {
  if (out == NULL || sk == NULL) {
    return false;
  }
  Hacl_Curve25519_secret_to_public(out, (uint8_t *)sk);
  return true;
}

bool tls13_hacl_x25519_shared(uint8_t out[32], const uint8_t sk[32], const uint8_t pk[32]) {
  if (out == NULL || sk == NULL || pk == NULL) {
    return false;
  }
  return Hacl_Curve25519_ecdh(out, (uint8_t *)sk, (uint8_t *)pk);
}

/* secp256r1 (NIST P-256) ECDH.

   TLS 1.3 puts the peer's share on the wire in the uncompressed SEC1 encoding,
   0x04 || X || Y, so 65 bytes; HACL works with the 64-byte raw X || Y form,
   hence the conversions.  RFC 8446 section 7.4.2 takes the shared secret to be
   the 32-byte X coordinate only, so the low 32 bytes of the 64-byte HACL
   output are what feeds the key schedule. */
bool tls13_hacl_p256_public_from_private(uint8_t out[65], const uint8_t sk[32]) {
  uint8_t raw[64];
  if (out == NULL || sk == NULL) {
    return false;
  }
  if (!Hacl_P256_Ecdh_dh_initiator(raw, (uint8_t *)sk)) {
    return false;
  }
  Hacl_P256_Sec1_raw_to_uncompressed(out, raw);
  return true;
}

bool tls13_hacl_p256_shared(uint8_t out[32], const uint8_t sk[32],
                            const uint8_t pk[65]) {
  uint8_t their_raw[64];
  uint8_t shared[64];
  if (out == NULL || sk == NULL || pk == NULL) {
    return false;
  }
  if (!Hacl_P256_Sec1_uncompressed_to_raw(their_raw, (uint8_t *)pk)) {
    return false;
  }
  if (!Hacl_P256_Key_Public_validate_public_key(their_raw)) {
    return false;
  }
  if (!Hacl_P256_Ecdh_dh_responder(shared, their_raw, (uint8_t *)sk)) {
    return false;
  }
  memcpy(out, shared, 32);
  return true;
}

static bool aead_args_ok(
    size_t plaintext_len,
    size_t ciphertext_and_tag_len,
    const uint8_t *key,
    const uint8_t *nonce,
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    const uint8_t *ciphertext_and_tag) {
  return plaintext_len <= TLS13_HACL_AEAD_MAX_PLAIN &&
         aad_len <= TLS13_HACL_AEAD_MAX_PLAIN &&
         ciphertext_and_tag_len == plaintext_len + 16 &&
         ciphertext_and_tag != NULL && key != NULL && nonce != NULL &&
         (aad_len == 0 || aad != NULL) &&
         (plaintext_len == 0 || plaintext != NULL);
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
  if (!aead_args_ok(plaintext_len, ciphertext_and_tag_len, key, nonce, aad,
                    aad_len, plaintext, ciphertext_and_tag)) {
    return false;
  }
  Hacl_Chacha20Poly1305_encrypt(
      write_ptr(ciphertext_and_tag, plaintext_len),
      ciphertext_and_tag + plaintext_len,
      read_ptr(plaintext, plaintext_len),
      plaintext_len,
      read_ptr(aad, aad_len),
      aad_len,
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
  if (!aead_args_ok(plaintext_len, ciphertext_and_tag_len, key, nonce, aad,
                    aad_len, plaintext, ciphertext_and_tag)) {
    return false;
  }
  return Hacl_Chacha20Poly1305_decrypt(
      write_ptr(plaintext, plaintext_len),
      read_ptr(ciphertext_and_tag, plaintext_len),
      plaintext_len,
      (uint8_t *)(ciphertext_and_tag + plaintext_len),
      read_ptr(aad, aad_len),
      aad_len,
      (uint8_t *)key,
      (uint8_t *)nonce);
}

/* ── AES-128-GCM ───────────────────────────────────────────────────────────
   hacl-pulse has a portable AES-GCM and an AES-NI/PCLMULQDQ one, chosen at run
   time, so the suite is always available.  Its GCM works in place: the message
   buffer is encrypted or decrypted where it stands, so the input is copied to
   the output first.  Each call expands the key; the stub stays stateless (and
   therefore trivially thread-safe). */

bool tls13_hacl_aes128_gcm_available(void) {
  return true;
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
  if (!aead_args_ok(plaintext_len, ciphertext_and_tag_len, key, nonce, aad,
                    aad_len, plaintext, ciphertext_and_tag)) {
    return false;
  }
  if (plaintext_len != 0) {
    memmove(ciphertext_and_tag, plaintext, plaintext_len);
  }
  Hacl_AES_GCM_aes128_encrypt(
      ciphertext_and_tag + plaintext_len,
      write_ptr(ciphertext_and_tag, plaintext_len),
      plaintext_len,
      (uint8_t *)key,
      (uint8_t *)nonce,
      12u,
      read_ptr(aad, aad_len),
      aad_len);
  return true;
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
  if (!aead_args_ok(plaintext_len, ciphertext_and_tag_len, key, nonce, aad,
                    aad_len, plaintext, ciphertext_and_tag)) {
    return false;
  }
  if (plaintext_len != 0) {
    memmove(plaintext, ciphertext_and_tag, plaintext_len);
  }
  if (!Hacl_AES_GCM_aes128_decrypt(
          write_ptr(plaintext, plaintext_len),
          plaintext_len,
          (uint8_t *)(ciphertext_and_tag + plaintext_len),
          (uint8_t *)key,
          (uint8_t *)nonce,
          12u,
          read_ptr(aad, aad_len),
          aad_len)) {
    if (plaintext_len != 0) {
      memset(plaintext, 0, plaintext_len);
    }
    return false;
  }
  return true;
}
