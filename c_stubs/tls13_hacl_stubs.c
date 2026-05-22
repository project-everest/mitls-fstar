#include "tls13_hacl_stubs.h"

#include <limits.h>

#include "Hacl_AEAD_Chacha20Poly1305.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_HKDF.h"
#include "Hacl_HMAC.h"
#include "Hacl_Hash_SHA2.h"
#include "Lib_RandomBuffer_System.h"

static bool fits_u32(size_t len) {
  return len <= UINT32_MAX;
}

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
  Hacl_Hash_SHA2_hash_256(out, (uint8_t *)input, (uint32_t)input_len);
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
  Hacl_HMAC_compute_sha2_256(
      out, (uint8_t *)key, (uint32_t)key_len, (uint8_t *)input, (uint32_t)input_len);
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
  Hacl_HKDF_extract_sha2_256(
      out, (uint8_t *)salt, (uint32_t)salt_len, (uint8_t *)ikm, (uint32_t)ikm_len);
  return true;
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
  Hacl_HKDF_expand_sha2_256(
      out, (uint8_t *)prk, 32, (uint8_t *)info, (uint32_t)info_len, (uint32_t)out_len);
  return true;
}

bool tls13_hacl_x25519_public_from_private(uint8_t out[32], const uint8_t sk[32]) {
  if (out == NULL || sk == NULL) {
    return false;
  }
  Hacl_Curve25519_51_secret_to_public(out, (uint8_t *)sk);
  return true;
}

bool tls13_hacl_x25519_shared(uint8_t out[32], const uint8_t sk[32], const uint8_t pk[32]) {
  if (out == NULL || sk == NULL || pk == NULL) {
    return false;
  }
  return Hacl_Curve25519_51_ecdh(out, (uint8_t *)sk, (uint8_t *)pk);
}

bool tls13_hacl_chacha20_poly1305_seal(
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
  Hacl_AEAD_Chacha20Poly1305_encrypt(
      ciphertext,
      tag,
      (uint8_t *)plaintext,
      (uint32_t)plaintext_len,
      (uint8_t *)aad,
      (uint32_t)aad_len,
      (uint8_t *)key,
      (uint8_t *)nonce);
  return true;
}

bool tls13_hacl_chacha20_poly1305_open(
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

