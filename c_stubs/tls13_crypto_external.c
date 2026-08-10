#include "tls13_crypto_external.h"

#include "tls13_hacl_stubs.h"

void TLS13_Crypto_sha256_empty(uint8_t *out) {
  (void)tls13_hacl_sha256(out, NULL, 0);
}

bool TLS13_Crypto_random_bytes(uint8_t *out, size_t out_len) {
  return tls13_hacl_random_bytes(out, out_len);
}

void TLS13_Crypto_sha256(
    uint8_t *input,
    size_t input_len,
    uint8_t *out) {
  (void)tls13_hacl_sha256(out, input, input_len);
}

void TLS13_Crypto_sha256_prefix(uint8_t *input, size_t input_len, uint8_t *out) {
  TLS13_Crypto_sha256(input, input_len, out);
}

void TLS13_Crypto_hmac_sha256(
    uint8_t *key,
    size_t key_len,
    uint8_t *msg,
    size_t msg_len,
    uint8_t *out) {
  (void)tls13_hacl_hmac_sha256(out, key, key_len, msg, msg_len);
}

bool TLS13_Crypto_equal32(uint8_t *a, uint8_t *b) {
  volatile uint8_t diff = 0;
  for (size_t i = 0; i < 32u; ++i) {
    diff = (uint8_t)(diff | (uint8_t)(a[i] ^ b[i]));
  }
  return diff == 0u;
}

bool TLS13_Crypto_equal12(uint8_t *a, uint8_t *b) {
  volatile uint8_t diff = 0;
  for (size_t i = 0; i < 12u; ++i) {
    diff = (uint8_t)(diff | (uint8_t)(a[i] ^ b[i]));
  }
  return diff == 0u;
}

void TLS13_Crypto_hkdf_extract(
    uint8_t *salt,
    size_t salt_len,
    uint8_t *ikm,
    size_t ikm_len,
    uint8_t *out) {
  (void)tls13_hacl_hkdf_extract_sha256(out, salt, salt_len, ikm, ikm_len);
}

void TLS13_Crypto_hkdf_expand(
    uint8_t *secret,
    uint8_t *info,
    size_t info_len,
    uint8_t *out,
    size_t out_len) {
  (void)tls13_hacl_hkdf_expand_sha256(out, out_len, secret, info, info_len);
}

bool TLS13_Crypto_x25519_shared_runtime(
    uint8_t *sk,
    uint8_t *pk,
    uint8_t *out) {
  return tls13_hacl_x25519_shared(out, sk, pk);
}

void TLS13_Crypto_x25519_public_from_private(
    uint8_t *sk,
    uint8_t *out) {
  (void)tls13_hacl_x25519_public_from_private(out, sk);
}

void TLS13_Crypto_aead_seal(
    uint8_t *key,
    size_t key_len,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out) {
  if (key_len == 16) {
    (void)tls13_hacl_aes128_gcm_seal_combined(
        out, plain_len + 16, key, nonce, aad, aad_len, plain, plain_len);
    return;
  }
  (void)tls13_hacl_chacha20_poly1305_seal_combined(
      out, plain_len + 16, key, nonce, aad, aad_len, plain, plain_len);
}

bool TLS13_Crypto_aead_open(
    uint8_t *key,
    size_t key_len,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out) {
  if (cipher_len < 16) {
    return false;
  }
  if (key_len == 16) {
    return tls13_hacl_aes128_gcm_open_combined(
        out, cipher_len - 16, key, nonce, aad, aad_len, cipher, cipher_len);
  }
  return tls13_hacl_chacha20_poly1305_open_combined(
      out, cipher_len - 16, key, nonce, aad, aad_len, cipher, cipher_len);
}
