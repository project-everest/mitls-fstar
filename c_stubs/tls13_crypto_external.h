#ifndef TLS13_CRYPTO_EXTERNAL_H
#define TLS13_CRYPTO_EXTERNAL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

void TLS13_Crypto_sha256_empty(uint8_t *out);

bool TLS13_Crypto_random_bytes(uint8_t *out, size_t out_len);

void TLS13_Crypto_sha256(
    uint8_t *input,
    size_t input_len,
    uint8_t *out);

void TLS13_Crypto_sha256_prefix(uint8_t *input, size_t input_len, uint8_t *out);

void TLS13_Crypto_hmac_sha256(
    uint8_t *key,
    size_t key_len,
    uint8_t *msg,
    size_t msg_len,
    uint8_t *out);

bool TLS13_Crypto_equal32(uint8_t *a, uint8_t *b);

bool TLS13_Crypto_equal12(uint8_t *a, uint8_t *b);

void TLS13_Crypto_hkdf_extract(
    uint8_t *salt,
    size_t salt_len,
    uint8_t *ikm,
    size_t ikm_len,
    uint8_t *out);

void TLS13_Crypto_hkdf_expand(
    uint8_t *secret,
    uint8_t *info,
    size_t info_len,
    uint8_t *out,
    size_t out_len);

bool TLS13_Crypto_x25519_shared_runtime(
    uint8_t *sk,
    uint8_t *pk,
    uint8_t *out);

void TLS13_Crypto_x25519_public_from_private(
    uint8_t *sk,
    uint8_t *out);

/* AEAD.  There is one raw binding per algorithm and each maps to exactly one
   primitive; no key length or algorithm identifier is passed, and no dispatch
   happens here.  The choice of algorithm for the negotiated cipher suite is
   made by verified Pulse code in TLS13.AEAD, which branches on the algorithm
   itself. */

/* key is 32 bytes, nonce 12, out is plain_len + 16. */
void TLS13_Crypto_chacha20_poly1305_seal(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out);

/* key is 32 bytes, nonce 12, cipher_len >= 16, out is cipher_len - 16. */
bool TLS13_Crypto_chacha20_poly1305_open(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out);

/* key is 16 bytes, nonce 12, out is plain_len + 16. */
void TLS13_Crypto_aes128_gcm_seal(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out);

/* key is 16 bytes, nonce 12, cipher_len >= 16, out is cipher_len - 16. */
bool TLS13_Crypto_aes128_gcm_open(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out);

#endif
