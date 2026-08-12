#ifndef TLS13_HACL_STUBS_H
#define TLS13_HACL_STUBS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

bool tls13_hacl_random_bytes(uint8_t *out, size_t out_len);

bool tls13_hacl_sha256(uint8_t out[32], const uint8_t *input, size_t input_len);

bool tls13_hacl_hmac_sha256(
    uint8_t out[32],
    const uint8_t *key,
    size_t key_len,
    const uint8_t *input,
    size_t input_len);

bool tls13_hacl_hkdf_extract_sha256(
    uint8_t out[32],
    const uint8_t *salt,
    size_t salt_len,
    const uint8_t *ikm,
    size_t ikm_len);

bool tls13_hacl_hkdf_expand_sha256(
    uint8_t *out,
    size_t out_len,
    const uint8_t prk[32],
    const uint8_t *info,
    size_t info_len);

bool tls13_hacl_x25519_public_from_private(uint8_t out[32], const uint8_t sk[32]);

bool tls13_hacl_x25519_shared(uint8_t out[32], const uint8_t sk[32], const uint8_t pk[32]);

bool tls13_hacl_p256_public_from_private(uint8_t out[65], const uint8_t sk[32]);

bool tls13_hacl_p256_shared(uint8_t out[32], const uint8_t sk[32], const uint8_t pk[65]);

bool tls13_hacl_chacha20_poly1305_seal_combined(
    uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    size_t plaintext_len);

bool tls13_hacl_chacha20_poly1305_open_combined(
    uint8_t *plaintext,
    size_t plaintext_len,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len);

/* Whether this build/CPU can run AES-128-GCM.  The ClientHello offer is
   filtered on this so we never negotiate a suite we cannot execute. */
bool tls13_hacl_aes128_gcm_available(void);

bool tls13_hacl_aes128_gcm_seal_combined(
    uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len,
    const uint8_t key[16],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    size_t plaintext_len);

bool tls13_hacl_aes128_gcm_open_combined(
    uint8_t *plaintext,
    size_t plaintext_len,
    const uint8_t key[16],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *ciphertext_and_tag,
    size_t ciphertext_and_tag_len);

#endif
