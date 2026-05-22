#ifndef TLS13_CRYPTO_EXTERNAL_H
#define TLS13_CRYPTO_EXTERNAL_H

#include <stddef.h>
#include <stdint.h>

void TLS13_Crypto_sha256_empty(uint8_t *out, void *old_out);

void TLS13_Crypto_hmac_sha256(
    uint8_t *key,
    size_t key_len,
    uint8_t *msg,
    size_t msg_len,
    uint8_t *out,
    void *key_bytes,
    void *msg_bytes,
    void *old_out);

void TLS13_Crypto_hkdf_extract(
    uint8_t *salt,
    size_t salt_len,
    uint8_t *ikm,
    size_t ikm_len,
    uint8_t *out,
    void *salt_bytes,
    void *ikm_bytes,
    void *old_out);

void TLS13_Crypto_hkdf_expand_label(
    uint8_t *secret,
    uint8_t *label,
    size_t label_len,
    uint8_t *context,
    size_t context_len,
    uint8_t *out,
    size_t out_len,
    void *secret_bytes,
    void *label_bytes,
    void *context_bytes,
    void *old_out);

void TLS13_Crypto_hkdf_expand_label_empty_context(
    uint8_t *secret,
    uint8_t *label,
    size_t label_len,
    uint8_t *out,
    size_t out_len,
    void *secret_bytes,
    void *label_bytes,
    void *old_out);

#endif
