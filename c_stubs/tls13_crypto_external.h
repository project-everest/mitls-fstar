#ifndef TLS13_CRYPTO_EXTERNAL_H
#define TLS13_CRYPTO_EXTERNAL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef uint8_t TLS13_Record_Spec_epoch;

void Pulse_Lib_Array_memcpy(
    size_t len,
    uint8_t *src,
    uint8_t *dst,
    void *src_bytes,
    void *dst_bytes,
    void *squash);

void Pulse_Lib_Array_memcpy_l(
    size_t len,
    uint8_t *src,
    uint8_t *dst,
    void *src_bytes,
    void *dst_bytes,
    void *squash);

void TLS13_Crypto_sha256_empty(uint8_t *out, void *old_out);

void TLS13_Crypto_sha256(
    uint8_t *input,
    size_t input_len,
    uint8_t *out,
    void *msg,
    void *old_out);

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

bool TLS13_Crypto_x25519_shared_runtime(
    uint8_t *sk,
    uint8_t *pk,
    uint8_t *out,
    void *sk_bytes,
    void *pk_bytes,
    void *old_out);

bool TLS13_Crypto_tls13_record_nonce(
    uint8_t *static_iv,
    uint64_t sequence_number,
    uint8_t *out,
    void *iv_bytes,
    void *old_out);

void TLS13_Crypto_chacha20_poly1305_seal(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out,
    void *key_bytes,
    void *nonce_bytes,
    void *aad_bytes,
    void *plain_bytes,
    void *old_out);

bool TLS13_Crypto_chacha20_poly1305_open(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out,
    void *key_bytes,
    void *nonce_bytes,
    void *aad_bytes,
    void *cipher_bytes,
    void *old_out);

#endif
