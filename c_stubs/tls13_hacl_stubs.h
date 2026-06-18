#ifndef TLS13_HACL_STUBS_H
#define TLS13_HACL_STUBS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "tls13_spec_types.h"

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

bool tls13_hacl_hkdf_expand_label_sha256(
    uint8_t *out,
    size_t out_len,
    const uint8_t prk[32],
    const uint8_t *label,
    size_t label_len,
    const uint8_t *context,
    size_t context_len);

bool tls13_hacl_finished_verify_data_sha256(
    uint8_t out[32],
    const uint8_t base_key[32],
    const uint8_t transcript_hash[32]);

bool tls13_hacl_x25519_public_from_private(uint8_t out[32], const uint8_t sk[32]);

bool tls13_hacl_x25519_shared(uint8_t out[32], const uint8_t sk[32], const uint8_t pk[32]);

bool tls13_record_nonce(uint8_t out[12], const uint8_t static_iv[12], uint64_t sequence_number);

bool tls13_hacl_chacha20_poly1305_seal(
    uint8_t *ciphertext,
    uint8_t tag[16],
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *plaintext,
    size_t plaintext_len);

bool tls13_hacl_chacha20_poly1305_open(
    uint8_t *plaintext,
    const uint8_t key[32],
    const uint8_t nonce[12],
    const uint8_t *aad,
    size_t aad_len,
    const uint8_t *ciphertext,
    size_t ciphertext_len,
    const uint8_t tag[16]);

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

#ifndef TLS13_USE_EXTRACTED_RECORD
TLS13_Record_record_state TLS13_Record_record_state_new(void);
void TLS13_Record_record_state_free(TLS13_Record_record_state st);
bool TLS13_Record_can_advance_seq(TLS13_Record_record_state st);
bool TLS13_Record_seq_eq(TLS13_Record_record_state st, uint64_t expected);
bool TLS13_Record_application_keys_match(
    TLS13_Record_record_state st,
    uint8_t *key,
    uint8_t *iv);
bool TLS13_Record_has_seal_keys(TLS13_Record_record_state st);
void TLS13_Record_advance_seq(TLS13_Record_record_state st);
void TLS13_Record_install_keys(
    TLS13_Record_record_state st,
    TLS13_Record_Spec_epoch epoch,
    uint8_t *key,
    uint8_t *iv);
void TLS13_Record_install_handshake_keys_runtime(
    TLS13_Record_record_state st,
    uint8_t *key,
    uint8_t *iv);
void TLS13_Record_install_application_keys_runtime(
    TLS13_Record_record_state st,
    uint8_t *key,
    uint8_t *iv);
bool TLS13_Record_seal_application(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out);
bool TLS13_Record_seal_application_no_update(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out);
bool TLS13_Record_seal_application_runtime(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out);
bool TLS13_Record_open_application(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out);
bool TLS13_Record_peek_open_application(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out);
bool TLS13_Record_open_application_runtime(
    TLS13_Record_record_state st,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out);
#endif

#endif
