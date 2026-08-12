#ifndef TLS13_OPENSSL_STUBS_H
#define TLS13_OPENSSL_STUBS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct tls13_peer_identity_s tls13_peer_identity;
typedef struct tls13_server_credentials_s tls13_server_credentials;
typedef struct tls13_trust_store_s tls13_trust_store;

#define TLS13_SIG_RSA_PSS_RSAE_SHA256 ((uint16_t)0x0804u)
#define TLS13_SIG_ECDSA_SECP256R1_SHA256 ((uint16_t)0x0403u)

bool tls13_openssl_validate_leaf_der(
    const char *hostname,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    const uint8_t *leaf_der,
    size_t leaf_der_len,
    tls13_peer_identity **out_peer);

tls13_trust_store *tls13_openssl_trust_store_new(
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len);

bool tls13_openssl_validate_leaf_der_with_store(
    const char *hostname,
    const tls13_trust_store *trust_store,
    size_t validation_time_seconds,
    const uint8_t *leaf_der,
    size_t leaf_der_len,
    tls13_peer_identity **out_peer);

/* As above, but additionally supplies the certificates the peer sent alongside
   the leaf.  Public certificate authorities issue end-entity certificates from
   intermediate CAs, so the leaf is essentially never signed directly by a
   configured trust anchor: without the intermediates OpenSSL cannot build a
   chain and validation fails with "unable to get local issuer certificate".
   The extra certificates are *untrusted* chain-building material only; trust
   decisions still come exclusively from `trust_store`.

   `chain_der` holds the DER encoding of every certificate the peer sent, with
   entry `i` occupying `chain_der[chain_offsets[i] .. chain_offsets[i] +
   chain_lens[i])`.  Entry 0 is the leaf and is skipped here, since it is passed
   separately as `leaf_der`. */
bool tls13_openssl_validate_leaf_der_with_store_and_chain(
    const char *hostname,
    const tls13_trust_store *trust_store,
    size_t validation_time_seconds,
    const uint8_t *leaf_der,
    size_t leaf_der_len,
    const uint8_t *chain_der,
    size_t chain_der_len,
    const size_t *chain_offsets,
    const size_t *chain_lens,
    size_t chain_count,
    tls13_peer_identity **out_peer);

bool tls13_openssl_peer_verify_signature(
    const tls13_peer_identity *peer,
    uint16_t signature_scheme,
    const uint8_t *message,
    size_t message_len,
    const uint8_t *signature,
    size_t signature_len);

bool tls13_openssl_peer_copy_public_key_der(
    const tls13_peer_identity *peer,
    uint8_t *out,
    size_t out_capacity,
    size_t *out_len);

tls13_server_credentials *tls13_openssl_server_credentials_new(
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key,
    size_t private_key_len);

bool tls13_openssl_server_sign_rsa_pss_sha256(
    const tls13_server_credentials *creds,
    const uint8_t *message,
    size_t message_len,
    uint8_t *signature,
    size_t signature_capacity,
    size_t *signature_len);

bool tls13_openssl_server_copy_certificate_chain(
    const tls13_server_credentials *creds,
    uint8_t *out,
    size_t out_capacity,
    size_t *out_len);

void tls13_openssl_peer_identity_free(tls13_peer_identity *peer);

void tls13_openssl_trust_store_free(tls13_trust_store *trust_store);

void tls13_openssl_server_credentials_free(tls13_server_credentials *creds);

#ifdef __cplusplus
}
#endif

#endif
