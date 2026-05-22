#ifndef TLS13_OPENSSL_STUBS_H
#define TLS13_OPENSSL_STUBS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct tls13_peer_identity_s tls13_peer_identity;

#define TLS13_SIG_RSA_PSS_RSAE_SHA256 ((uint16_t)0x0804u)

bool tls13_openssl_validate_chain_pem(
    const char *hostname,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    const uint8_t *chain_pem,
    size_t chain_pem_len,
    tls13_peer_identity **out_peer);

bool tls13_openssl_peer_verify_signature(
    const tls13_peer_identity *peer,
    uint16_t signature_scheme,
    const uint8_t *message,
    size_t message_len,
    const uint8_t *signature,
    size_t signature_len);

void tls13_openssl_peer_identity_free(tls13_peer_identity *peer);

#endif
