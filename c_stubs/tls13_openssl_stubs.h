#ifndef TLS13_OPENSSL_STUBS_H
#define TLS13_OPENSSL_STUBS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct tls13_peer_identity_s tls13_peer_identity;

bool tls13_openssl_validate_chain_pem(
    const char *hostname,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    const uint8_t *chain_pem,
    size_t chain_pem_len,
    tls13_peer_identity **out_peer);

void tls13_openssl_peer_identity_free(tls13_peer_identity *peer);

#endif
