#ifndef TLS13_HANDSHAKE_TRANSCRIPT_EXTERNAL_H
#define TLS13_HANDSHAKE_TRANSCRIPT_EXTERNAL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

bool TLS13_Handshake_Transcript_External_sha256_three(
    uint8_t *a,
    size_t a_len,
    uint8_t *b,
    size_t b_len,
    uint8_t *c,
    size_t c_len,
    uint8_t *out,
    void *a_bytes,
    void *b_bytes,
    void *c_bytes,
    void *old_out);

#endif
