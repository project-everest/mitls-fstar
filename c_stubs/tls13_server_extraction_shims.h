#ifndef TLS13_SERVER_EXTRACTION_SHIMS_H
#define TLS13_SERVER_EXTRACTION_SHIMS_H

#include <stddef.h>
#include <stdint.h>

void TLS13_Impl_ConnectionState_Repr_copy_array_prefix_to_transcript(
    uint8_t *src,
    uint8_t *dst,
    size_t src_len,
    size_t dst_offset);

void TLS13_Impl_Server_Material_copy_server_random_and_private_from_payload(
    uint8_t *payload,
    uint8_t *server_random,
    uint8_t *server_private_key);

#endif
