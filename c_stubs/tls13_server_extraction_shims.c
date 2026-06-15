#include "tls13_server_extraction_shims.h"

#include <string.h>

void TLS13_Impl_ConnectionState_Repr_copy_array_prefix_to_transcript(
    uint8_t *src,
    uint8_t *dst,
    size_t src_len,
    size_t dst_offset) {
  memcpy(dst + dst_offset, src, src_len);
}

void TLS13_Impl_Server_Material_copy_server_random_and_private_from_payload(
    uint8_t *payload,
    uint8_t *server_random,
    uint8_t *server_private_key) {
  memcpy(server_random, payload, 32u);
  memcpy(server_private_key, payload + 32u, 32u);
}
