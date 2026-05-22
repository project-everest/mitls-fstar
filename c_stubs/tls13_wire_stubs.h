#ifndef TLS13_WIRE_STUBS_H
#define TLS13_WIRE_STUBS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define TLS13_WIRE_RECORD_HEADER_LEN 5u
#define TLS13_WIRE_HANDSHAKE_HEADER_LEN 4u
#define TLS13_WIRE_MAX_RECORD_FRAGMENT_LEN 16384u
#define TLS13_WIRE_MAX_HANDSHAKE_BODY_LEN 0x00ffffffu

bool tls13_wire_parse_record_header(
    const uint8_t *input,
    size_t input_len,
    uint8_t *content_type,
    uint16_t *legacy_version,
    uint16_t *fragment_len);

bool tls13_wire_serialize_record_header(
    uint8_t out[TLS13_WIRE_RECORD_HEADER_LEN],
    uint8_t content_type,
    uint16_t legacy_version,
    uint16_t fragment_len);

bool tls13_wire_parse_handshake_header(
    const uint8_t *input,
    size_t input_len,
    uint8_t *msg_type,
    uint32_t *body_len);

bool tls13_wire_serialize_handshake_header(
    uint8_t out[TLS13_WIRE_HANDSHAKE_HEADER_LEN],
    uint8_t msg_type,
    uint32_t body_len);

#endif
