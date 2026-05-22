#ifndef TLS13_WIRE_STUBS_H
#define TLS13_WIRE_STUBS_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define TLS13_WIRE_RECORD_HEADER_LEN 5u
#define TLS13_WIRE_HANDSHAKE_HEADER_LEN 4u
#define TLS13_WIRE_MAX_RECORD_FRAGMENT_LEN 16384u
#define TLS13_WIRE_MAX_HANDSHAKE_BODY_LEN 0x00ffffffu
#define TLS13_WIRE_MAX_HOSTNAME_LEN 255u

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

bool tls13_wire_parse_supported_server_hello(
    const uint8_t *input,
    size_t input_len,
    uint8_t random[32],
    uint8_t key_share[32]);

bool tls13_wire_serialize_supported_client_hello(
    uint8_t *out,
    size_t out_len,
    const uint8_t random[32],
    const uint8_t key_share[32],
    const uint8_t *hostname,
    size_t hostname_len,
    size_t *written);

bool tls13_wire_encode_inner_plaintext(
    uint8_t *out,
    size_t out_len,
    const uint8_t *plaintext,
    size_t plaintext_len,
    uint8_t content_type,
    size_t padding_len);

bool tls13_wire_decode_inner_plaintext(
    const uint8_t *inner_plaintext,
    size_t inner_plaintext_len,
    uint8_t *content_type,
    size_t *plaintext_len);

#endif
