#include "tls13_wire_stubs.h"

bool tls13_wire_parse_record_header(
    const uint8_t *input,
    size_t input_len,
    uint8_t *content_type,
    uint16_t *legacy_version,
    uint16_t *fragment_len) {
  if (input == NULL || content_type == NULL || legacy_version == NULL || fragment_len == NULL ||
      input_len < TLS13_WIRE_RECORD_HEADER_LEN) {
    return false;
  }

  uint16_t len = ((uint16_t)input[3] << 8) | (uint16_t)input[4];
  if (len > TLS13_WIRE_MAX_RECORD_FRAGMENT_LEN + 256u) {
    return false;
  }

  *content_type = input[0];
  *legacy_version = ((uint16_t)input[1] << 8) | (uint16_t)input[2];
  *fragment_len = len;
  return true;
}

bool tls13_wire_serialize_record_header(
    uint8_t out[TLS13_WIRE_RECORD_HEADER_LEN],
    uint8_t content_type,
    uint16_t legacy_version,
    uint16_t fragment_len) {
  if (out == NULL || fragment_len > TLS13_WIRE_MAX_RECORD_FRAGMENT_LEN + 256u) {
    return false;
  }
  out[0] = content_type;
  out[1] = (uint8_t)(legacy_version >> 8);
  out[2] = (uint8_t)legacy_version;
  out[3] = (uint8_t)(fragment_len >> 8);
  out[4] = (uint8_t)fragment_len;
  return true;
}

