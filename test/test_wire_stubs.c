#include "tls13_wire_stubs.h"

#include <stdio.h>
#include <string.h>

static int test_record_header_roundtrip(void) {
  uint8_t header[TLS13_WIRE_RECORD_HEADER_LEN];
  uint8_t content_type = 0;
  uint16_t version = 0;
  uint16_t len = 0;

  if (!tls13_wire_serialize_record_header(header, 23, 0x0303, 42)) {
    fprintf(stderr, "serialize record header failed\n");
    return 1;
  }

  static const uint8_t expected[TLS13_WIRE_RECORD_HEADER_LEN] = {23, 0x03, 0x03, 0x00, 0x2a};
  if (memcmp(header, expected, sizeof header) != 0) {
    fprintf(stderr, "serialized record header mismatch\n");
    return 1;
  }

  if (!tls13_wire_parse_record_header(header, sizeof header, &content_type, &version, &len)) {
    fprintf(stderr, "parse record header failed\n");
    return 1;
  }
  if (content_type != 23 || version != 0x0303 || len != 42) {
    fprintf(stderr, "parsed record header fields mismatch\n");
    return 1;
  }
  return 0;
}

static int test_record_header_rejects_malformed(void) {
  uint8_t short_header[4] = {23, 0x03, 0x03, 0x00};
  uint8_t too_large[TLS13_WIRE_RECORD_HEADER_LEN] = {23, 0x03, 0x03, 0x41, 0x01};
  uint8_t content_type = 0;
  uint16_t version = 0;
  uint16_t len = 0;

  if (tls13_wire_parse_record_header(
          short_header, sizeof short_header, &content_type, &version, &len)) {
    fprintf(stderr, "accepted short record header\n");
    return 1;
  }
  if (tls13_wire_parse_record_header(
          too_large, sizeof too_large, &content_type, &version, &len)) {
    fprintf(stderr, "accepted oversized record fragment length\n");
    return 1;
  }
  if (tls13_wire_serialize_record_header(NULL, 23, 0x0303, 42)) {
    fprintf(stderr, "serialized to null output\n");
    return 1;
  }
  if (tls13_wire_serialize_record_header(too_large, 23, 0x0303, 0x4101)) {
    fprintf(stderr, "serialized oversized record fragment length\n");
    return 1;
  }
  return 0;
}

static int test_handshake_header_roundtrip(void) {
  uint8_t header[TLS13_WIRE_HANDSHAKE_HEADER_LEN];
  uint8_t msg_type = 0;
  uint32_t body_len = 0;

  if (!tls13_wire_serialize_handshake_header(header, 1, 0x00012a)) {
    fprintf(stderr, "serialize handshake header failed\n");
    return 1;
  }

  static const uint8_t expected[TLS13_WIRE_HANDSHAKE_HEADER_LEN] = {1, 0x00, 0x01, 0x2a};
  if (memcmp(header, expected, sizeof header) != 0) {
    fprintf(stderr, "serialized handshake header mismatch\n");
    return 1;
  }

  if (!tls13_wire_parse_handshake_header(header, sizeof header, &msg_type, &body_len)) {
    fprintf(stderr, "parse handshake header failed\n");
    return 1;
  }
  if (msg_type != 1 || body_len != 0x00012a) {
    fprintf(stderr, "parsed handshake header fields mismatch\n");
    return 1;
  }
  return 0;
}

static int test_handshake_header_rejects_malformed(void) {
  uint8_t short_header[3] = {1, 0x00, 0x01};
  uint8_t out[TLS13_WIRE_HANDSHAKE_HEADER_LEN];
  uint8_t msg_type = 0;
  uint32_t body_len = 0;

  if (tls13_wire_parse_handshake_header(short_header, sizeof short_header, &msg_type, &body_len)) {
    fprintf(stderr, "accepted short handshake header\n");
    return 1;
  }
  if (tls13_wire_serialize_handshake_header(NULL, 1, 0)) {
    fprintf(stderr, "serialized handshake header to null output\n");
    return 1;
  }
  if (tls13_wire_serialize_handshake_header(out, 1, TLS13_WIRE_MAX_HANDSHAKE_BODY_LEN + 1u)) {
    fprintf(stderr, "serialized oversized handshake body length\n");
    return 1;
  }
  return 0;
}

int main(void) {
  int failed = 0;
  failed |= test_record_header_roundtrip();
  failed |= test_record_header_rejects_malformed();
  failed |= test_handshake_header_roundtrip();
  failed |= test_handshake_header_rejects_malformed();
  if (failed != 0) {
    return 1;
  }
  printf("wire stub tests passed\n");
  return 0;
}
