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

static int test_supported_server_hello_scoped(void) {
  static const uint8_t server_hello[] = {
      0x02, 0x00, 0x00, 0x56, 0x03, 0x03, 0xa6, 0xaf,
      0x06, 0xa4, 0x12, 0x18, 0x60, 0xdc, 0x5e, 0x6e,
      0x60, 0x24, 0x9c, 0xd3, 0x4c, 0x95, 0x93, 0x0c,
      0x8a, 0xc5, 0xcb, 0x14, 0x34, 0xda, 0xc1, 0x55,
      0x77, 0x2e, 0xd3, 0xe2, 0x69, 0x28, 0x00, 0x13,
      0x03, 0x00, 0x00, 0x2e, 0x00, 0x33, 0x00, 0x24,
      0x00, 0x1d, 0x00, 0x20, 0xc9, 0x82, 0x88, 0x76,
      0x11, 0x20, 0x95, 0xfe, 0x66, 0x76, 0x2b, 0xdb,
      0xf7, 0xc6, 0x72, 0xe1, 0x56, 0xd6, 0xcc, 0x25,
      0x3b, 0x83, 0x3d, 0xf1, 0xdd, 0x69, 0xb1, 0xb0,
      0x4e, 0x75, 0x1f, 0x0f, 0x00, 0x2b, 0x00, 0x02,
      0x03, 0x04};
  static const uint8_t expected_random[32] = {
      0xa6, 0xaf, 0x06, 0xa4, 0x12, 0x18, 0x60, 0xdc,
      0x5e, 0x6e, 0x60, 0x24, 0x9c, 0xd3, 0x4c, 0x95,
      0x93, 0x0c, 0x8a, 0xc5, 0xcb, 0x14, 0x34, 0xda,
      0xc1, 0x55, 0x77, 0x2e, 0xd3, 0xe2, 0x69, 0x28};
  static const uint8_t expected_key_share[32] = {
      0xc9, 0x82, 0x88, 0x76, 0x11, 0x20, 0x95, 0xfe,
      0x66, 0x76, 0x2b, 0xdb, 0xf7, 0xc6, 0x72, 0xe1,
      0x56, 0xd6, 0xcc, 0x25, 0x3b, 0x83, 0x3d, 0xf1,
      0xdd, 0x69, 0xb1, 0xb0, 0x4e, 0x75, 0x1f, 0x0f};
  uint8_t random[32];
  uint8_t key_share[32];

  if (!tls13_wire_parse_supported_server_hello(
          server_hello, sizeof server_hello, random, key_share)) {
    fprintf(stderr, "failed to parse scoped supported ServerHello\n");
    return 1;
  }
  if (memcmp(random, expected_random, sizeof random) != 0 ||
      memcmp(key_share, expected_key_share, sizeof key_share) != 0) {
    fprintf(stderr, "parsed ServerHello fields mismatch\n");
    return 1;
  }
  return 0;
}

static int test_supported_server_hello_rejects_malformed(void) {
  static const uint8_t valid_server_hello[] = {
      0x02, 0x00, 0x00, 0x56, 0x03, 0x03, 0xa6, 0xaf,
      0x06, 0xa4, 0x12, 0x18, 0x60, 0xdc, 0x5e, 0x6e,
      0x60, 0x24, 0x9c, 0xd3, 0x4c, 0x95, 0x93, 0x0c,
      0x8a, 0xc5, 0xcb, 0x14, 0x34, 0xda, 0xc1, 0x55,
      0x77, 0x2e, 0xd3, 0xe2, 0x69, 0x28, 0x00, 0x13,
      0x03, 0x00, 0x00, 0x2e, 0x00, 0x33, 0x00, 0x24,
      0x00, 0x1d, 0x00, 0x20, 0xc9, 0x82, 0x88, 0x76,
      0x11, 0x20, 0x95, 0xfe, 0x66, 0x76, 0x2b, 0xdb,
      0xf7, 0xc6, 0x72, 0xe1, 0x56, 0xd6, 0xcc, 0x25,
      0x3b, 0x83, 0x3d, 0xf1, 0xdd, 0x69, 0xb1, 0xb0,
      0x4e, 0x75, 0x1f, 0x0f, 0x00, 0x2b, 0x00, 0x02,
      0x03, 0x04};
  uint8_t random[32];
  uint8_t key_share[32];
  uint8_t bad[sizeof valid_server_hello];

  if (tls13_wire_parse_supported_server_hello(NULL, sizeof valid_server_hello, random, key_share) ||
      tls13_wire_parse_supported_server_hello(valid_server_hello, sizeof valid_server_hello, NULL, key_share) ||
      tls13_wire_parse_supported_server_hello(valid_server_hello, sizeof valid_server_hello, random, NULL) ||
      tls13_wire_parse_supported_server_hello(valid_server_hello, 8, random, key_share)) {
    fprintf(stderr, "accepted malformed ServerHello arguments\n");
    return 1;
  }

  memcpy(bad, valid_server_hello, sizeof bad);
  bad[0] = 1;
  if (tls13_wire_parse_supported_server_hello(bad, sizeof bad, random, key_share)) {
    fprintf(stderr, "accepted non-ServerHello handshake type\n");
    return 1;
  }

  memcpy(bad, valid_server_hello, sizeof bad);
  bad[3] = 0x55;
  if (tls13_wire_parse_supported_server_hello(bad, sizeof bad, random, key_share)) {
    fprintf(stderr, "accepted bad ServerHello body length\n");
    return 1;
  }

  memcpy(bad, valid_server_hello, sizeof bad);
  bad[39] = 0x13;
  bad[40] = 0x01;
  if (tls13_wire_parse_supported_server_hello(bad, sizeof bad, random, key_share)) {
    fprintf(stderr, "accepted unsupported ServerHello cipher suite\n");
    return 1;
  }

  memcpy(bad, valid_server_hello, sizeof bad);
  static const uint8_t hrr_random[32] = {
      0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11,
      0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
      0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e,
      0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c};
  memcpy(&bad[6], hrr_random, sizeof hrr_random);
  if (tls13_wire_parse_supported_server_hello(bad, sizeof bad, random, key_share)) {
    fprintf(stderr, "accepted HelloRetryRequest as ServerHello\n");
    return 1;
  }

  memcpy(bad, valid_server_hello, sizeof bad);
  bad[44] = 0x00;
  bad[45] = 0x2a;
  if (tls13_wire_parse_supported_server_hello(bad, sizeof bad, random, key_share)) {
    fprintf(stderr, "accepted ServerHello missing key_share\n");
    return 1;
  }
  return 0;
}

static int test_inner_plaintext_roundtrip(void) {
  static const uint8_t plaintext[] = {'h', 'e', 'l', 'l', 'o'};
  uint8_t inner[sizeof plaintext + 1 + 3];
  uint8_t content_type = 0;
  size_t plaintext_len = 0;

  if (!tls13_wire_encode_inner_plaintext(
          inner, sizeof inner, plaintext, sizeof plaintext, 23, 3)) {
    fprintf(stderr, "encode TLSInnerPlaintext failed\n");
    return 1;
  }
  static const uint8_t expected[] = {'h', 'e', 'l', 'l', 'o', 23, 0, 0, 0};
  if (memcmp(inner, expected, sizeof inner) != 0) {
    fprintf(stderr, "encoded TLSInnerPlaintext mismatch\n");
    return 1;
  }
  if (!tls13_wire_decode_inner_plaintext(inner, sizeof inner, &content_type, &plaintext_len)) {
    fprintf(stderr, "decode TLSInnerPlaintext failed\n");
    return 1;
  }
  if (content_type != 23 || plaintext_len != sizeof plaintext ||
      memcmp(inner, plaintext, plaintext_len) != 0) {
    fprintf(stderr, "decoded TLSInnerPlaintext fields mismatch\n");
    return 1;
  }
  return 0;
}

static int test_inner_plaintext_rejects_malformed(void) {
  uint8_t out[4];
  uint8_t content_type = 0;
  size_t plaintext_len = 0;
  static const uint8_t all_padding[] = {0, 0, 0};
  static const uint8_t plaintext[] = {1, 2, 3};

  if (tls13_wire_encode_inner_plaintext(out, sizeof out - 1, plaintext, sizeof plaintext, 23, 0)) {
    fprintf(stderr, "encoded TLSInnerPlaintext with bad output length\n");
    return 1;
  }
  if (tls13_wire_encode_inner_plaintext(NULL, sizeof plaintext + 1, plaintext, sizeof plaintext, 23, 0)) {
    fprintf(stderr, "encoded TLSInnerPlaintext to null output\n");
    return 1;
  }
  if (tls13_wire_decode_inner_plaintext(all_padding, sizeof all_padding, &content_type, &plaintext_len)) {
    fprintf(stderr, "decoded all-padding TLSInnerPlaintext\n");
    return 1;
  }
  if (tls13_wire_decode_inner_plaintext(NULL, 1, &content_type, &plaintext_len) ||
      tls13_wire_decode_inner_plaintext(all_padding, 0, &content_type, &plaintext_len)) {
    fprintf(stderr, "decoded malformed TLSInnerPlaintext input\n");
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
  failed |= test_supported_server_hello_scoped();
  failed |= test_supported_server_hello_rejects_malformed();
  failed |= test_inner_plaintext_roundtrip();
  failed |= test_inner_plaintext_rejects_malformed();
  if (failed != 0) {
    return 1;
  }
  printf("wire stub tests passed\n");
  return 0;
}
