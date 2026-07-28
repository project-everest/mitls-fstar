#include "TLS13_KeySchedule.h"
#include "tls13_crypto_external.h"
#include "tls13_hacl_stubs.h"

#include <stdbool.h>
#include <stdio.h>
#include <string.h>

static int expect_bytes(
    const char *label,
    const uint8_t *got,
    const uint8_t *expected,
    size_t len) {
  if (memcmp(got, expected, len) != 0) {
    fprintf(stderr, "%s mismatch\n", label);
    return 1;
  }
  return 0;
}

static int test_rfc8448_handshake_secret(void) {
  static const uint8_t shared_secret[32] = {
      0x8b, 0xd4, 0x05, 0x4f, 0xb5, 0x5b, 0x9d, 0x63,
      0xfd, 0xfb, 0xac, 0xf9, 0xf0, 0x4b, 0x9f, 0x0d,
      0x35, 0xe6, 0xd6, 0x3f, 0x53, 0x75, 0x63, 0xef,
      0xd4, 0x62, 0x72, 0x90, 0x0f, 0x89, 0x49, 0x2d};
  static const uint8_t expected_handshake_secret[32] = {
      0x1d, 0xc8, 0x26, 0xe9, 0x36, 0x06, 0xaa, 0x6f,
      0xdc, 0x0a, 0xad, 0xc1, 0x2f, 0x74, 0x1b, 0x01,
      0x04, 0x6a, 0xa6, 0xb9, 0x9f, 0x69, 0x1e, 0xd2,
      0x21, 0xa9, 0xf0, 0xca, 0x04, 0x3f, 0xbe, 0xac};
  uint8_t early_secret[32];
  uint8_t zero_psk[32] = {0};
  uint8_t got[32];

  if (!tls13_hacl_hkdf_extract_sha256(
          early_secret, NULL, 0, zero_psk, sizeof zero_psk)) {
    fprintf(stderr, "early-secret setup failed\n");
    return 1;
  }
  TLS13_KeySchedule_handshake_secret(
      early_secret, (uint8_t *)shared_secret, sizeof shared_secret, got);
  return expect_bytes(
      "extracted handshake_secret", got, expected_handshake_secret, sizeof got);
}

static int test_rfc8448_client_handshake_traffic(void) {
  static const uint8_t handshake_secret[32] = {
      0x1d, 0xc8, 0x26, 0xe9, 0x36, 0x06, 0xaa, 0x6f,
      0xdc, 0x0a, 0xad, 0xc1, 0x2f, 0x74, 0x1b, 0x01,
      0x04, 0x6a, 0xa6, 0xb9, 0x9f, 0x69, 0x1e, 0xd2,
      0x21, 0xa9, 0xf0, 0xca, 0x04, 0x3f, 0xbe, 0xac};
  static const uint8_t transcript_hash[32] = {
      0x86, 0x0c, 0x06, 0xed, 0xc0, 0x78, 0x58, 0xee,
      0x8e, 0x78, 0xf0, 0xe7, 0x42, 0x8c, 0x58, 0xed,
      0xd6, 0xb4, 0x3f, 0x2c, 0xa3, 0xe6, 0xe9, 0x5f,
      0x02, 0xed, 0x06, 0x3c, 0xf0, 0xe1, 0xca, 0xd8};
  static const uint8_t expected_client_hs_traffic[32] = {
      0xb3, 0xed, 0xdb, 0x12, 0x6e, 0x06, 0x7f, 0x35,
      0xa7, 0x80, 0xb3, 0xab, 0xf4, 0x5e, 0x2d, 0x8f,
      0x3b, 0x1a, 0x95, 0x07, 0x38, 0xf5, 0x2e, 0x96,
      0x00, 0x74, 0x6a, 0x0e, 0x27, 0xa5, 0x5a, 0x21};
  uint8_t got[32];

  TLS13_KeySchedule_client_handshake_traffic_secret(
      (uint8_t *)handshake_secret, (uint8_t *)transcript_hash, got);
  return expect_bytes(
      "extracted client_handshake_traffic_secret",
      got,
      expected_client_hs_traffic,
      sizeof got);
}

static int test_traffic_key_iv_against_hacl(void) {
  static const uint8_t traffic_secret[32] = {
      0xb3, 0xed, 0xdb, 0x12, 0x6e, 0x06, 0x7f, 0x35,
      0xa7, 0x80, 0xb3, 0xab, 0xf4, 0x5e, 0x2d, 0x8f,
      0x3b, 0x1a, 0x95, 0x07, 0x38, 0xf5, 0x2e, 0x96,
      0x00, 0x74, 0x6a, 0x0e, 0x27, 0xa5, 0x5a, 0x21};
  static const uint8_t key_info[] = {
      0x00, 0x20, 0x09,
      't', 'l', 's', '1', '3', ' ', 'k', 'e', 'y',
      0x00};
  static const uint8_t iv_info[] = {
      0x00, 0x0c, 0x08,
      't', 'l', 's', '1', '3', ' ', 'i', 'v',
      0x00};
  uint8_t expected_key[32];
  uint8_t expected_iv[12];
  uint8_t got_key[32];
  uint8_t got_iv[12];

  if (!tls13_hacl_hkdf_expand_sha256(
          expected_key, sizeof expected_key, traffic_secret, key_info, sizeof key_info) ||
      !tls13_hacl_hkdf_expand_sha256(
          expected_iv, sizeof expected_iv, traffic_secret, iv_info, sizeof iv_info)) {
    fprintf(stderr, "direct traffic key/iv setup failed\n");
    return 1;
  }

  TLS13_KeySchedule_derive_traffic_key((uint8_t *)traffic_secret, got_key);
  TLS13_KeySchedule_derive_traffic_iv((uint8_t *)traffic_secret, got_iv);
  return expect_bytes("extracted traffic key", got_key, expected_key, sizeof got_key) ||
         expect_bytes("extracted traffic iv", got_iv, expected_iv, sizeof got_iv);
}

int main(void) {
  int failed = 0;
  failed |= test_rfc8448_handshake_secret();
  failed |= test_rfc8448_client_handshake_traffic();
  failed |= test_traffic_key_iv_against_hacl();
  if (failed != 0) {
    return 1;
  }
  printf("key schedule binding test passed\n");
  return 0;
}
