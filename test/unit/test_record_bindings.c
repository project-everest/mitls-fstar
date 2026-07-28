#include "TLS13_Record.h"
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

int main(void) {
  static const uint8_t key[32] = {
      0x9f, 0x02, 0x28, 0x3b, 0x6c, 0x9c, 0x07, 0xef,
      0xcb, 0x88, 0x36, 0x8f, 0xa3, 0x91, 0x4f, 0x11,
      0x2b, 0x2a, 0x65, 0x9a, 0x1f, 0xa7, 0x6f, 0x00,
      0xf0, 0xee, 0xa3, 0x2e, 0x7b, 0x6a, 0x7c, 0x01};
  static const uint8_t iv[12] = {
      0xcf, 0x78, 0x2b, 0x88, 0xdd, 0x83, 0x54, 0x9a,
      0xad, 0xf1, 0xe9, 0x84};
  static const uint8_t aad[5] = {23, 3, 3, 0, 21};
  static const uint8_t plain[] = "record wrapper test";
  uint8_t expected_cipher[sizeof plain - 1 + 16];
  uint8_t sealed[sizeof expected_cipher];
  uint8_t opened[sizeof plain - 1];

  if (!tls13_hacl_chacha20_poly1305_seal_combined(
          expected_cipher,
          sizeof expected_cipher,
          key,
          iv,
          aad,
          sizeof aad,
          plain,
          sizeof plain - 1)) {
    fprintf(stderr, "direct record setup failed\n");
    return 1;
  }

  TLS13_Record_record_state uninstalled = TLS13_Record_record_state_new();
  bool uninstalled_ok = TLS13_Record_seal_application(
      uninstalled, (uint8_t *)aad, sizeof aad, (uint8_t *)plain, sizeof plain - 1, sealed);
  TLS13_Record_record_state_free(uninstalled);
  if (uninstalled_ok) {
    fprintf(stderr, "uninstalled record state sealed data\n");
    return 1;
  }

  TLS13_Record_record_state seal_state = TLS13_Record_record_state_new();
  TLS13_Record_install_keys(seal_state, 2, (uint8_t *)key, (uint8_t *)iv);
  bool seal_ok = TLS13_Record_seal_application(
      seal_state, (uint8_t *)aad, sizeof aad, (uint8_t *)plain, sizeof plain - 1, sealed);
  TLS13_Record_record_state_free(seal_state);
  if (!seal_ok || expect_bytes("extracted record seal", sealed, expected_cipher, sizeof sealed) != 0) {
    return 1;
  }

  TLS13_Record_record_state open_state = TLS13_Record_record_state_new();
  TLS13_Record_install_keys(open_state, 2, (uint8_t *)key, (uint8_t *)iv);
  bool open_ok = TLS13_Record_open_application(
      open_state, (uint8_t *)aad, sizeof aad, sealed, sizeof sealed, opened);
  TLS13_Record_record_state_free(open_state);
  if (!open_ok || expect_bytes("extracted record open", opened, plain, sizeof opened) != 0) {
    return 1;
  }

  sealed[0] ^= 1;
  TLS13_Record_record_state tamper_state = TLS13_Record_record_state_new();
  TLS13_Record_install_keys(tamper_state, 2, (uint8_t *)key, (uint8_t *)iv);
  bool tamper_ok = TLS13_Record_open_application(
      tamper_state, (uint8_t *)aad, sizeof aad, sealed, sizeof sealed, opened);
  TLS13_Record_record_state_free(tamper_state);
  if (tamper_ok) {
    fprintf(stderr, "tampered extracted record opened successfully\n");
    return 1;
  }

  printf("record binding test passed\n");
  return 0;
}
