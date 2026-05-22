#include "TLS13_Record.h"
#include "tls13_crypto_external.h"
#include "tls13_hacl_stubs.h"

#include <stdbool.h>
#include <stdio.h>
#include <string.h>

void TLS13_Crypto_sha256_empty(uint8_t *out, void *old_out) {
  (void)old_out;
  (void)tls13_hacl_sha256(out, NULL, 0);
}

void TLS13_Crypto_hmac_sha256(
    uint8_t *key,
    size_t key_len,
    uint8_t *msg,
    size_t msg_len,
    uint8_t *out,
    void *key_bytes,
    void *msg_bytes,
    void *old_out) {
  (void)key_bytes;
  (void)msg_bytes;
  (void)old_out;
  (void)tls13_hacl_hmac_sha256(out, key, key_len, msg, msg_len);
}

void TLS13_Crypto_hkdf_extract(
    uint8_t *salt,
    size_t salt_len,
    uint8_t *ikm,
    size_t ikm_len,
    uint8_t *out,
    void *salt_bytes,
    void *ikm_bytes,
    void *old_out) {
  (void)salt_bytes;
  (void)ikm_bytes;
  (void)old_out;
  (void)tls13_hacl_hkdf_extract_sha256(out, salt, salt_len, ikm, ikm_len);
}

void TLS13_Crypto_hkdf_expand_label(
    uint8_t *secret,
    uint8_t *label,
    size_t label_len,
    uint8_t *context,
    size_t context_len,
    uint8_t *out,
    size_t out_len,
    void *secret_bytes,
    void *label_bytes,
    void *context_bytes,
    void *old_out) {
  (void)secret_bytes;
  (void)label_bytes;
  (void)context_bytes;
  (void)old_out;
  (void)tls13_hacl_hkdf_expand_label_sha256(
      out, out_len, secret, label, label_len, context, context_len);
}

void TLS13_Crypto_hkdf_expand_label_empty_context(
    uint8_t *secret,
    uint8_t *label,
    size_t label_len,
    uint8_t *out,
    size_t out_len,
    void *secret_bytes,
    void *label_bytes,
    void *old_out) {
  (void)secret_bytes;
  (void)label_bytes;
  (void)old_out;
  (void)tls13_hacl_hkdf_expand_label_sha256(
      out, out_len, secret, label, label_len, NULL, 0);
}

bool TLS13_Crypto_tls13_record_nonce(
    uint8_t *static_iv,
    uint64_t sequence_number,
    uint8_t *out,
    void *iv_bytes,
    void *old_out) {
  (void)iv_bytes;
  (void)old_out;
  return tls13_record_nonce(out, static_iv, sequence_number);
}

void TLS13_Crypto_chacha20_poly1305_seal(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out,
    void *key_bytes,
    void *nonce_bytes,
    void *aad_bytes,
    void *plain_bytes,
    void *old_out) {
  (void)key_bytes;
  (void)nonce_bytes;
  (void)aad_bytes;
  (void)plain_bytes;
  (void)old_out;
  (void)tls13_hacl_chacha20_poly1305_seal_combined(
      out, plain_len + 16, key, nonce, aad, aad_len, plain, plain_len);
}

bool TLS13_Crypto_chacha20_poly1305_open(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out,
    void *key_bytes,
    void *nonce_bytes,
    void *aad_bytes,
    void *cipher_bytes,
    void *old_out) {
  (void)key_bytes;
  (void)nonce_bytes;
  (void)aad_bytes;
  (void)cipher_bytes;
  (void)old_out;
  if (cipher_len < 16) {
    return false;
  }
  return tls13_hacl_chacha20_poly1305_open_combined(
      out, cipher_len - 16, key, nonce, aad, aad_len, cipher, cipher_len);
}

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
  uint8_t expected_nonce[12];
  uint8_t expected_cipher[sizeof plain - 1 + 16];
  uint8_t sealed[sizeof expected_cipher];
  uint8_t opened[sizeof plain - 1];

  if (!tls13_record_nonce(expected_nonce, iv, 0) ||
      !tls13_hacl_chacha20_poly1305_seal_combined(
          expected_cipher,
          sizeof expected_cipher,
          key,
          expected_nonce,
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
