#include "tls13_hacl_stubs.h"
#include "tls13_wire_stubs.h"

#include <stdio.h>
#include <string.h>

static int test_application_record_roundtrip(void) {
  uint8_t key[32];
  uint8_t static_iv[12];
  uint8_t nonce[12];
  uint8_t plaintext[257];
  uint8_t inner[sizeof plaintext + 1 + 5];
  uint8_t aad[TLS13_WIRE_RECORD_HEADER_LEN];
  uint8_t ciphertext[sizeof inner + 16];
  uint8_t opened[sizeof inner];
  uint8_t content_type = 0;
  size_t opened_plaintext_len = 0;

  for (size_t i = 0; i < sizeof key; ++i) key[i] = (uint8_t)(0x40 + i);
  for (size_t i = 0; i < sizeof static_iv; ++i) static_iv[i] = (uint8_t)(0xa0 + i);
  for (size_t i = 0; i < sizeof plaintext; ++i) plaintext[i] = (uint8_t)(i * 7u + 3u);

  if (!tls13_record_nonce(nonce, static_iv, 7)) {
    fprintf(stderr, "record nonce construction failed\n");
    return 1;
  }
  if (!tls13_wire_encode_inner_plaintext(
          inner, sizeof inner, plaintext, sizeof plaintext, 23, 5)) {
    fprintf(stderr, "TLSInnerPlaintext encoding failed\n");
    return 1;
  }
  if (!tls13_wire_serialize_record_header(
          aad, 23, 0x0303, (uint16_t)sizeof ciphertext)) {
    fprintf(stderr, "record AAD header construction failed\n");
    return 1;
  }
  if (!tls13_hacl_chacha20_poly1305_seal_combined(
          ciphertext, sizeof ciphertext, key, nonce, aad, sizeof aad, inner, sizeof inner)) {
    fprintf(stderr, "record AEAD seal failed\n");
    return 1;
  }
  if (!tls13_hacl_chacha20_poly1305_open_combined(
          opened, sizeof opened, key, nonce, aad, sizeof aad, ciphertext, sizeof ciphertext)) {
    fprintf(stderr, "record AEAD open failed\n");
    return 1;
  }
  if (!tls13_wire_decode_inner_plaintext(
          opened, sizeof opened, &content_type, &opened_plaintext_len)) {
    fprintf(stderr, "TLSInnerPlaintext decoding failed\n");
    return 1;
  }
  if (content_type != 23 || opened_plaintext_len != sizeof plaintext ||
      memcmp(opened, plaintext, sizeof plaintext) != 0) {
    fprintf(stderr, "application record roundtrip mismatch\n");
    return 1;
  }

  ciphertext[0] ^= 1u;
  if (tls13_hacl_chacha20_poly1305_open_combined(
          opened, sizeof opened, key, nonce, aad, sizeof aad, ciphertext, sizeof ciphertext)) {
    fprintf(stderr, "record AEAD accepted tampered ciphertext\n");
    return 1;
  }
  ciphertext[0] ^= 1u;
  aad[4] ^= 1u;
  if (tls13_hacl_chacha20_poly1305_open_combined(
          opened, sizeof opened, key, nonce, aad, sizeof aad, ciphertext, sizeof ciphertext)) {
    fprintf(stderr, "record AEAD accepted tampered AAD\n");
    return 1;
  }
  return 0;
}

int main(void) {
  if (test_application_record_roundtrip() != 0) {
    return 1;
  }
  printf("record stub tests passed\n");
  return 0;
}
