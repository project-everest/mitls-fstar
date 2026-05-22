#include "tls13_hacl_stubs.h"

#include <stdio.h>
#include <string.h>

static int expect_bytes(const char *name, const uint8_t *got, const uint8_t *want, size_t len) {
  if (memcmp(got, want, len) == 0) {
    return 0;
  }
  fprintf(stderr, "%s mismatch\n", name);
  return 1;
}

static int test_sha256_empty(void) {
  static const uint8_t expected[32] = {
      0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
      0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
      0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
      0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55};
  uint8_t out[32];
  if (!tls13_hacl_sha256(out, NULL, 0)) {
    fprintf(stderr, "sha256 rejected empty input\n");
    return 1;
  }
  return expect_bytes("sha256(empty)", out, expected, sizeof out);
}

static int test_hmac_sha256_rfc4231_case1(void) {
  static const uint8_t expected[32] = {
      0xb0, 0x34, 0x4c, 0x61, 0xd8, 0xdb, 0x38, 0x53,
      0x5c, 0xa8, 0xaf, 0xce, 0xaf, 0x0b, 0xf1, 0x2b,
      0x88, 0x1d, 0xc2, 0x00, 0xc9, 0x83, 0x3d, 0xa7,
      0x26, 0xe9, 0x37, 0x6c, 0x2e, 0x32, 0xcf, 0xf7};
  uint8_t key[20];
  memset(key, 0x0b, sizeof key);
  static const uint8_t msg[] = "Hi There";
  uint8_t out[32];
  if (!tls13_hacl_hmac_sha256(out, key, sizeof key, msg, strlen((const char *)msg))) {
    fprintf(stderr, "hmac-sha256 rejected RFC 4231 case 1\n");
    return 1;
  }
  return expect_bytes("hmac-sha256 RFC4231 case 1", out, expected, sizeof out);
}

static int test_hkdf_sha256_rfc5869_case1(void) {
  static const uint8_t ikm[22] = {
      0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
      0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
      0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b};
  static const uint8_t salt[13] = {
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
      0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c};
  static const uint8_t info[10] = {
      0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9};
  static const uint8_t expected_prk[32] = {
      0x07, 0x77, 0x09, 0x36, 0x2c, 0x2e, 0x32, 0xdf,
      0x0d, 0xdc, 0x3f, 0x0d, 0xc4, 0x7b, 0xba, 0x63,
      0x90, 0xb6, 0xc7, 0x3b, 0xb5, 0x0f, 0x9c, 0x31,
      0x22, 0xec, 0x84, 0x4a, 0xd7, 0xc2, 0xb3, 0xe5};
  static const uint8_t expected_okm[42] = {
      0x3c, 0xb2, 0x5f, 0x25, 0xfa, 0xac, 0xd5, 0x7a,
      0x90, 0x43, 0x4f, 0x64, 0xd0, 0x36, 0x2f, 0x2a,
      0x2d, 0x2d, 0x0a, 0x90, 0xcf, 0x1a, 0x5a, 0x4c,
      0x5d, 0xb0, 0x2d, 0x56, 0xec, 0xc4, 0xc5, 0xbf,
      0x34, 0x00, 0x72, 0x08, 0xd5, 0xb8, 0x87, 0x18,
      0x58, 0x65};
  uint8_t prk[32];
  uint8_t okm[42];
  if (!tls13_hacl_hkdf_extract_sha256(prk, salt, sizeof salt, ikm, sizeof ikm)) {
    fprintf(stderr, "hkdf-extract rejected RFC 5869 case 1\n");
    return 1;
  }
  if (expect_bytes("hkdf-extract RFC5869 case 1", prk, expected_prk, sizeof prk) != 0) {
    return 1;
  }
  if (!tls13_hacl_hkdf_expand_sha256(okm, sizeof okm, prk, info, sizeof info)) {
    fprintf(stderr, "hkdf-expand rejected RFC 5869 case 1\n");
    return 1;
  }
  return expect_bytes("hkdf-expand RFC5869 case 1", okm, expected_okm, sizeof okm);
}

static int test_tls13_hkdf_expand_label_encoding(void) {
  uint8_t prk[32];
  uint8_t via_label[48];
  uint8_t via_info[48];
  static const uint8_t label[] = {'c', ' ', 'h', 's', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t context[32] = {
      0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
      0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
      0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
      0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55};
  uint8_t info[2 + 1 + 6 + sizeof label + 1 + sizeof context];
  size_t p = 0;

  for (size_t i = 0; i < sizeof prk; ++i) prk[i] = (uint8_t)(0xa0 + i);

  info[p++] = 0x00;
  info[p++] = sizeof via_label;
  info[p++] = 6 + sizeof label;
  memcpy(&info[p], "tls13 ", 6);
  p += 6;
  memcpy(&info[p], label, sizeof label);
  p += sizeof label;
  info[p++] = sizeof context;
  memcpy(&info[p], context, sizeof context);
  p += sizeof context;

  if (!tls13_hacl_hkdf_expand_label_sha256(
          via_label, sizeof via_label, prk, label, sizeof label, context, sizeof context)) {
    fprintf(stderr, "HKDF-Expand-Label wrapper failed\n");
    return 1;
  }
  if (!tls13_hacl_hkdf_expand_sha256(via_info, sizeof via_info, prk, info, p)) {
    fprintf(stderr, "direct HKDF-Expand for label test failed\n");
    return 1;
  }
  return expect_bytes("TLS 1.3 HKDF label encoding", via_label, via_info, sizeof via_label);
}

static int test_tls13_hkdf_rfc8448_simple_handshake(void) {
  static const uint8_t derived_secret[32] = {
      0x6f, 0x26, 0x15, 0xa1, 0x08, 0xc7, 0x02, 0xc5,
      0x67, 0x8f, 0x54, 0xfc, 0x9d, 0xba, 0xb6, 0x97,
      0x16, 0xc0, 0x76, 0x18, 0x9c, 0x48, 0x25, 0x0c,
      0xeb, 0xea, 0xc3, 0x57, 0x6c, 0x36, 0x11, 0xba};
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
  static const uint8_t transcript_hash[32] = {
      0x86, 0x0c, 0x06, 0xed, 0xc0, 0x78, 0x58, 0xee,
      0x8e, 0x78, 0xf0, 0xe7, 0x42, 0x8c, 0x58, 0xed,
      0xd6, 0xb4, 0x3f, 0x2c, 0xa3, 0xe6, 0xe9, 0x5f,
      0x02, 0xed, 0x06, 0x3c, 0xf0, 0xe1, 0xca, 0xd8};
  static const uint8_t c_hs_label[] = {
      'c', ' ', 'h', 's', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t expected_client_hs_traffic[32] = {
      0xb3, 0xed, 0xdb, 0x12, 0x6e, 0x06, 0x7f, 0x35,
      0xa7, 0x80, 0xb3, 0xab, 0xf4, 0x5e, 0x2d, 0x8f,
      0x3b, 0x1a, 0x95, 0x07, 0x38, 0xf5, 0x2e, 0x96,
      0x00, 0x74, 0x6a, 0x0e, 0x27, 0xa5, 0x5a, 0x21};
  uint8_t handshake_secret[32];
  uint8_t client_hs_traffic[32];

  if (!tls13_hacl_hkdf_extract_sha256(
          handshake_secret, derived_secret, sizeof derived_secret, shared_secret, sizeof shared_secret)) {
    fprintf(stderr, "RFC 8448 handshake HKDF-Extract failed\n");
    return 1;
  }
  if (expect_bytes(
          "RFC8448 handshake secret",
          handshake_secret,
          expected_handshake_secret,
          sizeof handshake_secret) != 0) {
    return 1;
  }
  if (!tls13_hacl_hkdf_expand_label_sha256(
          client_hs_traffic,
          sizeof client_hs_traffic,
          handshake_secret,
          c_hs_label,
          sizeof c_hs_label,
          transcript_hash,
          sizeof transcript_hash)) {
    fprintf(stderr, "RFC 8448 client handshake traffic secret derivation failed\n");
    return 1;
  }
  return expect_bytes(
      "RFC8448 client handshake traffic secret",
      client_hs_traffic,
      expected_client_hs_traffic,
      sizeof client_hs_traffic);
}

static int test_x25519_rfc7748(void) {
  static const uint8_t alice_sk[32] = {
      0x77, 0x07, 0x6d, 0x0a, 0x73, 0x18, 0xa5, 0x7d,
      0x3c, 0x16, 0xc1, 0x72, 0x51, 0xb2, 0x66, 0x45,
      0xdf, 0x4c, 0x2f, 0x87, 0xeb, 0xc0, 0x99, 0x2a,
      0xb1, 0x77, 0xfb, 0xa5, 0x1d, 0xb9, 0x2c, 0x2a};
  static const uint8_t alice_pk_expected[32] = {
      0x85, 0x20, 0xf0, 0x09, 0x89, 0x30, 0xa7, 0x54,
      0x74, 0x8b, 0x7d, 0xdc, 0xb4, 0x3e, 0xf7, 0x5a,
      0x0d, 0xbf, 0x3a, 0x0d, 0x26, 0x38, 0x1a, 0xf4,
      0xeb, 0xa4, 0xa9, 0x8e, 0xaa, 0x9b, 0x4e, 0x6a};
  static const uint8_t bob_sk[32] = {
      0x5d, 0xab, 0x08, 0x7e, 0x62, 0x4a, 0x8a, 0x4b,
      0x79, 0xe1, 0x7f, 0x8b, 0x83, 0x80, 0x0e, 0xe6,
      0x6f, 0x3b, 0xb1, 0x29, 0x26, 0x18, 0xb6, 0xfd,
      0x1c, 0x2f, 0x8b, 0x27, 0xff, 0x88, 0xe0, 0xeb};
  static const uint8_t bob_pk_expected[32] = {
      0xde, 0x9e, 0xdb, 0x7d, 0x7b, 0x7d, 0xc1, 0xb4,
      0xd3, 0x5b, 0x61, 0xc2, 0xec, 0xe4, 0x35, 0x37,
      0x3f, 0x83, 0x43, 0xc8, 0x5b, 0x78, 0x67, 0x4d,
      0xad, 0xfc, 0x7e, 0x14, 0x6f, 0x88, 0x2b, 0x4f};
  static const uint8_t shared_expected[32] = {
      0x4a, 0x5d, 0x9d, 0x5b, 0xa4, 0xce, 0x2d, 0xe1,
      0x72, 0x8e, 0x3b, 0xf4, 0x80, 0x35, 0x0f, 0x25,
      0xe0, 0x7e, 0x21, 0xc9, 0x47, 0xd1, 0x9e, 0x33,
      0x76, 0xf0, 0x9b, 0x3c, 0x1e, 0x16, 0x17, 0x42};
  uint8_t alice_pk[32];
  uint8_t bob_pk[32];
  uint8_t shared1[32];
  uint8_t shared2[32];

  if (!tls13_hacl_x25519_public_from_private(alice_pk, alice_sk) ||
      !tls13_hacl_x25519_public_from_private(bob_pk, bob_sk)) {
    fprintf(stderr, "x25519 public key derivation failed\n");
    return 1;
  }
  if (expect_bytes("x25519 Alice public", alice_pk, alice_pk_expected, sizeof alice_pk) != 0 ||
      expect_bytes("x25519 Bob public", bob_pk, bob_pk_expected, sizeof bob_pk) != 0) {
    return 1;
  }
  if (!tls13_hacl_x25519_shared(shared1, alice_sk, bob_pk) ||
      !tls13_hacl_x25519_shared(shared2, bob_sk, alice_pk)) {
    fprintf(stderr, "x25519 shared secret failed\n");
    return 1;
  }
  if (expect_bytes("x25519 shared Alice", shared1, shared_expected, sizeof shared1) != 0 ||
      expect_bytes("x25519 shared Bob", shared2, shared_expected, sizeof shared2) != 0) {
    return 1;
  }
  return 0;
}

static int test_chacha20_poly1305_roundtrip(void) {
  uint8_t key[32];
  uint8_t nonce[12];
  uint8_t aad[13];
  uint8_t plaintext[129];
  uint8_t ciphertext[sizeof plaintext];
  uint8_t decrypted[sizeof plaintext];
  uint8_t tag[16];

  for (size_t i = 0; i < sizeof key; ++i) key[i] = (uint8_t)i;
  for (size_t i = 0; i < sizeof nonce; ++i) nonce[i] = (uint8_t)(0xa0 + i);
  for (size_t i = 0; i < sizeof aad; ++i) aad[i] = (uint8_t)(0x50 + i);
  for (size_t i = 0; i < sizeof plaintext; ++i) plaintext[i] = (uint8_t)(i * 3u + 1u);
  memset(decrypted, 0, sizeof decrypted);

  if (!tls13_hacl_chacha20_poly1305_seal(
          ciphertext, tag, key, nonce, aad, sizeof aad, plaintext, sizeof plaintext)) {
    fprintf(stderr, "chacha20-poly1305 seal failed\n");
    return 1;
  }
  if (!tls13_hacl_chacha20_poly1305_open(
          decrypted, key, nonce, aad, sizeof aad, ciphertext, sizeof ciphertext, tag)) {
    fprintf(stderr, "chacha20-poly1305 open failed\n");
    return 1;
  }
  if (expect_bytes("chacha20-poly1305 roundtrip", decrypted, plaintext, sizeof plaintext) != 0) {
    return 1;
  }
  tag[0] ^= 1u;
  if (tls13_hacl_chacha20_poly1305_open(
          decrypted, key, nonce, aad, sizeof aad, ciphertext, sizeof ciphertext, tag)) {
    fprintf(stderr, "chacha20-poly1305 accepted a tampered tag\n");
    return 1;
  }

  uint8_t combined[sizeof plaintext + 16];
  memset(decrypted, 0, sizeof decrypted);
  if (!tls13_hacl_chacha20_poly1305_seal_combined(
          combined, sizeof combined, key, nonce, aad, sizeof aad, plaintext, sizeof plaintext)) {
    fprintf(stderr, "combined chacha20-poly1305 seal failed\n");
    return 1;
  }
  if (!tls13_hacl_chacha20_poly1305_open_combined(
          decrypted, sizeof decrypted, key, nonce, aad, sizeof aad, combined, sizeof combined)) {
    fprintf(stderr, "combined chacha20-poly1305 open failed\n");
    return 1;
  }
  if (expect_bytes("combined chacha20-poly1305 roundtrip", decrypted, plaintext, sizeof plaintext) != 0) {
    return 1;
  }
  combined[sizeof combined - 1] ^= 1u;
  if (tls13_hacl_chacha20_poly1305_open_combined(
          decrypted, sizeof decrypted, key, nonce, aad, sizeof aad, combined, sizeof combined)) {
    fprintf(stderr, "combined chacha20-poly1305 accepted a tampered tag\n");
    return 1;
  }
  if (tls13_hacl_chacha20_poly1305_seal_combined(
          combined, sizeof combined - 1, key, nonce, aad, sizeof aad, plaintext, sizeof plaintext) ||
      tls13_hacl_chacha20_poly1305_open_combined(
          decrypted, sizeof decrypted, key, nonce, aad, sizeof aad, combined, sizeof combined - 1)) {
    fprintf(stderr, "combined chacha20-poly1305 accepted a bad length\n");
    return 1;
  }
  return 0;
}

static int test_tls13_record_nonce(void) {
  static const uint8_t static_iv[12] = {
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05,
      0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b};
  static const uint8_t expected_zero[12] = {
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05,
      0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b};
  static const uint8_t expected_seq[12] = {
      0x00, 0x01, 0x02, 0x03, 0x05, 0x07,
      0x05, 0x03, 0x0d, 0x0f, 0x0d, 0x03};
  uint8_t out[12];

  if (!tls13_record_nonce(out, static_iv, 0)) {
    fprintf(stderr, "TLS record nonce rejected sequence zero\n");
    return 1;
  }
  if (expect_bytes("TLS record nonce seq 0", out, expected_zero, sizeof out) != 0) {
    return 1;
  }
  if (!tls13_record_nonce(out, static_iv, UINT64_C(0x0102030405060708))) {
    fprintf(stderr, "TLS record nonce rejected non-zero sequence\n");
    return 1;
  }
  if (expect_bytes("TLS record nonce seq non-zero", out, expected_seq, sizeof out) != 0) {
    return 1;
  }
  if (tls13_record_nonce(NULL, static_iv, 0) || tls13_record_nonce(out, NULL, 0)) {
    fprintf(stderr, "TLS record nonce accepted a null buffer\n");
    return 1;
  }
  return 0;
}

int main(void) {
  int failed = 0;
  failed |= test_sha256_empty();
  failed |= test_hmac_sha256_rfc4231_case1();
  failed |= test_hkdf_sha256_rfc5869_case1();
  failed |= test_tls13_hkdf_expand_label_encoding();
  failed |= test_tls13_hkdf_rfc8448_simple_handshake();
  failed |= test_x25519_rfc7748();
  failed |= test_tls13_record_nonce();
  failed |= test_chacha20_poly1305_roundtrip();
  if (failed != 0) {
    return 1;
  }
  printf("HACL* stub tests passed\n");
  return 0;
}
