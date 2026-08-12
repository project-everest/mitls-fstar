#include "tls13_crypto_external.h"

#include <stdio.h>
#include <stdlib.h>

#include "tls13_hacl_stubs.h"

/* ATLAS's default ClientHello offers TLS_AES_128_GCM_SHA256 alongside
   TLS_CHACHA20_POLY1305_SHA256 (see [default_connection_config] in
   TLS13.Impl.ConnectionState.Repr.fsti).  HACL* ships AES-GCM only as Vale
   assembly, so a build without the accelerated modules cannot honour an offer
   it makes.  Fail at compile time rather than emit a client that negotiates a
   suite it cannot implement. */
#ifndef TLS13_HACL_HAS_AESGCM
#define TLS13_HACL_HAS_AESGCM 0
#endif
#if !TLS13_HACL_HAS_AESGCM
#error "ATLAS offers TLS_AES_128_GCM_SHA256; build with HACL_ACCEL=1 (x86_64 Linux)"
#endif

/* The seal bindings are assumed *total* functions in F*: their postconditions
   pin the output buffer to [C.aead_seal ...] unconditionally.
   The only way the backend can fail is if the running CPU lacks AES-NI /
   PCLMULQDQ, in which case EverCrypt refuses to create the AEAD state.  Silently
   returning leaves the caller reading uninitialised memory, so abort instead:
   an assumption that cannot be met must be loud. */
static void tls13_aead_backend_failed(const char *what) {
  fprintf(stderr, "ATLAS: %s failed; the CPU does not provide the required "
                  "AEAD backend\n", what);
  abort();
}

void TLS13_Crypto_sha256_empty(uint8_t *out) {
  (void)tls13_hacl_sha256(out, NULL, 0);
}

bool TLS13_Crypto_random_bytes(uint8_t *out, size_t out_len) {
  return tls13_hacl_random_bytes(out, out_len);
}

void TLS13_Crypto_sha256(
    uint8_t *input,
    size_t input_len,
    uint8_t *out) {
  (void)tls13_hacl_sha256(out, input, input_len);
}

void TLS13_Crypto_sha256_prefix(uint8_t *input, size_t input_len, uint8_t *out) {
  TLS13_Crypto_sha256(input, input_len, out);
}

void TLS13_Crypto_hmac_sha256(
    uint8_t *key,
    size_t key_len,
    uint8_t *msg,
    size_t msg_len,
    uint8_t *out) {
  (void)tls13_hacl_hmac_sha256(out, key, key_len, msg, msg_len);
}

bool TLS13_Crypto_equal32(uint8_t *a, uint8_t *b) {
  volatile uint8_t diff = 0;
  for (size_t i = 0; i < 32u; ++i) {
    diff = (uint8_t)(diff | (uint8_t)(a[i] ^ b[i]));
  }
  return diff == 0u;
}

bool TLS13_Crypto_equal12(uint8_t *a, uint8_t *b) {
  volatile uint8_t diff = 0;
  for (size_t i = 0; i < 12u; ++i) {
    diff = (uint8_t)(diff | (uint8_t)(a[i] ^ b[i]));
  }
  return diff == 0u;
}

void TLS13_Crypto_hkdf_extract(
    uint8_t *salt,
    size_t salt_len,
    uint8_t *ikm,
    size_t ikm_len,
    uint8_t *out) {
  (void)tls13_hacl_hkdf_extract_sha256(out, salt, salt_len, ikm, ikm_len);
}

void TLS13_Crypto_hkdf_expand(
    uint8_t *secret,
    uint8_t *info,
    size_t info_len,
    uint8_t *out,
    size_t out_len) {
  (void)tls13_hacl_hkdf_expand_sha256(out, out_len, secret, info, info_len);
}

bool TLS13_Crypto_x25519_shared_runtime(
    uint8_t *sk,
    uint8_t *pk,
    uint8_t *out) {
  return tls13_hacl_x25519_shared(out, sk, pk);
}

void TLS13_Crypto_x25519_public_from_private(
    uint8_t *sk,
    uint8_t *out) {
  (void)tls13_hacl_x25519_public_from_private(out, sk);
}

bool TLS13_Crypto_p256_shared_runtime(
    uint8_t *sk,
    uint8_t *pk,
    uint8_t *out) {
  return tls13_hacl_p256_shared(out, sk, pk);
}

void TLS13_Crypto_p256_public_from_private(
    uint8_t *sk,
    uint8_t *out) {
  (void)tls13_hacl_p256_public_from_private(out, sk);
}

void TLS13_Crypto_chacha20_poly1305_seal(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out) {
  if (!tls13_hacl_chacha20_poly1305_seal_combined(
          out, plain_len + 16, key, nonce, aad, aad_len, plain, plain_len)) {
    tls13_aead_backend_failed("ChaCha20-Poly1305 seal");
  }
}

bool TLS13_Crypto_chacha20_poly1305_open(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out) {
  return tls13_hacl_chacha20_poly1305_open_combined(
      out, cipher_len - 16, key, nonce, aad, aad_len, cipher, cipher_len);
}

void TLS13_Crypto_aes128_gcm_seal(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *plain,
    size_t plain_len,
    uint8_t *out) {
  if (!tls13_hacl_aes128_gcm_seal_combined(
          out, plain_len + 16, key, nonce, aad, aad_len, plain, plain_len)) {
    tls13_aead_backend_failed("AES-128-GCM seal");
  }
}

bool TLS13_Crypto_aes128_gcm_open(
    uint8_t *key,
    uint8_t *nonce,
    uint8_t *aad,
    size_t aad_len,
    uint8_t *cipher,
    size_t cipher_len,
    uint8_t *out) {
  return tls13_hacl_aes128_gcm_open_combined(
      out, cipher_len - 16, key, nonce, aad, aad_len, cipher, cipher_len);
}
