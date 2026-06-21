#include "tls13_openssl_stubs.h"

#include <openssl/bio.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint8_t *read_file(const char *path, size_t *len_out) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return NULL;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fclose(f);
    return NULL;
  }
  long len = ftell(f);
  if (len < 0) {
    fclose(f);
    return NULL;
  }
  rewind(f);
  uint8_t *buf = malloc((size_t)len);
  if (buf == NULL) {
    fclose(f);
    return NULL;
  }
  if (fread(buf, 1, (size_t)len, f) != (size_t)len) {
    free(buf);
    fclose(f);
    return NULL;
  }
  fclose(f);
  *len_out = (size_t)len;
  return buf;
}

static EVP_PKEY *read_private_key_pem(const char *path) {
  BIO *bio = BIO_new_file(path, "rb");
  if (bio == NULL) {
    return NULL;
  }
  EVP_PKEY *key = PEM_read_bio_PrivateKey(bio, NULL, NULL, NULL);
  BIO_free(bio);
  return key;
}

static bool sign_rsa_pss_sha256(
    EVP_PKEY *key,
    const uint8_t *message,
    size_t message_len,
    uint8_t **signature_out,
    size_t *signature_len_out) {
  *signature_out = NULL;
  *signature_len_out = 0;

  bool ok = false;
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  EVP_PKEY_CTX *pkey_ctx = NULL;
  uint8_t *signature = NULL;
  size_t signature_len = 0;
  if (ctx == NULL ||
      EVP_DigestSignInit(ctx, &pkey_ctx, EVP_sha256(), NULL, key) != 1 ||
      pkey_ctx == NULL ||
      EVP_PKEY_CTX_set_rsa_padding(pkey_ctx, RSA_PKCS1_PSS_PADDING) != 1 ||
      EVP_PKEY_CTX_set_rsa_pss_saltlen(pkey_ctx, RSA_PSS_SALTLEN_DIGEST) != 1 ||
      EVP_PKEY_CTX_set_rsa_mgf1_md(pkey_ctx, EVP_sha256()) != 1 ||
      EVP_DigestSign(ctx, NULL, &signature_len, message, message_len) != 1) {
    goto done;
  }
  signature = malloc(signature_len);
  if (signature == NULL ||
      EVP_DigestSign(ctx, signature, &signature_len, message, message_len) != 1) {
    goto done;
  }
  *signature_out = signature;
  *signature_len_out = signature_len;
  signature = NULL;
  ok = true;

done:
  free(signature);
  EVP_MD_CTX_free(ctx);
  return ok;
}

int main(int argc, char **argv) {
  if (argc != 4) {
    fprintf(stderr, "usage: %s CA_PEM LEAF_KEY_PEM LEAF_DER\n", argv[0]);
    return 1;
  }

  size_t ca_len = 0;
  size_t leaf_der_len = 0;
  uint8_t *ca = read_file(argv[1], &ca_len);
  uint8_t *leaf_der = read_file(argv[3], &leaf_der_len);
  if (ca == NULL || leaf_der == NULL) {
    free(ca);
    free(leaf_der);
    return 1;
  }

  tls13_peer_identity *peer = NULL;
  bool ok = tls13_openssl_validate_leaf_der("localhost", ca, ca_len, leaf_der, leaf_der_len, &peer);
  if (!ok || peer == NULL) {
    fprintf(stderr, "expected localhost certificate validation to succeed\n");
    free(ca);
    free(leaf_der);
    return 1;
  }

  const uint8_t message[] = "TLS 1.3 CertificateVerify test message";
  EVP_PKEY *leaf_key = read_private_key_pem(argv[2]);
  uint8_t *signature = NULL;
  size_t signature_len = 0;
  if (leaf_key == NULL ||
      !sign_rsa_pss_sha256(
          leaf_key, message, sizeof message - 1, &signature, &signature_len)) {
    fprintf(stderr, "failed to sign test message with generated leaf key\n");
    EVP_PKEY_free(leaf_key);
    tls13_openssl_peer_identity_free(peer);
    free(ca);
    free(leaf_der);
    return 1;
  }

  if (!tls13_openssl_peer_verify_signature(
          peer,
          TLS13_SIG_RSA_PSS_RSAE_SHA256,
          message,
          sizeof message - 1,
          signature,
          signature_len)) {
    fprintf(stderr, "expected RSA-PSS-SHA256 signature verification to succeed\n");
    free(signature);
    EVP_PKEY_free(leaf_key);
    tls13_openssl_peer_identity_free(peer);
    free(ca);
    free(leaf_der);
    return 1;
  }

  const uint8_t wrong_message[] = "wrong message";
  if (tls13_openssl_peer_verify_signature(
          peer,
          TLS13_SIG_RSA_PSS_RSAE_SHA256,
          wrong_message,
          sizeof wrong_message - 1,
          signature,
          signature_len)) {
    fprintf(stderr, "expected RSA-PSS-SHA256 verification to reject wrong message\n");
    free(signature);
    EVP_PKEY_free(leaf_key);
    tls13_openssl_peer_identity_free(peer);
    free(ca);
    free(leaf_der);
    return 1;
  }

  signature[0] ^= 0xffu;
  if (tls13_openssl_peer_verify_signature(
          peer,
          TLS13_SIG_RSA_PSS_RSAE_SHA256,
          message,
          sizeof message - 1,
          signature,
          signature_len)) {
    fprintf(stderr, "expected RSA-PSS-SHA256 verification to reject bad signature\n");
    free(signature);
    EVP_PKEY_free(leaf_key);
    tls13_openssl_peer_identity_free(peer);
    free(ca);
    free(leaf_der);
    return 1;
  }
  signature[0] ^= 0xffu;

  if (tls13_openssl_peer_verify_signature(
          peer, 0xffffu, message, sizeof message - 1, signature, signature_len)) {
    fprintf(stderr, "expected unsupported signature scheme to fail\n");
    free(signature);
    EVP_PKEY_free(leaf_key);
    tls13_openssl_peer_identity_free(peer);
    free(ca);
    free(leaf_der);
    return 1;
  }

  free(signature);
  EVP_PKEY_free(leaf_key);
  tls13_openssl_peer_identity_free(peer);

  peer = NULL;
  ok = tls13_openssl_validate_leaf_der("not-localhost.example", ca, ca_len, leaf_der, leaf_der_len, &peer);
  if (ok || peer != NULL) {
    fprintf(stderr, "expected wrong-hostname DER certificate validation to fail\n");
    tls13_openssl_peer_identity_free(peer);
    free(ca);
    free(leaf_der);
    return 1;
  }

  free(ca);
  free(leaf_der);
  printf("OpenSSL X.509 and signature stub tests passed\n");
  return 0;
}
