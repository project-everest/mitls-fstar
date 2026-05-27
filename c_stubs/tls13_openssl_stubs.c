#include "tls13_openssl_stubs.h"

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>

#include <limits.h>
#include <stdlib.h>

struct tls13_peer_identity_s {
  EVP_PKEY *leaf_public_key;
};

static X509 *read_single_cert_pem(const uint8_t *pem, size_t pem_len) {
  BIO *bio = BIO_new_mem_buf(pem, (int)pem_len);
  if (bio == NULL) {
    return NULL;
  }
  X509 *cert = PEM_read_bio_X509(bio, NULL, NULL, NULL);
  BIO_free(bio);
  return cert;
}

static X509 *read_single_cert_der(const uint8_t *der, size_t der_len) {
  if (der_len > LONG_MAX) {
    return NULL;
  }
  const unsigned char *p = der;
  X509 *cert = d2i_X509(NULL, &p, (long)der_len);
  if (cert != NULL && p != der + der_len) {
    X509_free(cert);
    return NULL;
  }
  return cert;
}

static bool validate_leaf_cert(
    const char *hostname,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    X509 *leaf,
    tls13_peer_identity **out_peer) {
  if (hostname == NULL || trust_anchor_pem == NULL || leaf == NULL || out_peer == NULL ||
      trust_anchor_pem_len > INT_MAX) {
    return false;
  }

  *out_peer = NULL;
  bool ok = false;
  X509 *trust_anchor = NULL;
  X509_STORE *store = NULL;
  X509_STORE_CTX *ctx = NULL;
  tls13_peer_identity *peer = NULL;

  trust_anchor = read_single_cert_pem(trust_anchor_pem, trust_anchor_pem_len);
  store = X509_STORE_new();
  ctx = X509_STORE_CTX_new();
  peer = calloc(1, sizeof *peer);
  if (trust_anchor == NULL || store == NULL || ctx == NULL || peer == NULL) {
    goto done;
  }
  if (X509_STORE_add_cert(store, trust_anchor) != 1) {
    goto done;
  }
  if (X509_STORE_CTX_init(ctx, store, leaf, NULL) != 1) {
    goto done;
  }
  X509_VERIFY_PARAM *param = X509_STORE_CTX_get0_param(ctx);
  if (param == NULL ||
      (X509_VERIFY_PARAM_set1_ip_asc(param, hostname) != 1 &&
       X509_VERIFY_PARAM_set1_host(param, hostname, 0) != 1)) {
    goto done;
  }
  if (X509_verify_cert(ctx) != 1) {
    goto done;
  }
  peer->leaf_public_key = X509_get_pubkey(leaf);
  if (peer->leaf_public_key == NULL) {
    goto done;
  }
  *out_peer = peer;
  peer = NULL;
  ok = true;

done:
  tls13_openssl_peer_identity_free(peer);
  X509_STORE_CTX_free(ctx);
  X509_STORE_free(store);
  X509_free(trust_anchor);
  return ok;
}

bool tls13_openssl_validate_chain_pem(
    const char *hostname,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    const uint8_t *chain_pem,
    size_t chain_pem_len,
    tls13_peer_identity **out_peer) {
  if (hostname == NULL || trust_anchor_pem == NULL || chain_pem == NULL || out_peer == NULL ||
      trust_anchor_pem_len > INT_MAX || chain_pem_len > INT_MAX) {
    return false;
  }

  X509 *leaf = NULL;
  leaf = read_single_cert_pem(chain_pem, chain_pem_len);
  bool ok = validate_leaf_cert(hostname, trust_anchor_pem, trust_anchor_pem_len, leaf, out_peer);
  X509_free(leaf);
  return ok;
}

bool tls13_openssl_validate_leaf_der(
    const char *hostname,
    const uint8_t *trust_anchor_pem,
    size_t trust_anchor_pem_len,
    const uint8_t *leaf_der,
    size_t leaf_der_len,
    tls13_peer_identity **out_peer) {
  if (hostname == NULL || trust_anchor_pem == NULL || leaf_der == NULL || out_peer == NULL ||
      trust_anchor_pem_len > INT_MAX || leaf_der_len > LONG_MAX) {
    return false;
  }

  X509 *leaf = read_single_cert_der(leaf_der, leaf_der_len);
  bool ok = validate_leaf_cert(hostname, trust_anchor_pem, trust_anchor_pem_len, leaf, out_peer);
  X509_free(leaf);
  return ok;
}

static bool verify_rsa_pss_rsae_sha256(
    EVP_PKEY *public_key,
    const uint8_t *message,
    size_t message_len,
    const uint8_t *signature,
    size_t signature_len) {
  if (public_key == NULL || EVP_PKEY_base_id(public_key) != EVP_PKEY_RSA) {
    return false;
  }

  bool ok = false;
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  EVP_PKEY_CTX *pkey_ctx = NULL;
  if (ctx == NULL ||
      EVP_DigestVerifyInit(ctx, &pkey_ctx, EVP_sha256(), NULL, public_key) != 1 ||
      pkey_ctx == NULL ||
      EVP_PKEY_CTX_set_rsa_padding(pkey_ctx, RSA_PKCS1_PSS_PADDING) != 1 ||
      EVP_PKEY_CTX_set_rsa_pss_saltlen(pkey_ctx, RSA_PSS_SALTLEN_DIGEST) != 1 ||
      EVP_PKEY_CTX_set_rsa_mgf1_md(pkey_ctx, EVP_sha256()) != 1) {
    goto done;
  }
  ok = EVP_DigestVerify(ctx, signature, signature_len, message, message_len) == 1;

done:
  EVP_MD_CTX_free(ctx);
  return ok;
}

bool tls13_openssl_peer_verify_signature(
    const tls13_peer_identity *peer,
    uint16_t signature_scheme,
    const uint8_t *message,
    size_t message_len,
    const uint8_t *signature,
    size_t signature_len) {
  if (peer == NULL || message == NULL || signature == NULL) {
    return false;
  }
  switch (signature_scheme) {
  case TLS13_SIG_RSA_PSS_RSAE_SHA256:
    return verify_rsa_pss_rsae_sha256(
        peer->leaf_public_key, message, message_len, signature, signature_len);
  default:
    return false;
  }
}

void tls13_openssl_peer_identity_free(tls13_peer_identity *peer) {
  if (peer == NULL) {
    return;
  }
  EVP_PKEY_free(peer->leaf_public_key);
  free(peer);
}
