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
#include <string.h>

struct tls13_peer_identity_s {
  EVP_PKEY *leaf_public_key;
};

struct tls13_server_credentials_s {
  uint8_t *certificate_chain;
  size_t certificate_chain_len;
  EVP_PKEY *private_key;
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

static EVP_PKEY *read_private_key_pem_or_der(const uint8_t *bytes, size_t len) {
  if (bytes == NULL || len == 0u || len > INT_MAX) {
    return NULL;
  }
  BIO *bio = BIO_new_mem_buf(bytes, (int)len);
  if (bio == NULL) {
    return NULL;
  }
  EVP_PKEY *key = PEM_read_bio_PrivateKey(bio, NULL, NULL, NULL);
  BIO_free(bio);
  if (key != NULL) {
    return key;
  }
  if (len > LONG_MAX) {
    return NULL;
  }
  const unsigned char *p = bytes;
  key = d2i_AutoPrivateKey(NULL, &p, (long)len);
  if (key != NULL && p != bytes + len) {
    EVP_PKEY_free(key);
    return NULL;
  }
  return key;
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

tls13_server_credentials *tls13_openssl_server_credentials_new(
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key,
    size_t private_key_len) {
  if ((certificate_chain == NULL && certificate_chain_len != 0u) ||
      private_key == NULL || private_key_len == 0u) {
    return NULL;
  }
  tls13_server_credentials *creds = calloc(1, sizeof *creds);
  if (creds == NULL) {
    return NULL;
  }
  creds->certificate_chain = calloc(certificate_chain_len == 0u ? 1u : certificate_chain_len, 1u);
  if (creds->certificate_chain == NULL) {
    tls13_openssl_server_credentials_free(creds);
    return NULL;
  }
  if (certificate_chain_len != 0u) {
    memcpy(creds->certificate_chain, certificate_chain, certificate_chain_len);
  }
  creds->certificate_chain_len = certificate_chain_len;
  creds->private_key = read_private_key_pem_or_der(private_key, private_key_len);
  if (creds->private_key == NULL || EVP_PKEY_base_id(creds->private_key) != EVP_PKEY_RSA) {
    tls13_openssl_server_credentials_free(creds);
    return NULL;
  }
  return creds;
}

bool tls13_openssl_server_sign_rsa_pss_sha256(
    const tls13_server_credentials *creds,
    const uint8_t *message,
    size_t message_len,
    uint8_t *signature,
    size_t signature_capacity,
    size_t *signature_len) {
  if (creds == NULL || creds->private_key == NULL || message == NULL ||
      signature == NULL || signature_len == NULL) {
    return false;
  }

  bool ok = false;
  EVP_MD_CTX *ctx = EVP_MD_CTX_new();
  EVP_PKEY_CTX *pkey_ctx = NULL;
  size_t needed = 0u;
  if (ctx == NULL ||
      EVP_DigestSignInit(ctx, &pkey_ctx, EVP_sha256(), NULL, creds->private_key) != 1 ||
      pkey_ctx == NULL ||
      EVP_PKEY_CTX_set_rsa_padding(pkey_ctx, RSA_PKCS1_PSS_PADDING) != 1 ||
      EVP_PKEY_CTX_set_rsa_pss_saltlen(pkey_ctx, RSA_PSS_SALTLEN_DIGEST) != 1 ||
      EVP_PKEY_CTX_set_rsa_mgf1_md(pkey_ctx, EVP_sha256()) != 1 ||
      EVP_DigestSign(ctx, NULL, &needed, message, message_len) != 1 ||
      needed > signature_capacity ||
      EVP_DigestSign(ctx, signature, &needed, message, message_len) != 1) {
    goto done;
  }
  *signature_len = needed;
  ok = true;

done:
  EVP_MD_CTX_free(ctx);
  return ok;
}

bool tls13_openssl_server_copy_certificate_chain(
    const tls13_server_credentials *creds,
    uint8_t *out,
    size_t out_capacity,
    size_t *out_len) {
  if (creds == NULL || out == NULL || out_len == NULL) {
    return false;
  }
  if (creds->certificate_chain_len > out_capacity) {
    return false;
  }
  if (creds->certificate_chain_len != 0u) {
    memcpy(out, creds->certificate_chain, creds->certificate_chain_len);
  }
  *out_len = creds->certificate_chain_len;
  return true;
}

void tls13_openssl_peer_identity_free(tls13_peer_identity *peer) {
  if (peer == NULL) {
    return;
  }
  EVP_PKEY_free(peer->leaf_public_key);
  free(peer);
}

void tls13_openssl_server_credentials_free(tls13_server_credentials *creds) {
  if (creds == NULL) {
    return;
  }
  EVP_PKEY_free(creds->private_key);
  free(creds->certificate_chain);
  free(creds);
}
