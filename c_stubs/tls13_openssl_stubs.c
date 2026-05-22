#include "tls13_openssl_stubs.h"

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
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

  *out_peer = NULL;
  bool ok = false;
  X509 *trust_anchor = NULL;
  X509 *leaf = NULL;
  X509_STORE *store = NULL;
  X509_STORE_CTX *ctx = NULL;
  tls13_peer_identity *peer = NULL;

  trust_anchor = read_single_cert_pem(trust_anchor_pem, trust_anchor_pem_len);
  leaf = read_single_cert_pem(chain_pem, chain_pem_len);
  store = X509_STORE_new();
  ctx = X509_STORE_CTX_new();
  peer = calloc(1, sizeof *peer);
  if (trust_anchor == NULL || leaf == NULL || store == NULL || ctx == NULL || peer == NULL) {
    goto done;
  }
  if (X509_STORE_add_cert(store, trust_anchor) != 1) {
    goto done;
  }
  if (X509_STORE_CTX_init(ctx, store, leaf, NULL) != 1) {
    goto done;
  }
  X509_VERIFY_PARAM *param = X509_STORE_CTX_get0_param(ctx);
  if (param == NULL || X509_VERIFY_PARAM_set1_host(param, hostname, 0) != 1) {
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
  X509_free(leaf);
  X509_free(trust_anchor);
  return ok;
}

void tls13_openssl_peer_identity_free(tls13_peer_identity *peer) {
  if (peer == NULL) {
    return;
  }
  EVP_PKEY_free(peer->leaf_public_key);
  free(peer);
}
