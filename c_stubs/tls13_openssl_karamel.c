#include "tls13_openssl_karamel.h"

#if __has_include("TLS13_OpenSSL.h")
#include "TLS13_OpenSSL.h"
#else
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#ifndef FStar_Pervasives_Native_None
#define FStar_Pervasives_Native_None 0
#endif
#ifndef FStar_Pervasives_Native_Some
#define FStar_Pervasives_Native_Some 1
#endif
typedef uint8_t FStar_Pervasives_Native_option_tag;
typedef struct FStar_Pervasives_Native_option__size_t_s {
  FStar_Pervasives_Native_option_tag tag;
  size_t v;
} FStar_Pervasives_Native_option__size_t;
typedef struct FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials_s {
  FStar_Pervasives_Native_option_tag tag;
  TLS13_OpenSSL_server_credentials v;
} FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials;
#endif

#include "tls13_openssl_stubs.h"

#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>

struct TLS13_OpenSSL_auth_config_s {
  atomic_size_t references;
  char *server_name;
  tls13_trust_store *trust_store;
  size_t validation_time_seconds;
};

struct TLS13_OpenSSL_auth_context_s {
  TLS13_OpenSSL_auth_config config;
  tls13_peer_identity *peer;
};

struct TLS13_OpenSSL_server_credentials_s {
  tls13_server_credentials *raw;
};

void TLS13_OpenSSL_auth_config_free(TLS13_OpenSSL_auth_config config);
void TLS13_OpenSSL_auth_context_free(TLS13_OpenSSL_auth_context ctx);
void TLS13_OpenSSL_server_credentials_free(TLS13_OpenSSL_server_credentials creds);

static char *duplicate_hostname_bytes(uint8_t *src, size_t len) {
  if (src == NULL || len == 0u || memchr(src, '\0', len) != NULL) {
    return NULL;
  }
  char *dst = malloc(len + 1u);
  if (dst == NULL) {
    return NULL;
  }
  memcpy(dst, src, len);
  dst[len] = '\0';
  return dst;
}

static void auth_config_retain(TLS13_OpenSSL_auth_config config) {
  (void)atomic_fetch_add_explicit(
      &config->references, (size_t)1u, memory_order_relaxed);
}

TLS13_OpenSSL_auth_config
TLS13_OpenSSL_auth_config_new(
    uint8_t *server_name,
    size_t server_name_len,
    uint8_t *trust_anchors,
    size_t trust_anchors_len,
    size_t validation_time_seconds) {
  TLS13_OpenSSL_auth_config config = calloc(1u, sizeof *config);
  if (config == NULL) {
    abort();
  }
  atomic_init(&config->references, (size_t)1u);
  config->server_name =
      duplicate_hostname_bytes(server_name, server_name_len);
  config->trust_store =
      tls13_openssl_trust_store_new(trust_anchors, trust_anchors_len);
  config->validation_time_seconds = validation_time_seconds;
  if (config->server_name == NULL) {
    TLS13_OpenSSL_auth_config_free(config);
    abort();
  }
  return config;
}

TLS13_OpenSSL_auth_context
TLS13_OpenSSL_auth_context_new(TLS13_OpenSSL_auth_config config) {
  if (config == NULL) {
    abort();
  }
  TLS13_OpenSSL_auth_context ctx = calloc(1u, sizeof *ctx);
  if (ctx == NULL) {
    abort();
  }
  auth_config_retain(config);
  ctx->config = config;
  return ctx;
}

bool TLS13_OpenSSL_validate_certificate_for_local_event(
    TLS13_OpenSSL_auth_context ctx,
    uint8_t *leaf_der,
    size_t leaf_der_capacity,
    size_t leaf_der_len,
    uint8_t *payload,
    size_t payload_len) {
  if (ctx == NULL || ctx->config == NULL || leaf_der == NULL ||
      payload == NULL ||
      leaf_der_len == 0u || leaf_der_len > leaf_der_capacity ||
      leaf_der_len > payload_len) {
    return false;
  }

  tls13_peer_identity *peer = NULL;
  if (!tls13_openssl_validate_leaf_der_with_store(
          ctx->config->server_name,
          ctx->config->trust_store,
          ctx->config->validation_time_seconds,
          leaf_der,
          leaf_der_len,
          &peer)) {
    return false;
  }

  tls13_openssl_peer_identity_free(ctx->peer);
  ctx->peer = peer;
  memset(payload, 0, payload_len);
  memcpy(payload, leaf_der, leaf_der_len);
  return true;
}

bool TLS13_OpenSSL_verify_certificate_signature_for_local_event(
    TLS13_OpenSSL_auth_context ctx,
    uint8_t *certificate_verify_input,
    size_t certificate_verify_input_capacity,
    size_t certificate_verify_input_len,
    uint16_t signature_scheme,
    uint8_t *signature,
    size_t signature_capacity,
    size_t signature_len) {
  if (ctx == NULL || ctx->peer == NULL ||
      certificate_verify_input == NULL || signature == NULL ||
      certificate_verify_input_len > certificate_verify_input_capacity ||
      signature_len == 0u || signature_len > signature_capacity) {
    return false;
  }
  return tls13_openssl_peer_verify_signature(
      ctx->peer,
      signature_scheme,
      certificate_verify_input,
      certificate_verify_input_len,
      signature,
      signature_len);
}

FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials
TLS13_OpenSSL_server_credentials_new(
    uint8_t *certificate_chain,
    size_t certificate_chain_len,
    uint8_t *private_key,
    size_t private_key_len) {
  FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials result = {
      .tag = FStar_Pervasives_Native_None,
      .v = NULL,
  };
  tls13_server_credentials *raw =
      tls13_openssl_server_credentials_new(
          certificate_chain,
          certificate_chain_len,
          private_key,
          private_key_len);
  if (raw == NULL) {
    return result;
  }

  TLS13_OpenSSL_server_credentials creds = calloc(1, sizeof *creds);
  if (creds == NULL) {
    tls13_openssl_server_credentials_free(raw);
    return result;
  }
  creds->raw = raw;
  result.tag = FStar_Pervasives_Native_Some;
  result.v = creds;
  return result;
}

FStar_Pervasives_Native_option__size_t
TLS13_OpenSSL_sign_certificate_verify(
    TLS13_OpenSSL_server_credentials creds,
    uint8_t *input,
    size_t input_len,
    uint8_t *signature,
    size_t signature_capacity) {
  FStar_Pervasives_Native_option__size_t result = {
      .tag = FStar_Pervasives_Native_None,
      .v = 0,
  };
  size_t signature_len = 0;
  if (creds != NULL &&
      tls13_openssl_server_sign_rsa_pss_sha256(
          creds->raw,
          input,
          input_len,
          signature,
          signature_capacity,
          &signature_len)) {
    result.tag = FStar_Pervasives_Native_Some;
    result.v = signature_len;
  }
  return result;
}

FStar_Pervasives_Native_option__size_t
TLS13_OpenSSL_copy_server_certificate_chain(
    TLS13_OpenSSL_server_credentials creds,
    uint8_t *out,
    size_t out_capacity) {
  FStar_Pervasives_Native_option__size_t result = {
      .tag = FStar_Pervasives_Native_None,
      .v = 0,
  };
  size_t out_len = 0;
  if (creds != NULL &&
      tls13_openssl_server_copy_certificate_chain(
          creds->raw,
          out,
          out_capacity,
          &out_len)) {
    result.tag = FStar_Pervasives_Native_Some;
    result.v = out_len;
  }
  return result;
}

void TLS13_OpenSSL_auth_config_free(TLS13_OpenSSL_auth_config config) {
  if (config == NULL) {
    return;
  }
  if (atomic_fetch_sub_explicit(
          &config->references, (size_t)1u, memory_order_acq_rel) !=
      (size_t)1u) {
    return;
  }
  tls13_openssl_trust_store_free(config->trust_store);
  free(config->server_name);
  free(config);
}

void TLS13_OpenSSL_auth_context_free(TLS13_OpenSSL_auth_context ctx) {
  if (ctx == NULL) {
    return;
  }
  tls13_openssl_peer_identity_free(ctx->peer);
  TLS13_OpenSSL_auth_config_free(ctx->config);
  free(ctx);
}

void TLS13_OpenSSL_server_credentials_free(TLS13_OpenSSL_server_credentials creds) {
  if (creds == NULL) {
    return;
  }
  tls13_openssl_server_credentials_free(creds->raw);
  free(creds);
}
