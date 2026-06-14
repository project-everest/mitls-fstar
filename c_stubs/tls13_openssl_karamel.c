#include "tls13_openssl_karamel.h"

#if __has_include("TLS13_OpenSSL.h")
#include "TLS13_OpenSSL.h"
#else
#include <stddef.h>
#include <stdint.h>
#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1
typedef uint8_t FStar_Pervasives_Native_option__TLS13_OpenSSL_auth_context_tags;
typedef struct FStar_Pervasives_Native_option__TLS13_OpenSSL_auth_context_s {
  FStar_Pervasives_Native_option__TLS13_OpenSSL_auth_context_tags tag;
  TLS13_OpenSSL_auth_context v;
} FStar_Pervasives_Native_option__TLS13_OpenSSL_auth_context;
typedef uint8_t FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials_tags;
typedef struct FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials_s {
  FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials_tags tag;
  TLS13_OpenSSL_server_credentials v;
} FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials;
typedef uint8_t FStar_Pervasives_Native_option__size_t_tags;
typedef struct FStar_Pervasives_Native_option__size_t_s {
  FStar_Pervasives_Native_option__size_t_tags tag;
  size_t v;
} FStar_Pervasives_Native_option__size_t;
#endif

#include "tls13_openssl_stubs.h"

#include <stdlib.h>
#include <string.h>

struct TLS13_OpenSSL_auth_context_s {
  char *server_name;
  uint8_t *trust_anchors;
  size_t trust_anchors_len;
  size_t validation_time_seconds;
  tls13_peer_identity *peer;
};

struct TLS13_OpenSSL_server_credentials_s {
  tls13_server_credentials *creds;
};

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

static uint8_t *duplicate_bytes(uint8_t *src, size_t len) {
  if (src == NULL && len != 0u) {
    return NULL;
  }
  uint8_t *dst = calloc(len == 0u ? 1u : len, sizeof(uint8_t));
  if (dst != NULL && len != 0u) {
    memcpy(dst, src, len);
  }
  return dst;
}

FStar_Pervasives_Native_option__TLS13_OpenSSL_auth_context
TLS13_OpenSSL_auth_context_new(
    uint8_t *server_name,
    size_t server_name_len,
    uint8_t *trust_anchors,
    size_t trust_anchors_len,
    size_t validation_time_seconds) {
  TLS13_OpenSSL_auth_context ctx = calloc(1, sizeof *ctx);
  if (ctx == NULL) {
    return (FStar_Pervasives_Native_option__TLS13_OpenSSL_auth_context){
        .tag = FStar_Pervasives_Native_None};
  }
  ctx->server_name = duplicate_hostname_bytes(server_name, server_name_len);
  ctx->trust_anchors = duplicate_bytes(trust_anchors, trust_anchors_len);
  ctx->trust_anchors_len = trust_anchors_len;
  ctx->validation_time_seconds = validation_time_seconds;
  if (ctx->server_name == NULL || ctx->trust_anchors == NULL) {
    TLS13_OpenSSL_auth_context_free(ctx);
    return (FStar_Pervasives_Native_option__TLS13_OpenSSL_auth_context){
        .tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__TLS13_OpenSSL_auth_context){
      .tag = FStar_Pervasives_Native_Some, .v = ctx};
}

FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials
TLS13_OpenSSL_server_credentials_new(
    uint8_t *certificate_chain,
    size_t certificate_chain_len,
    uint8_t *private_key,
    size_t private_key_len) {
  if ((certificate_chain == NULL && certificate_chain_len != 0u) ||
      private_key == NULL || private_key_len == 0u) {
    return (FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials){
        .tag = FStar_Pervasives_Native_None};
  }
  TLS13_OpenSSL_server_credentials out = calloc(1, sizeof *out);
  if (out == NULL) {
    return (FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials){
        .tag = FStar_Pervasives_Native_None};
  }
  out->creds = tls13_openssl_server_credentials_new(
      certificate_chain,
      certificate_chain_len,
      private_key,
      private_key_len);
  if (out->creds == NULL) {
    TLS13_OpenSSL_server_credentials_free(out);
    return (FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials){
        .tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__TLS13_OpenSSL_server_credentials){
      .tag = FStar_Pervasives_Native_Some, .v = out};
}

FStar_Pervasives_Native_option__size_t
TLS13_OpenSSL_sign_certificate_verify(
    TLS13_OpenSSL_server_credentials creds,
    uint8_t *input,
    size_t input_len,
    uint8_t *signature,
    size_t signature_capacity) {
  if (creds == NULL || creds->creds == NULL || input == NULL || signature == NULL) {
    return (FStar_Pervasives_Native_option__size_t){.tag = FStar_Pervasives_Native_None};
  }
  size_t signature_len = 0u;
  if (!tls13_openssl_server_sign_rsa_pss_sha256(
          creds->creds,
          input,
          input_len,
          signature,
          signature_capacity,
          &signature_len)) {
    return (FStar_Pervasives_Native_option__size_t){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__size_t){
      .tag = FStar_Pervasives_Native_Some,
      .v = signature_len,
  };
}

FStar_Pervasives_Native_option__size_t
TLS13_OpenSSL_copy_server_certificate_chain(
    TLS13_OpenSSL_server_credentials creds,
    uint8_t *out,
    size_t out_capacity) {
  if (creds == NULL || creds->creds == NULL || out == NULL) {
    return (FStar_Pervasives_Native_option__size_t){.tag = FStar_Pervasives_Native_None};
  }
  size_t out_len = 0u;
  if (!tls13_openssl_server_copy_certificate_chain(
          creds->creds,
          out,
          out_capacity,
          &out_len)) {
    return (FStar_Pervasives_Native_option__size_t){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__size_t){
      .tag = FStar_Pervasives_Native_Some,
      .v = out_len,
  };
}

bool TLS13_OpenSSL_validate_certificate_for_local_event(
    TLS13_OpenSSL_auth_context ctx,
    uint8_t *leaf_der,
    size_t leaf_der_capacity,
    size_t leaf_der_len,
    uint8_t *payload,
    size_t payload_len) {
  if (ctx == NULL || leaf_der == NULL || payload == NULL ||
      leaf_der_len == 0u || leaf_der_len > leaf_der_capacity ||
      leaf_der_len > payload_len) {
    return false;
  }

  tls13_peer_identity *peer = NULL;
  if (!tls13_openssl_validate_leaf_der(
          ctx->server_name,
          ctx->trust_anchors,
          ctx->trust_anchors_len,
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

void TLS13_OpenSSL_auth_context_free(TLS13_OpenSSL_auth_context ctx) {
  if (ctx == NULL) {
    return;
  }
  tls13_openssl_peer_identity_free(ctx->peer);
  free(ctx->trust_anchors);
  free(ctx->server_name);
  free(ctx);
}

void TLS13_OpenSSL_server_credentials_free(TLS13_OpenSSL_server_credentials creds) {
  if (creds == NULL) {
    return;
  }
  tls13_openssl_server_credentials_free(creds->creds);
  free(creds);
}
