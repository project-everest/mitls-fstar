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

void TLS13_OpenSSL_auth_context_free(TLS13_OpenSSL_auth_context ctx);

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
