#include "TLS13_Handshake.h"
#include "tls13_handshake_external_layer.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct TLS13_Handshake_External_handshake_context_s {
  bool recv_server_hello_ok;
  bool recv_encrypted_extensions_ok;
  bool recv_certificate_ok;
  bool validate_certificate_ok;
  bool recv_certificate_verify_ok;
  bool recv_server_finished_ok;
  bool send_client_finished_ok;
  unsigned send_client_hello_calls;
  unsigned recv_server_hello_calls;
  unsigned recv_encrypted_extensions_calls;
  unsigned recv_certificate_calls;
  unsigned validate_certificate_calls;
  unsigned recv_certificate_verify_calls;
  unsigned recv_server_finished_calls;
  unsigned send_client_finished_calls;
};

TLS13_Handshake_External_handshake_context TLS13_Handshake_External_context_new(void) {
  struct TLS13_Handshake_External_handshake_context_s *ctx =
      calloc(1, sizeof *ctx);
  if (ctx != NULL) {
    ctx->recv_server_hello_ok = true;
    ctx->recv_encrypted_extensions_ok = true;
    ctx->recv_certificate_ok = true;
    ctx->validate_certificate_ok = true;
    ctx->recv_certificate_verify_ok = true;
    ctx->recv_server_finished_ok = true;
    ctx->send_client_finished_ok = true;
  }
  return ctx;
}

void TLS13_Handshake_External_context_free(
    TLS13_Handshake_External_handshake_context ctx) {
  free(ctx);
}

void TLS13_Handshake_External_send_client_hello(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  (void)ch;
  ctx->send_client_hello_calls++;
}

size_t TLS13_Handshake_External_read_raw(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *old_buf) {
  (void)ctx;
  (void)ch;
  (void)old_buf;
  if (remaining == 0 || offset > total_len || remaining > total_len - offset) {
    return 0;
  }
  size_t chunk = remaining > 3 ? 3 : remaining;
  if (total_len == 5) {
    static const uint8_t header[] = {22, 3, 3, 0, 90};
    memcpy(buf + offset, header + offset, chunk);
    return chunk;
  }
  if (total_len == 90) {
    uint8_t server_hello[90] = {0};
    server_hello[0] = 0x02;
    server_hello[3] = 0x56;
    server_hello[4] = 0x03;
    server_hello[5] = 0x03;
    server_hello[38] = 0x00;
    server_hello[39] = 0x13;
    server_hello[40] = 0x03;
    server_hello[41] = 0x00;
    server_hello[42] = 0x00;
    server_hello[43] = 0x2e;
    server_hello[44] = 0x00;
    server_hello[45] = 0x33;
    server_hello[46] = 0x00;
    server_hello[47] = 0x24;
    server_hello[48] = 0x00;
    server_hello[49] = 0x1d;
    server_hello[50] = 0x00;
    server_hello[51] = 0x20;
    server_hello[84] = 0x00;
    server_hello[85] = 0x2b;
    server_hello[86] = 0x00;
    server_hello[87] = 0x02;
    server_hello[88] = 0x03;
    server_hello[89] = 0x04;
    memcpy(buf + offset, server_hello + offset, chunk);
    return chunk;
  }
  return 0;
}

bool TLS13_Handshake_External_process_server_hello_record(
    TLS13_Handshake_External_handshake_context ctx,
    uint8_t *header,
    size_t header_len,
    uint8_t *fragment,
    size_t fragment_len,
    uint8_t *key_share,
    size_t key_share_len,
    void *header_bytes,
    void *fragment_bytes,
    void *key_share_bytes) {
  (void)header;
  (void)header_len;
  (void)fragment;
  (void)fragment_len;
  (void)key_share;
  (void)key_share_len;
  (void)header_bytes;
  (void)fragment_bytes;
  (void)key_share_bytes;
  ctx->recv_server_hello_calls++;
  return ctx->recv_server_hello_ok;
}

bool TLS13_Handshake_External_recv_encrypted_extensions(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  (void)ch;
  ctx->recv_encrypted_extensions_calls++;
  return ctx->recv_encrypted_extensions_ok;
}

bool TLS13_Handshake_External_recv_certificate(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  (void)ch;
  ctx->recv_certificate_calls++;
  return ctx->recv_certificate_ok;
}

bool TLS13_Handshake_External_validate_certificate(
    TLS13_Handshake_External_handshake_context ctx) {
  ctx->validate_certificate_calls++;
  return ctx->validate_certificate_ok;
}

bool TLS13_Handshake_External_recv_certificate_verify(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  (void)ch;
  ctx->recv_certificate_verify_calls++;
  return ctx->recv_certificate_verify_ok;
}

bool TLS13_Handshake_External_recv_server_finished(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  (void)ch;
  ctx->recv_server_finished_calls++;
  return ctx->recv_server_finished_ok;
}

bool TLS13_Handshake_External_send_client_finished(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  (void)ch;
  ctx->send_client_finished_calls++;
  return ctx->send_client_finished_ok;
}

static int test_success_path(void) {
  TLS13_Handshake_External_handshake_context ctx =
      TLS13_Handshake_External_context_new();
  TLS13_IO_channel ch = (TLS13_IO_channel)ctx;
  if (ctx == NULL) {
    return 1;
  }

  TLS13_Handshake_send_client_hello(ctx, ch);
  bool ok =
      TLS13_Handshake_recv_server_hello(ctx, ch) &&
      TLS13_Handshake_recv_encrypted_extensions(ctx, ch) &&
      TLS13_Handshake_recv_certificate(ctx, ch) &&
      TLS13_Handshake_validate_certificate(ctx) &&
      TLS13_Handshake_recv_certificate_verify(ctx, ch) &&
      TLS13_Handshake_recv_server_finished(ctx, ch) &&
      TLS13_Handshake_send_client_finished(ctx, ch);

  int failed =
      !ok ||
      ctx->send_client_hello_calls != 1 ||
      ctx->recv_server_hello_calls != 1 ||
      ctx->recv_encrypted_extensions_calls != 1 ||
      ctx->recv_certificate_calls != 1 ||
      ctx->validate_certificate_calls != 1 ||
      ctx->recv_certificate_verify_calls != 1 ||
      ctx->recv_server_finished_calls != 1 ||
      ctx->send_client_finished_calls != 1;
  TLS13_Handshake_External_context_free(ctx);
  if (failed) {
    fprintf(stderr, "handshake wrapper success path failed\n");
    return 1;
  }
  return 0;
}

static int test_failure_return(void) {
  TLS13_Handshake_External_handshake_context ctx =
      TLS13_Handshake_External_context_new();
  TLS13_IO_channel ch = (TLS13_IO_channel)ctx;
  if (ctx == NULL) {
    return 1;
  }
  ctx->recv_server_hello_ok = false;
  bool ok = TLS13_Handshake_recv_server_hello(ctx, ch);
  int failed = ok || ctx->recv_server_hello_calls != 1;
  TLS13_Handshake_External_context_free(ctx);
  if (failed) {
    fprintf(stderr, "handshake wrapper failure path failed\n");
    return 1;
  }
  return 0;
}

int main(void) {
  if (test_success_path() != 0 || test_failure_return() != 0) {
    return 1;
  }
  printf("handshake binding test passed\n");
  return 0;
}
