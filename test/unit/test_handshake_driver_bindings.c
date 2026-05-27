#include "TLS13_Handshake_Driver.h"

#include <stdio.h>

enum handshake_step {
  STEP_SEND_CLIENT_HELLO = 1,
  STEP_RECV_SERVER_HELLO,
  STEP_RECV_ENCRYPTED_EXTENSIONS,
  STEP_RECV_CERTIFICATE,
  STEP_VALIDATE_CERTIFICATE,
  STEP_RECV_CERTIFICATE_VERIFY,
  STEP_RECV_SERVER_FINISHED,
  STEP_SEND_CLIENT_FINISHED,
};

struct TLS13_Handshake_handshake_context_s {
  bool client_hello_ok;
  bool server_hello_ok;
  bool encrypted_extensions_ok;
  bool certificate_ok;
  bool validate_certificate_ok;
  bool certificate_verify_ok;
  bool server_finished_ok;
  bool client_finished_ok;
  enum handshake_step calls[8];
  size_t call_count;
};

struct TLS13_IO_channel_s {
  int unused;
};

static void record_call(
    TLS13_Handshake_handshake_context ctx,
    enum handshake_step step) {
  if (ctx->call_count < sizeof ctx->calls / sizeof ctx->calls[0]) {
    ctx->calls[ctx->call_count] = step;
  }
  ctx->call_count++;
}

bool TLS13_Handshake_send_client_hello(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_raw;
  record_call(ctx, STEP_SEND_CLIENT_HELLO);
  return ctx->client_hello_ok;
}

bool TLS13_Handshake_recv_server_hello(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_raw;
  record_call(ctx, STEP_RECV_SERVER_HELLO);
  return ctx->server_hello_ok;
}

bool TLS13_Handshake_recv_encrypted_extensions(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_raw;
  record_call(ctx, STEP_RECV_ENCRYPTED_EXTENSIONS);
  return ctx->encrypted_extensions_ok;
}

bool TLS13_Handshake_recv_certificate(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_raw;
  record_call(ctx, STEP_RECV_CERTIFICATE);
  return ctx->certificate_ok;
}

bool TLS13_Handshake_validate_certificate(
    TLS13_Handshake_handshake_context ctx,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw) {
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_raw;
  record_call(ctx, STEP_VALIDATE_CERTIFICATE);
  return ctx->validate_certificate_ok;
}

bool TLS13_Handshake_recv_certificate_verify(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_raw;
  record_call(ctx, STEP_RECV_CERTIFICATE_VERIFY);
  return ctx->certificate_verify_ok;
}

bool TLS13_Handshake_recv_server_finished(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_raw;
  record_call(ctx, STEP_RECV_SERVER_FINISHED);
  return ctx->server_finished_ok;
}

bool TLS13_Handshake_send_client_finished(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_raw) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_raw;
  record_call(ctx, STEP_SEND_CLIENT_FINISHED);
  return ctx->client_finished_ok;
}

static int expect_trace(
    const char *name,
    const struct TLS13_Handshake_handshake_context_s *ctx,
    const enum handshake_step *expected,
    size_t expected_len) {
  if (ctx->call_count != expected_len) {
    fprintf(stderr, "%s call count: got %zu, expected %zu\n", name, ctx->call_count, expected_len);
    return 1;
  }
  for (size_t i = 0; i < expected_len; ++i) {
    if (ctx->calls[i] != expected[i]) {
      fprintf(stderr, "%s call %zu: got %d, expected %d\n", name, i, ctx->calls[i], expected[i]);
      return 1;
    }
  }
  return 0;
}

static int test_success_path(void) {
  struct TLS13_Handshake_handshake_context_s ctx = {
      .client_hello_ok = true,
      .server_hello_ok = true,
      .encrypted_extensions_ok = true,
      .certificate_ok = true,
      .validate_certificate_ok = true,
      .certificate_verify_ok = true,
      .server_finished_ok = true,
      .client_finished_ok = true,
  };
  struct TLS13_IO_channel_s ch = {0};
  bool ok = TLS13_Handshake_Driver_run_client_handshake(&ctx, &ch);
  static const enum handshake_step expected[] = {
      STEP_SEND_CLIENT_HELLO,
      STEP_RECV_SERVER_HELLO,
      STEP_RECV_ENCRYPTED_EXTENSIONS,
      STEP_RECV_CERTIFICATE,
      STEP_VALIDATE_CERTIFICATE,
      STEP_RECV_CERTIFICATE_VERIFY,
      STEP_RECV_SERVER_FINISHED,
      STEP_SEND_CLIENT_FINISHED,
  };
  if (!ok) {
    fprintf(stderr, "handshake success path returned false\n");
    return 1;
  }
  return expect_trace("success", &ctx, expected, sizeof expected / sizeof expected[0]);
}

static int test_server_hello_failure_short_circuits(void) {
  struct TLS13_Handshake_handshake_context_s ctx = {
      .client_hello_ok = true,
  };
  struct TLS13_IO_channel_s ch = {0};
  bool ok = TLS13_Handshake_Driver_run_client_handshake(&ctx, &ch);
  static const enum handshake_step expected[] = {
      STEP_SEND_CLIENT_HELLO,
      STEP_RECV_SERVER_HELLO,
  };
  if (ok) {
    fprintf(stderr, "server-hello failure path returned true\n");
    return 1;
  }
  return expect_trace("server hello failure", &ctx, expected, sizeof expected / sizeof expected[0]);
}

static int test_certificate_validation_failure_short_circuits(void) {
  struct TLS13_Handshake_handshake_context_s ctx = {
      .client_hello_ok = true,
      .server_hello_ok = true,
      .encrypted_extensions_ok = true,
      .certificate_ok = true,
      .validate_certificate_ok = false,
      .certificate_verify_ok = true,
      .server_finished_ok = true,
      .client_finished_ok = true,
  };
  struct TLS13_IO_channel_s ch = {0};
  bool ok = TLS13_Handshake_Driver_run_client_handshake(&ctx, &ch);
  static const enum handshake_step expected[] = {
      STEP_SEND_CLIENT_HELLO,
      STEP_RECV_SERVER_HELLO,
      STEP_RECV_ENCRYPTED_EXTENSIONS,
      STEP_RECV_CERTIFICATE,
      STEP_VALIDATE_CERTIFICATE,
  };
  if (ok) {
    fprintf(stderr, "certificate-validation failure path returned true\n");
    return 1;
  }
  return expect_trace("certificate validation failure", &ctx, expected, sizeof expected / sizeof expected[0]);
}

int main(void) {
  int failed = 0;
  failed |= test_success_path();
  failed |= test_server_hello_failure_short_circuits();
  failed |= test_certificate_validation_failure_short_circuits();
  if (failed != 0) {
    return 1;
  }
  printf("handshake driver binding test passed\n");
  return 0;
}
