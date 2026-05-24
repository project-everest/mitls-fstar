#include "tls13_connection_external_layer.h"
#include "tls13_hacl_stubs.h"
#include "tls13_handshake_external_layer.h"
#include "tls13_io_stubs.h"
#include "tls13_openssl_stubs.h"

#include "TLS13_Handshake_Framing.h"
#include "TLS13_Handshake_FlightState.h"
#include "TLS13_Handshake_ByteDriver.h"
#include "TLS13_Record.h"
#include "tls13_connection_external_layer.h"

#include "TLS13_Handshake_Driver.h"

#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PROBE_APP_RECORD_CHUNK_LEN 4096u
#define PROBE_CLIENT_HELLO_CAPACITY 512u
#define PROBE_SERVER_HELLO_CAPACITY 4096u
#define PROBE_SERVER_HANDSHAKE_CAPACITY 32768u
#define TLS13_WIRE_RECORD_HEADER_LEN 5u
#define TLS13_WIRE_HANDSHAKE_HEADER_LEN 4u
#define TLS13_WIRE_CERTIFICATE_VERIFY_INPUT_LEN 130u

#define TLS13_Connection_connection TLS13_Connection_External_connection
#define TLS13_Connection_connection_s TLS13_Connection_External_connection_s
#define TLS13_Handshake_ByteDriver_External_context_s TLS13_Connection_External_connection_s

#define TLS13_Handshake_External_handshake_context_s TLS13_Connection_connection_s
typedef TLS13_Handshake_External_handshake_context TLS13_Handshake_handshake_context;

struct TLS13_Connection_connection_s {
  char *host;
  uint16_t port;
  const char *ca_pem_path;
  int fd;
  TLS13_Handshake_FlightState_flight_state server_handshake_flight_state;
};

struct TLS13_IO_channel_s {
  int unused;
};

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

static int write_all_fd(int fd, const uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = tls13_io_write_fd(fd, buf + off, len - off);
    if (n <= 0) {
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

static TLS13_Connection_connection from_handshake_context(
    TLS13_Handshake_handshake_context ctx) {
  return (TLS13_Connection_connection)ctx;
}

static bool handshake_can_continue(TLS13_Connection_connection c) {
  return c != NULL && c->fd >= 0;
}

static void fail_handshake(TLS13_Connection_connection c) {
  if (c == NULL) {
    return;
  }
  if (c->fd >= 0) {
    tls13_io_close_fd(c->fd);
    c->fd = -1;
  }
}

static bool copy_server_handshake_messages(
    TLS13_Connection_connection c,
    uint8_t messages[PROBE_SERVER_HANDSHAKE_CAPACITY]) {
  if (c == NULL || messages == NULL) {
    return false;
  }
  TLS13_Handshake_FlightState_copy_server_handshake(
      c->server_handshake_flight_state,
      messages,
      PROBE_SERVER_HANDSHAKE_CAPACITY);
  return true;
}

static bool process_encrypted_handshake_record(
    TLS13_Connection_connection c,
    uint8_t encrypted_header[TLS13_WIRE_RECORD_HEADER_LEN],
    uint8_t *encrypted_fragment,
    size_t fragment_len) {
  if (fragment_len <= 16 || fragment_len > 20000) {
    fprintf(stderr, "unexpected encrypted handshake fragment length\n");
    return false;
  }
  if (!TLS13_Handshake_FlightState_process_server_handshake_record(
          c->server_handshake_flight_state,
          encrypted_header,
          TLS13_WIRE_RECORD_HEADER_LEN,
          encrypted_fragment,
          fragment_len)) {
    fprintf(stderr, "failed to process OpenSSL encrypted handshake record\n");
    return false;
  }
  return true;
}

static bool process_server_hello_record(
    TLS13_Handshake_handshake_context ctx,
    uint8_t header[TLS13_WIRE_RECORD_HEADER_LEN],
    uint8_t *server_hello_fragment,
    size_t fragment_len,
    uint8_t server_key_share[32],
    size_t server_key_share_len) {
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) ||
      header == NULL ||
      server_hello_fragment == NULL ||
      fragment_len == 0 ||
      fragment_len > PROBE_SERVER_HELLO_CAPACITY ||
      server_key_share == NULL ||
      server_key_share_len != 32) {
    return false;
  }

  uint8_t padded_server_hello_fragment[PROBE_SERVER_HELLO_CAPACITY] = {0};
  memcpy(padded_server_hello_fragment, server_hello_fragment, fragment_len);
  TLS13_Handshake_FlightState_set_server_hello(
      c->server_handshake_flight_state,
      padded_server_hello_fragment,
      sizeof padded_server_hello_fragment,
      fragment_len);
  if (!TLS13_Handshake_FlightState_derive_server_handshake_keys_from_share(
          c->server_handshake_flight_state,
          server_key_share,
          server_key_share_len)) {
    fprintf(stderr, "failed to derive handshake traffic keys\n");
    fail_handshake(c);
    return false;
  }
  return true;
}

static bool probe_handshake_recv_encrypted_extensions(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) || c->fd < 0) {
    return false;
  }

  bool ok = TLS13_Handshake_ByteDriver_recv_encrypted_handshake(
      (TLS13_Handshake_ByteDriver_External_context)c, ch);
  if (!ok) {
    fail_handshake(c);
  }
  return ok;
}

static bool probe_handshake_recv_certificate(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) ||
      !TLS13_Handshake_FlightState_saw_certificate(c->server_handshake_flight_state)
      ) {
    fail_handshake(c);
    return false;
  }
  return true;
}

static bool probe_handshake_validate_certificate(
    TLS13_Handshake_handshake_context ctx,
    void *erased_state_ref,
    void *erased_state) {
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) ||
      !TLS13_Handshake_FlightState_saw_certificate(c->server_handshake_flight_state)
      ) {
    fail_handshake(c);
    return false;
  }
  size_t ca_pem_len = 0;
  uint8_t *ca_pem = read_file(c->ca_pem_path, &ca_pem_len);
  if (ca_pem == NULL) {
    fail_handshake(c);
    return false;
  }
  size_t leaf_der_offset =
      TLS13_Handshake_FlightState_certificate_leaf_offset(c->server_handshake_flight_state);
  size_t leaf_der_len =
      TLS13_Handshake_FlightState_certificate_leaf_len(c->server_handshake_flight_state);
  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!copy_server_handshake_messages(c, server_handshake_messages)) {
    free(ca_pem);
    fail_handshake(c);
    return false;
  }
  const uint8_t *leaf_der = server_handshake_messages + leaf_der_offset;
  tls13_peer_identity *peer = NULL;
  bool ok = tls13_openssl_validate_leaf_der(
      "localhost", ca_pem, ca_pem_len, leaf_der, leaf_der_len, &peer);
  free(ca_pem);
  if (!ok || peer == NULL) {
    fprintf(stderr, "failed to validate server certificate\n");
    fail_handshake(c);
    return false;
  }
  uint8_t certificate_verify_input[TLS13_WIRE_CERTIFICATE_VERIFY_INPUT_LEN];
  if (!TLS13_Handshake_FlightState_build_certificate_verify_input(
          c->server_handshake_flight_state,
          certificate_verify_input,
          sizeof certificate_verify_input)) {
      fprintf(stderr, "failed to build CertificateVerify input\n");
      tls13_openssl_peer_identity_free(peer);
      fail_handshake(c);
      return false;
  }
  uint16_t signature_scheme =
      TLS13_Handshake_FlightState_certificate_verify_signature_scheme(
          c->server_handshake_flight_state);
  size_t signature_offset =
      TLS13_Handshake_FlightState_certificate_verify_signature_offset(
          c->server_handshake_flight_state);
  size_t signature_len =
      TLS13_Handshake_FlightState_certificate_verify_signature_len(
          c->server_handshake_flight_state);
  const uint8_t *signature = server_handshake_messages + signature_offset;
  bool signature_ok = tls13_openssl_peer_verify_signature(
          peer,
          signature_scheme,
          certificate_verify_input,
          sizeof certificate_verify_input,
          signature,
          signature_len);
  tls13_openssl_peer_identity_free(peer);
  if (!signature_ok) {
    fprintf(stderr, "failed to verify server CertificateVerify\n");
    fail_handshake(c);
    return false;
  }
  TLS13_Handshake_FlightState_mark_certificate_verify_verified(c->server_handshake_flight_state);
  return true;
}

static bool probe_handshake_recv_certificate_verify(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) ||
      !TLS13_Handshake_FlightState_certificate_verify_verified(c->server_handshake_flight_state)) {
    fail_handshake(c);
    return false;
  }
  return true;
}

static bool probe_handshake_recv_server_finished(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) ||
      !TLS13_Handshake_FlightState_saw_finished(c->server_handshake_flight_state)
      ) {
    fail_handshake(c);
    return false;
  }
  if (!TLS13_Handshake_FlightState_verify_server_finished(c->server_handshake_flight_state)) {
    fprintf(stderr, "failed to verify OpenSSL server Finished\n");
    fail_handshake(c);
    return false;
  }
  return true;
}

bool TLS13_Handshake_External_connect(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  (void)ch;
  TLS13_Connection_connection c = from_handshake_context((TLS13_Handshake_handshake_context)ctx);
  if (c == NULL || c->fd >= 0) {
    fail_handshake(c);
    return false;
  }
  c->fd = tls13_io_connect_tcp(c->host, c->port);
  if (c->fd < 0) {
    perror("connect");
    fail_handshake(c);
    return false;
  }
  return true;
}

bool TLS13_Handshake_External_store_client_hello(
    TLS13_Handshake_External_handshake_context ctx,
    uint8_t *hello,
    size_t hello_len,
    void *hello_bytes) {
  (void)hello_bytes;
  TLS13_Connection_connection c = from_handshake_context((TLS13_Handshake_handshake_context)ctx);
  if (c == NULL || hello == NULL || hello_len != 130) {
    fail_handshake(c);
    return false;
  }
  uint8_t padded_client_hello[PROBE_CLIENT_HELLO_CAPACITY] = {0};
  memcpy(padded_client_hello, hello, hello_len);
  TLS13_Handshake_FlightState_set_client_hello(
      c->server_handshake_flight_state,
      padded_client_hello,
      sizeof padded_client_hello,
      hello_len);
  return true;
}

size_t TLS13_Handshake_External_read_raw(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *old_buf) {
  (void)ch;
  (void)old_buf;
  TLS13_Connection_connection c = from_handshake_context((TLS13_Handshake_handshake_context)ctx);
  if (!handshake_can_continue(c) || c->fd < 0 || buf == NULL ||
      remaining == 0 || offset > total_len || remaining > total_len - offset) {
    return 0;
  }
  ssize_t n = tls13_io_read_fd(c->fd, buf + offset, remaining);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

size_t TLS13_Handshake_External_write_raw(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *buf_bytes) {
  (void)ch;
  (void)buf_bytes;
  TLS13_Connection_connection c = from_handshake_context((TLS13_Handshake_handshake_context)ctx);
  if (!handshake_can_continue(c) || c->fd < 0 || buf == NULL ||
      remaining == 0 || offset > total_len || remaining > total_len - offset) {
    return 0;
  }
  ssize_t n = tls13_io_write_fd(c->fd, buf + offset, remaining);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

bool TLS13_Handshake_External_build_client_finished_record(
    TLS13_Handshake_External_handshake_context ctx,
    uint8_t *out,
    size_t out_len,
    void *old_out) {
  (void)old_out;
  TLS13_Connection_connection c = from_handshake_context((TLS13_Handshake_handshake_context)ctx);
  if (!handshake_can_continue(c) || out == NULL || out_len != 58) {
    return false;
  }
  return TLS13_Handshake_FlightState_build_client_finished_record(
      c->server_handshake_flight_state, out, out_len);
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
  (void)header_bytes;
  (void)fragment_bytes;
  (void)key_share_bytes;
  if (header_len != TLS13_WIRE_RECORD_HEADER_LEN) {
    return false;
  }
  return process_server_hello_record(
      (TLS13_Handshake_handshake_context)ctx, header, fragment, fragment_len, key_share, key_share_len);
}

bool TLS13_Handshake_External_recv_encrypted_extensions(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  return probe_handshake_recv_encrypted_extensions(
      (TLS13_Handshake_handshake_context)ctx, ch, NULL, NULL);
}

bool TLS13_Handshake_External_recv_certificate(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  return probe_handshake_recv_certificate((TLS13_Handshake_handshake_context)ctx, ch, NULL, NULL);
}

bool TLS13_Handshake_External_validate_certificate(
    TLS13_Handshake_External_handshake_context ctx) {
  return probe_handshake_validate_certificate((TLS13_Handshake_handshake_context)ctx, NULL, NULL);
}

bool TLS13_Handshake_External_recv_certificate_verify(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  return probe_handshake_recv_certificate_verify(
      (TLS13_Handshake_handshake_context)ctx, ch, NULL, NULL);
}

bool TLS13_Handshake_External_recv_server_finished(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  return probe_handshake_recv_server_finished(
      (TLS13_Handshake_handshake_context)ctx, ch, NULL, NULL);
}

static TLS13_Connection_connection tls13_connection_probe_new(
    const char *host,
    uint16_t port,
    const char *ca_pem_path) {
  if (host == NULL || ca_pem_path == NULL) {
    errno = EINVAL;
    return NULL;
  }
  TLS13_Connection_connection c = calloc(1, sizeof *c);
  if (c == NULL) {
    return NULL;
  }
  size_t host_len = strlen(host);
  c->host = malloc(host_len + 1u);
  if (c->host == NULL) {
    free(c);
    return NULL;
  }
  memcpy(c->host, host, host_len + 1u);
  c->port = port;
  c->ca_pem_path = ca_pem_path;
  c->fd = -1;
  c->server_handshake_flight_state = TLS13_Handshake_FlightState_flight_state_new();
  return c;
}

static void tls13_connection_probe_free(TLS13_Connection_connection c) {
  if (c == NULL) {
    return;
  }
  if (c->fd >= 0) {
    tls13_io_close_fd(c->fd);
  }
  TLS13_Handshake_FlightState_flight_state_free(c->server_handshake_flight_state);
  free(c->host);
  free(c);
}




TLS13_Connection_External_connection TLS13_Connection_External_client_new(
    uint8_t *hostname,
    size_t hostname_len,
    TLS13_X509_Spec_trust_store trust_store,
    void *hostname_bytes) {
  (void)hostname_bytes;
  char host[256];
  if (hostname == NULL || hostname_len == 0 || hostname_len >= sizeof host) {
    return NULL;
  }
  memcpy(host, hostname, hostname_len);
  host[hostname_len] = '\0';
  TLS13_Connection_External_config *config =
      (TLS13_Connection_External_config *)trust_store;
  uint16_t port = config == NULL || config->port == 0 ? 443 : config->port;
  const char *ca_pem_path =
      config == NULL || config->ca_pem_path == NULL ? "" : config->ca_pem_path;
  return tls13_connection_probe_new(host, port, ca_pem_path);
}

void TLS13_Connection_External_client_free(TLS13_Connection_External_connection c) {
  tls13_connection_probe_free(c);
}

bool TLS13_Connection_External_client_connect(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *client_key,
    uint8_t *client_iv,
    uint8_t *server_key,
    uint8_t *server_iv,
    void *old_client_key,
    void *old_client_iv,
    void *old_server_key,
    void *old_server_iv) {
  (void)old_client_key;
  (void)old_client_iv;
  (void)old_server_key;
  (void)old_server_iv;
  if (c == NULL || c->fd >= 0 ||
      client_key == NULL || client_iv == NULL || server_key == NULL || server_iv == NULL) {
    return false;
  }
  bool ok = TLS13_Handshake_Driver_run_client_handshake(
      (TLS13_Handshake_handshake_context)c, ch);

  if (!ok) {
    fail_handshake(c);
    return false;
  }
  if (!TLS13_Handshake_FlightState_derive_application_keys(
          c->server_handshake_flight_state,
          client_key,
          32,
          client_iv,
          12,
          server_key,
          32,
          server_iv,
          12)) {
    fprintf(stderr, "failed to derive application traffic keys\n");
    fail_handshake(c);
    return false;
  }
  return true;
}

size_t TLS13_Connection_External_client_write_raw(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *buf_bytes) {
  (void)ch;
  (void)buf_bytes;
  if (c == NULL || c->fd < 0 || buf == NULL ||
      remaining == 0 || offset > total_len || remaining > total_len - offset) {
    return 0;
  }
  ssize_t n = tls13_io_write_fd(c->fd, buf + offset, remaining);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

size_t TLS13_Connection_External_client_read_raw(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *old_buf) {
  (void)ch;
  (void)old_buf;
  if (c == NULL || c->fd < 0 || buf == NULL ||
      remaining == 0 || offset > total_len || remaining > total_len - offset) {
    return 0;
  }
  ssize_t n = tls13_io_read_fd(c->fd, buf + offset, remaining);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

bool TLS13_Connection_External_client_close(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch) {
  (void)ch;
  if (c == NULL) {
    return false;
  }
  if (c->fd >= 0) {
    tls13_io_close_fd(c->fd);
    c->fd = -1;
  }
  return true;
}

void TLS13_Handshake_ByteDriver_External_reset_encrypted_handshake(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *old_progress) {
  (void)old_progress;
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  if (c == NULL) {
    return;
  }
  TLS13_Handshake_FlightState_reset(c->server_handshake_flight_state);
  uint8_t server_handshake_key[32] = {0};
  uint8_t server_handshake_iv[12] = {0};
  TLS13_Handshake_FlightState_copy_server_handshake_key_iv(
      c->server_handshake_flight_state,
      server_handshake_key,
      sizeof server_handshake_key,
      server_handshake_iv,
      sizeof server_handshake_iv);
  TLS13_Handshake_FlightState_install_server_handshake_record_keys(
      c->server_handshake_flight_state,
      server_handshake_key,
      server_handshake_iv);
}

size_t TLS13_Handshake_ByteDriver_External_read_raw(
    TLS13_Handshake_ByteDriver_External_context ctx,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *progress,
    void *old_buf) {
  (void)ch;
  (void)progress;
  (void)old_buf;
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  if (!handshake_can_continue(c) || c->fd < 0 || buf == NULL ||
      remaining == 0 || offset > total_len || remaining > total_len - offset) {
    return 0;
  }
  ssize_t n = tls13_io_read_fd(c->fd, buf + offset, remaining);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

bool TLS13_Handshake_ByteDriver_External_process_encrypted_handshake_record(
    TLS13_Handshake_ByteDriver_External_context ctx,
    uint8_t *header,
    size_t header_len,
    uint8_t *cipher,
    size_t cipher_len,
    void *progress,
    void *header_bytes,
    void *cipher_bytes) {
  (void)progress;
  (void)header_bytes;
  (void)cipher_bytes;
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  if (!handshake_can_continue(c) ||
      header == NULL ||
      header_len != TLS13_WIRE_RECORD_HEADER_LEN ||
      cipher == NULL) {
    return false;
  }
  return process_encrypted_handshake_record(c, header, cipher, cipher_len);
}

bool TLS13_Handshake_ByteDriver_External_pending_handshake_message_complete(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *progress) {
  (void)progress;
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  return c != NULL &&
         TLS13_Handshake_FlightState_pending_handshake_message_complete(
             c->server_handshake_flight_state);
}

uint8_t TLS13_Handshake_ByteDriver_External_pending_handshake_message_type(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *progress) {
  (void)progress;
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  if (c == NULL) {
    return 0;
  }
  return TLS13_Handshake_FlightState_pending_handshake_message_type(
      c->server_handshake_flight_state);
}

bool TLS13_Handshake_ByteDriver_External_accept_encrypted_extensions(
    TLS13_Handshake_ByteDriver_External_context ctx) {
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  if (c == NULL ||
      !TLS13_Handshake_FlightState_accept_pending_encrypted_extensions(
          c->server_handshake_flight_state)) {
    fprintf(stderr, "decrypted first OpenSSL handshake message is not EncryptedExtensions\n");
    return false;
  }
  return true;
}

bool TLS13_Handshake_ByteDriver_External_accept_certificate(
    TLS13_Handshake_ByteDriver_External_context ctx) {
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  if (c == NULL ||
      !TLS13_Handshake_FlightState_accept_pending_certificate(
          c->server_handshake_flight_state)) {
    fprintf(stderr, "failed to parse server Certificate\n");
    return false;
  }
  return true;
}

bool TLS13_Handshake_ByteDriver_External_accept_certificate_verify(
    TLS13_Handshake_ByteDriver_External_context ctx) {
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  if (c == NULL ||
      !TLS13_Handshake_FlightState_accept_pending_certificate_verify(
          c->server_handshake_flight_state)) {
    fprintf(stderr, "failed to parse server CertificateVerify\n");
    return false;
  }
  return true;
}

bool TLS13_Handshake_ByteDriver_External_accept_finished(
    TLS13_Handshake_ByteDriver_External_context ctx) {
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  if (c == NULL ||
      !TLS13_Handshake_FlightState_accept_pending_finished(
          c->server_handshake_flight_state)) {
    fprintf(stderr, "OpenSSL Finished has unexpected length\n");
    return false;
  }
  return true;
}

bool TLS13_Handshake_ByteDriver_External_encrypted_handshake_complete(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *progress) {
  (void)progress;
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  return c != NULL &&
         TLS13_Handshake_FlightState_encrypted_handshake_complete(
             c->server_handshake_flight_state);
}
