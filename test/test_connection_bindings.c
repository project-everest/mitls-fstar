#include "TLS13_Connection.h"
#include "tls13_connection_external_layer.h"

#undef TLS13_Record_record_state_free
#undef TLS13_Record_install_application_keys_runtime
#undef TLS13_Record_seal_application_runtime

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct TLS13_Connection_External_connection_s {
  bool connect_ok;
  bool write_record_ok;
  bool read_exact_ok;
  bool close_ok;
  unsigned new_calls;
  unsigned connect_calls;
  unsigned write_record_calls;
  unsigned read_header_calls;
  unsigned read_fragment_calls;
  unsigned close_calls;
  TLS13_Record_record_state read_record_state;
};

TLS13_Connection_External_connection TLS13_Connection_External_client_new(
    uint8_t *hostname,
    size_t hostname_len,
    TLS13_X509_Spec_trust_store trust_store,
    void *hostname_bytes) {
  (void)hostname;
  (void)hostname_len;
  (void)trust_store;
  (void)hostname_bytes;
  struct TLS13_Connection_External_connection_s *c = calloc(1, sizeof *c);
  if (c != NULL) {
    c->connect_ok = true;
    c->write_record_ok = true;
    c->read_exact_ok = true;
    c->close_ok = true;
    c->new_calls = 1;
    c->read_record_state = TLS13_Record_record_state_new();
  }
  return c;
}

void TLS13_Connection_External_client_free(TLS13_Connection_External_connection c) {
  if (c == NULL) {
    return;
  }
  TLS13_Record_record_state_free(c->read_record_state);
  free(c);
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
  (void)ch;
  (void)old_client_key;
  (void)old_client_iv;
  (void)old_server_key;
  (void)old_server_iv;
  c->connect_calls++;
  memset(client_key, 0x11, 32);
  memset(client_iv, 0x22, 12);
  memset(server_key, 0x33, 32);
  memset(server_iv, 0x44, 12);
  TLS13_Record_install_application_keys_runtime(c->read_record_state, server_key, server_iv);
  return c->connect_ok;
}

bool TLS13_Connection_External_client_write_raw_record(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *header,
    size_t header_len,
    uint8_t *cipher,
    size_t cipher_len,
    void *header_bytes,
    void *cipher_bytes) {
  (void)ch;
  (void)header;
  (void)header_len;
  (void)cipher;
  (void)cipher_len;
  (void)header_bytes;
  (void)cipher_bytes;
  c->write_record_calls++;
  return c->write_record_ok;
}

bool TLS13_Connection_External_client_read_raw_record_header(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *header,
    size_t header_len,
    void *old_header) {
  (void)ch;
  (void)old_header;
  if (!c->read_exact_ok) {
    return false;
  }
  c->read_header_calls++;
  memset(header, 0, header_len);
  header[0] = 23;
  header[1] = 3;
  header[2] = 3;
  header[3] = 0;
  header[4] = 23;
  return true;
}

bool TLS13_Connection_External_client_read_raw_record_fragment(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *cipher,
    size_t cipher_len,
    void *old_cipher) {
  (void)ch;
  (void)old_cipher;
  if (!c->read_exact_ok) {
    return false;
  }
  c->read_fragment_calls++;
  if (cipher_len != 23) {
    return false;
  }
  uint8_t header[] = {23, 3, 3, 0, 23};
  uint8_t plain[] = {0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 23};
  return TLS13_Record_seal_application_runtime(
      c->read_record_state, header, sizeof header, plain, sizeof plain, cipher);
}

bool TLS13_Connection_External_client_close(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch) {
  (void)ch;
  c->close_calls++;
  return c->close_ok;
}

static int test_success_path(void) {
  uint8_t hostname[] = "localhost";
  uint8_t buf[] = "hello";
  uint8_t out[sizeof buf] = {0};
  TLS13_Connection_connection c =
      TLS13_Connection_client_new(hostname, sizeof hostname - 1, NULL);
  TLS13_IO_channel ch = (TLS13_IO_channel)c.backend;
  if (c.backend == NULL) {
    return 1;
  }

  bool ok =
      TLS13_Connection_client_connect(c, ch) &&
      TLS13_Connection_client_write_all(c, ch, buf, sizeof buf) &&
      TLS13_Connection_client_read_exact(c, ch, out, sizeof out);
  TLS13_Connection_client_close(c, ch);

  int failed =
      !ok ||
      c.backend->new_calls != 1 ||
      c.backend->connect_calls != 1 ||
      c.backend->write_record_calls != 1 ||
      c.backend->read_header_calls == 0 ||
      c.backend->read_fragment_calls == 0 ||
      c.backend->close_calls != 1 ||
      out[0] != 0x5a;
  TLS13_Connection_client_free(c);
  if (failed) {
    fprintf(stderr, "connection wrapper success path failed\n");
    return 1;
  }
  return 0;
}

static int test_failure_return(void) {
  uint8_t hostname[] = "localhost";
  TLS13_Connection_connection c =
      TLS13_Connection_client_new(hostname, sizeof hostname - 1, NULL);
  TLS13_IO_channel ch = (TLS13_IO_channel)c.backend;
  if (c.backend == NULL) {
    return 1;
  }
  c.backend->connect_ok = false;
  bool ok = TLS13_Connection_client_connect(c, ch);
  int failed = ok || c.backend->connect_calls != 1;
  TLS13_Connection_client_free(c);
  if (failed) {
    fprintf(stderr, "connection wrapper failure path failed\n");
    return 1;
  }
  return 0;
}

int main(void) {
  if (test_success_path() != 0 || test_failure_return() != 0) {
    return 1;
  }
  printf("connection wrapper binding test passed\n");
  return 0;
}
