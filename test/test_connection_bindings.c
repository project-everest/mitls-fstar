#include "TLS13_Connection.h"
#include "tls13_connection_external_layer.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct TLS13_Connection_External_connection_s {
  bool connect_ok;
  bool write_all_ok;
  bool read_exact_ok;
  bool close_ok;
  size_t write_result;
  size_t read_result;
  unsigned new_calls;
  unsigned connect_calls;
  unsigned write_calls;
  unsigned write_all_calls;
  unsigned read_calls;
  unsigned read_exact_calls;
  unsigned close_calls;
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
    c->write_all_ok = true;
    c->read_exact_ok = true;
    c->close_ok = true;
    c->read_result = 1;
    c->new_calls = 1;
  }
  return c;
}

void TLS13_Connection_External_client_free(TLS13_Connection_External_connection c) {
  free(c);
}

bool TLS13_Connection_External_client_connect(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch) {
  (void)ch;
  c->connect_calls++;
  return c->connect_ok;
}

size_t TLS13_Connection_External_client_write(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *bytes) {
  (void)ch;
  (void)buf;
  (void)bytes;
  c->write_calls++;
  return c->write_result == 0 ? len : c->write_result;
}

bool TLS13_Connection_External_client_write_all(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *bytes) {
  (void)ch;
  (void)buf;
  (void)len;
  (void)bytes;
  c->write_all_calls++;
  return c->write_all_ok;
}

size_t TLS13_Connection_External_client_read(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t max_len,
    void *old_bytes) {
  (void)ch;
  (void)old_bytes;
  c->read_calls++;
  if (max_len != 0) {
    out[0] = 0xa5;
  }
  return c->read_result;
}

bool TLS13_Connection_External_client_read_exact(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t len,
    void *old_bytes) {
  (void)ch;
  (void)old_bytes;
  c->read_exact_calls++;
  memset(out, 0x5a, len);
  return c->read_exact_ok;
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
  TLS13_Connection_External_connection c =
      TLS13_Connection_client_new(hostname, sizeof hostname - 1, NULL);
  TLS13_IO_channel ch = (TLS13_IO_channel)c;
  if (c == NULL) {
    return 1;
  }

  bool ok =
      TLS13_Connection_client_connect(c, ch) &&
      TLS13_Connection_client_write_all(c, ch, buf, sizeof buf) &&
      TLS13_Connection_client_read_exact(c, ch, out, sizeof out);
  TLS13_Connection_client_close(c, ch);

  int failed =
      !ok ||
      c->new_calls != 1 ||
      c->connect_calls != 1 ||
      c->write_all_calls != 1 ||
      c->read_exact_calls != 1 ||
      c->close_calls != 1 ||
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
  TLS13_Connection_External_connection c =
      TLS13_Connection_client_new(hostname, sizeof hostname - 1, NULL);
  TLS13_IO_channel ch = (TLS13_IO_channel)c;
  if (c == NULL) {
    return 1;
  }
  c->connect_ok = false;
  bool ok = TLS13_Connection_client_connect(c, ch);
  int failed = ok || c->connect_calls != 1;
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
