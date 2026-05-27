#include "TLS13_Connection_Driver.h"

#include <stdio.h>
#include <string.h>

struct TLS13_Connection_connection_s {
  bool connect_ok;
  bool write_ok;
  bool read_ok;
  unsigned connect_calls;
  unsigned write_calls;
  unsigned read_calls;
  const uint8_t *last_write;
  size_t last_write_len;
  const uint8_t *read_src;
  size_t read_src_len;
};

struct TLS13_IO_channel_s {
  int unused;
};

bool TLS13_Connection_client_connect(
    TLS13_Connection_connection c,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state,
    void *erased_log_ref,
    void *erased_raw,
    void *erased_app_log) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_log_ref;
  (void)erased_raw;
  (void)erased_app_log;
  c->connect_calls++;
  return c->connect_ok;
}

bool TLS13_Connection_client_write_all(
    TLS13_Connection_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *erased_bytes,
    void *erased_state_ref,
    void *erased_state,
    void *erased_log_ref,
    void *erased_raw,
    void *erased_app_log) {
  (void)ch;
  (void)erased_bytes;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_log_ref;
  (void)erased_raw;
  (void)erased_app_log;
  c->write_calls++;
  c->last_write = buf;
  c->last_write_len = len;
  return c->write_ok;
}

bool TLS13_Connection_client_read_exact(
    TLS13_Connection_connection c,
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t len,
    void *erased_old_bytes,
    void *erased_state_ref,
    void *erased_state,
    void *erased_log_ref,
    void *erased_raw,
    void *erased_app_log) {
  (void)ch;
  (void)erased_old_bytes;
  (void)erased_state_ref;
  (void)erased_state;
  (void)erased_log_ref;
  (void)erased_raw;
  (void)erased_app_log;
  c->read_calls++;
  if (!c->read_ok || c->read_src_len != len) {
    return false;
  }
  memcpy(out, c->read_src, len);
  return true;
}

static int expect_counts(
    const char *name,
    const struct TLS13_Connection_connection_s *c,
    unsigned connect_calls,
    unsigned write_calls,
    unsigned read_calls) {
  if (c->connect_calls != connect_calls ||
      c->write_calls != write_calls ||
      c->read_calls != read_calls) {
    fprintf(stderr,
            "%s call counts: got %u/%u/%u, expected %u/%u/%u\n",
            name,
            c->connect_calls,
            c->write_calls,
            c->read_calls,
            connect_calls,
            write_calls,
            read_calls);
    return 1;
  }
  return 0;
}

static int test_success_path(void) {
  static const uint8_t outbound[] = "verified outbound";
  static const uint8_t inbound_expected[] = "verified inbound";
  uint8_t inbound[sizeof inbound_expected];
  memset(inbound, 0, sizeof inbound);

  struct TLS13_Connection_connection_s c = {
      .connect_ok = true,
      .write_ok = true,
      .read_ok = true,
      .read_src = inbound_expected,
      .read_src_len = sizeof inbound_expected,
  };
  struct TLS13_IO_channel_s ch = {0};

  bool ok = TLS13_Connection_Driver_connect_write_read_exact(
      &c, &ch, (uint8_t *)outbound, sizeof outbound, inbound, sizeof inbound);
  if (!ok) {
    fprintf(stderr, "success path returned false\n");
    return 1;
  }
  if (expect_counts("success", &c, 1, 1, 1) != 0) {
    return 1;
  }
  if (c.last_write != outbound || c.last_write_len != sizeof outbound) {
    fprintf(stderr, "success path did not pass outbound buffer through\n");
    return 1;
  }
  if (memcmp(inbound, inbound_expected, sizeof inbound) != 0) {
    fprintf(stderr, "success path did not fill inbound buffer\n");
    return 1;
  }
  return 0;
}

static int test_connect_failure_short_circuits(void) {
  uint8_t outbound[] = "out";
  uint8_t inbound[4] = {0};
  struct TLS13_Connection_connection_s c = {
      .connect_ok = false,
      .write_ok = true,
      .read_ok = true,
  };
  struct TLS13_IO_channel_s ch = {0};

  bool ok = TLS13_Connection_Driver_connect_write_read_exact(
      &c, &ch, outbound, sizeof outbound, inbound, sizeof inbound);
  if (ok) {
    fprintf(stderr, "connect failure path returned true\n");
    return 1;
  }
  return expect_counts("connect failure", &c, 1, 0, 0);
}

static int test_write_failure_short_circuits(void) {
  uint8_t outbound[] = "out";
  uint8_t inbound[4] = {0};
  struct TLS13_Connection_connection_s c = {
      .connect_ok = true,
      .write_ok = false,
      .read_ok = true,
  };
  struct TLS13_IO_channel_s ch = {0};

  bool ok = TLS13_Connection_Driver_connect_write_read_exact(
      &c, &ch, outbound, sizeof outbound, inbound, sizeof inbound);
  if (ok) {
    fprintf(stderr, "write failure path returned true\n");
    return 1;
  }
  return expect_counts("write failure", &c, 1, 1, 0);
}

int main(void) {
  int failed = 0;
  failed |= test_success_path();
  failed |= test_connect_failure_short_circuits();
  failed |= test_write_failure_short_circuits();
  if (failed != 0) {
    return 1;
  }
  printf("connection driver binding test passed\n");
  return 0;
}
