#include "tls13_connection_backend.h"  /* For TLS13_IO_channel - must be first */
#include "TLS13_Connection.h"
#include "TLS13_Record.h"

#undef TLS13_Record_record_state_free
#undef TLS13_Record_install_application_keys_runtime
#undef TLS13_Record_seal_application_runtime

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum read_record_kind {
  READ_APPLICATION_DATA,
  READ_PADDED_APPLICATION_DATA,
  READ_CLOSE_NOTIFY,
  READ_UNEXPECTED_MESSAGE_ALERT,
  READ_BAD_RECORD_MAC_ALERT,
  READ_HANDSHAKE_FAILURE_ALERT,
  READ_DECODE_ERROR_ALERT,
  READ_DECRYPT_ERROR_ALERT,
  READ_PROTOCOL_VERSION_ALERT,
  READ_UNSUPPORTED_EXTENSION_ALERT,
  READ_CERTIFICATE_UNKNOWN_ALERT,
  READ_ILLEGAL_PARAMETER_ALERT,
};

struct TLS13_Connection_Backend_connection_s {
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
  uint8_t read_cipher[25];
  size_t read_cipher_len;
  bool read_cipher_ready;
  enum read_record_kind read_kind;
};

static size_t selected_read_cipher_len(
    const struct TLS13_Connection_Backend_connection_s *c) {
  if (c->read_kind == READ_PADDED_APPLICATION_DATA) {
    return 25;
  }
  return c->read_kind == READ_APPLICATION_DATA ? 23 : 19;
}

TLS13_Connection_Backend_connection TLS13_Connection_Backend_client_new(
    uint8_t *hostname,
    size_t hostname_len,
    TLS13_Connection_Backend_config cfg,
    void *hostname_bytes) {
  (void)hostname;
  (void)hostname_len;
  (void)cfg;
  (void)hostname_bytes;
  struct TLS13_Connection_Backend_connection_s *c = calloc(1, sizeof *c);
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

void TLS13_Connection_Backend_client_free(
    TLS13_Connection_Backend_connection c,
    void *raw) {
  (void)raw;
  if (c == NULL) {
    return;
  }
  TLS13_Record_record_state_free(c->read_record_state);
  free(c);
}

bool TLS13_Connection_Backend_connect(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    void *raw) {
  (void)ch;
  (void)raw;
  c->connect_calls++;
  return c->connect_ok;
}

size_t TLS13_Connection_Backend_write_raw(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *buf_bytes,
    void *raw) {
  (void)ch;
  (void)buf;
  (void)buf_bytes;
  (void)raw;
  if (!c->write_record_ok) {
    return 0;
  }
  if (remaining == 0 || offset > total_len || remaining > total_len - offset) {
    return 0;
  }
  c->write_record_calls++;
  return remaining > 4 ? 4 : remaining;
}

size_t TLS13_Connection_Backend_read_raw(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t total_len,
    size_t offset,
    size_t remaining,
    void *old_buf,
    void *raw) {
  (void)ch;
  (void)old_buf;
  (void)raw;
  if (!c->read_exact_ok) {
    return 0;
  }
  if (remaining == 0 || offset > total_len || remaining > total_len - offset) {
    return 0;
  }
  size_t chunk = remaining > 3 ? 3 : remaining;
  if (total_len == 5) {
    uint8_t header[] = {23, 3, 3, 0, (uint8_t)selected_read_cipher_len(c)};
    if (offset == 0) {
      c->read_cipher_ready = false;
    }
    c->read_header_calls++;
    memcpy(buf + offset, header + offset, chunk);
    return chunk;
  }
  if (total_len == selected_read_cipher_len(c)) {
    if (!c->read_cipher_ready) {
      c->read_cipher_len = selected_read_cipher_len(c);
      uint8_t header[] = {23, 3, 3, 0, (uint8_t)c->read_cipher_len};
      uint8_t app_plain[] = {0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 0x5a, 23};
      uint8_t padded_app_plain[] = {0x6b, 0x6b, 0x6b, 0x6b, 0x6b, 0x6b, 23, 0, 0};
      uint8_t close_notify_plain[] = {1, 0, 21};
      uint8_t alert_plain[] = {2, 50, 21};
      uint8_t *plain = app_plain;
      size_t plain_len = sizeof app_plain;
      if (c->read_kind == READ_PADDED_APPLICATION_DATA) {
        plain = padded_app_plain;
        plain_len = sizeof padded_app_plain;
      } else if (c->read_kind == READ_CLOSE_NOTIFY) {
        plain = close_notify_plain;
        plain_len = sizeof close_notify_plain;
      } else if (c->read_kind == READ_BAD_RECORD_MAC_ALERT) {
        alert_plain[1] = 20;
        plain = alert_plain;
        plain_len = sizeof alert_plain;
      } else if (c->read_kind == READ_UNEXPECTED_MESSAGE_ALERT) {
        alert_plain[1] = 10;
        plain = alert_plain;
        plain_len = sizeof alert_plain;
      } else if (c->read_kind == READ_HANDSHAKE_FAILURE_ALERT) {
        alert_plain[1] = 40;
        plain = alert_plain;
        plain_len = sizeof alert_plain;
      } else if (c->read_kind == READ_DECODE_ERROR_ALERT) {
        alert_plain[1] = 50;
        plain = alert_plain;
        plain_len = sizeof alert_plain;
      } else if (c->read_kind == READ_DECRYPT_ERROR_ALERT) {
        alert_plain[1] = 51;
        plain = alert_plain;
        plain_len = sizeof alert_plain;
      } else if (c->read_kind == READ_PROTOCOL_VERSION_ALERT) {
        alert_plain[1] = 70;
        plain = alert_plain;
        plain_len = sizeof alert_plain;
      } else if (c->read_kind == READ_UNSUPPORTED_EXTENSION_ALERT) {
        alert_plain[1] = 110;
        plain = alert_plain;
        plain_len = sizeof alert_plain;
      } else if (c->read_kind == READ_CERTIFICATE_UNKNOWN_ALERT) {
        alert_plain[1] = 46;
        plain = alert_plain;
        plain_len = sizeof alert_plain;
      } else if (c->read_kind == READ_ILLEGAL_PARAMETER_ALERT) {
        alert_plain[1] = 47;
        plain = alert_plain;
        plain_len = sizeof alert_plain;
      }
      c->read_cipher_ready = TLS13_Record_seal_application_runtime(
          c->read_record_state, header, sizeof header, plain, plain_len, c->read_cipher);
    }
    if (!c->read_cipher_ready) {
      return 0;
    }
    c->read_fragment_calls++;
    memcpy(buf + offset, c->read_cipher + offset, chunk);
    return chunk;
  }
  return 0;
}

bool TLS13_Connection_Backend_validate_certificate(
    TLS13_Connection_Backend_connection c,
    uint8_t *leaf_der,
    size_t leaf_der_capacity,
    size_t leaf_der_len,
    void *leaf_der_bytes,
    void *raw) {
  (void)c;
  (void)leaf_der;
  (void)leaf_der_capacity;
  (void)leaf_der_len;
  (void)leaf_der_bytes;
  (void)raw;
  return true;
}

bool TLS13_Connection_Backend_verify_certificate_signature(
    TLS13_Connection_Backend_connection c,
    uint8_t *certificate_verify_input,
    size_t certificate_verify_input_len,
    uint16_t signature_scheme,
    uint8_t *signature,
    size_t signature_capacity,
    size_t signature_len,
    void *input_bytes,
    void *signature_bytes,
    void *raw) {
  (void)c;
  (void)certificate_verify_input;
  (void)certificate_verify_input_len;
  (void)signature_scheme;
  (void)signature;
  (void)signature_capacity;
  (void)signature_len;
  (void)input_bytes;
  (void)signature_bytes;
  (void)raw;
  return true;
}

bool TLS13_Connection_Backend_close(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    void *raw) {
  (void)ch;
  (void)raw;
  c->close_calls++;
  return c->close_ok;
}

static TLS13_Connection_Backend_connection backend_of(connection c) {
  return c.backend;
}

static void mark_application_ready(connection c) {
  uint8_t client_key[32];
  uint8_t client_iv[12];
  uint8_t server_key[32];
  uint8_t server_iv[12];
  memset(client_key, 0x11, sizeof client_key);
  memset(client_iv, 0x22, sizeof client_iv);
  memset(server_key, 0x33, sizeof server_key);
  memset(server_iv, 0x44, sizeof server_iv);
  TLS13_Record_install_application_keys_runtime(
      c.client_application_record_state, client_key, client_iv);
  TLS13_Record_install_application_keys_runtime(
      c.server_application_record_state, server_key, server_iv);
  TLS13_Record_install_application_keys_runtime(
      backend_of(c)->read_record_state, server_key, server_iv);
  *c.application_keys_installed = true;
}

static connection new_mock_connection(void) {
  uint8_t hostname[] = "localhost";
  struct TLS13_Connection_Backend_config_s cfg = {
      .port = 443,
      .ca_pem_path = "unused",
  };
  return client_new(hostname, sizeof hostname - 1, &cfg);
}

static int test_success_path(void) {
  uint8_t buf[] = "hello";
  uint8_t out[sizeof buf] = {0};
  connection c = new_mock_connection();
  TLS13_Connection_Backend_connection backend = backend_of(c);
  TLS13_IO_channel ch = (TLS13_IO_channel)backend;
  if (backend == NULL) {
    return 1;
  }
  mark_application_ready(c);

  bool ok =
      client_write_all(c, ch, buf, sizeof buf) &&
      client_read_exact(c, ch, out, sizeof out);
  client_close(c, ch);

  int failed =
      !ok ||
      backend->new_calls != 1 ||
      backend->connect_calls != 0 ||
      backend->write_record_calls <= 1 ||
      backend->read_header_calls <= 1 ||
      backend->read_fragment_calls <= 1 ||
      backend->close_calls != 1 ||
      out[0] != 0x5a;
  client_free(c);
  if (failed) {
    fprintf(stderr, "connection wrapper success path failed\n");
    return 1;
  }
  return 0;
}

static int test_failure_return(void) {
  connection c = new_mock_connection();
  TLS13_Connection_Backend_connection backend = backend_of(c);
  TLS13_IO_channel ch = (TLS13_IO_channel)backend;
  if (backend == NULL) {
    return 1;
  }
  backend->connect_ok = false;
  bool ok = client_connect(c, ch);
  int failed = ok || backend->connect_calls != 1;
  client_free(c);
  if (failed) {
    fprintf(stderr, "connection wrapper failure path failed\n");
    return 1;
  }
  return 0;
}

static int test_close_notify_read_returns_zero(void) {
  uint8_t out[1] = {0};
  connection c = new_mock_connection();
  TLS13_Connection_Backend_connection backend = backend_of(c);
  TLS13_IO_channel ch = (TLS13_IO_channel)backend;
  if (backend == NULL) {
    return 1;
  }
  mark_application_ready(c);
  backend->read_kind = READ_CLOSE_NOTIFY;
  size_t n = client_read(c, ch, out, sizeof out);
  int failed =
      n != 0 ||
      backend->read_header_calls == 0 ||
      backend->read_fragment_calls == 0;
  client_free(c);
  if (failed) {
    fprintf(stderr, "connection wrapper close_notify read failed\n");
    return 1;
  }
  return 0;
}

static int test_alert_read_returns_zero(
    enum read_record_kind kind,
    const char *name) {
  uint8_t out[1] = {0};
  connection c = new_mock_connection();
  TLS13_Connection_Backend_connection backend = backend_of(c);
  TLS13_IO_channel ch = (TLS13_IO_channel)backend;
  if (backend == NULL) {
    return 1;
  }

  mark_application_ready(c);
  backend->read_kind = kind;
  size_t n = client_read(c, ch, out, sizeof out);
  int failed =
      n != 0 ||
      backend->read_header_calls == 0 ||
      backend->read_fragment_calls == 0;
  client_free(c);
  if (failed) {
    fprintf(stderr, "connection wrapper %s alert read failed\n", name);
    return 1;
  }
  return 0;
}

static int test_mapped_alert_reads_return_zero(void) {
  return
      test_alert_read_returns_zero(READ_UNEXPECTED_MESSAGE_ALERT, "unexpected_message") ||
      test_alert_read_returns_zero(READ_BAD_RECORD_MAC_ALERT, "bad_record_mac") ||
      test_alert_read_returns_zero(READ_HANDSHAKE_FAILURE_ALERT, "handshake_failure") ||
      test_alert_read_returns_zero(READ_DECODE_ERROR_ALERT, "decode_error") ||
      test_alert_read_returns_zero(READ_DECRYPT_ERROR_ALERT, "decrypt_error") ||
      test_alert_read_returns_zero(READ_PROTOCOL_VERSION_ALERT, "protocol_version") ||
      test_alert_read_returns_zero(READ_UNSUPPORTED_EXTENSION_ALERT, "unsupported_extension") ||
      test_alert_read_returns_zero(READ_CERTIFICATE_UNKNOWN_ALERT, "certificate_unknown") ||
      test_alert_read_returns_zero(READ_ILLEGAL_PARAMETER_ALERT, "illegal_parameter");
}

static int test_multi_record_read_exact(void) {
  uint8_t out[12] = {0};
  connection c = new_mock_connection();
  TLS13_Connection_Backend_connection backend = backend_of(c);
  TLS13_IO_channel ch = (TLS13_IO_channel)backend;
  if (backend == NULL) {
    return 1;
  }
  mark_application_ready(c);
  bool ok =
      client_read_exact(c, ch, out, sizeof out);
  int failed =
      !ok ||
      out[0] != 0x5a ||
      out[5] != 0x5a ||
      out[6] != 0x5a ||
      out[11] != 0x5a ||
      backend->read_header_calls < 4 ||
      backend->read_fragment_calls < 2;
  client_free(c);
  if (failed) {
    fprintf(stderr, "connection wrapper multi-record read_exact failed\n");
    return 1;
  }
  return 0;
}

static int test_padded_application_read(void) {
  uint8_t out[6] = {0};
  connection c = new_mock_connection();
  TLS13_Connection_Backend_connection backend = backend_of(c);
  TLS13_IO_channel ch = (TLS13_IO_channel)backend;
  if (backend == NULL) {
    return 1;
  }
  mark_application_ready(c);
  backend->read_kind = READ_PADDED_APPLICATION_DATA;
  bool ok = client_read_exact(c, ch, out, sizeof out);
  int failed =
      !ok ||
      out[0] != 0x6b ||
      out[5] != 0x6b;
  client_free(c);
  if (failed) {
    fprintf(stderr, "connection wrapper padded application read failed\n");
    return 1;
  }
  return 0;
}

static int test_buffered_application_reads(void) {
  uint8_t first[3] = {0};
  uint8_t second[3] = {0};
  connection c = new_mock_connection();
  TLS13_Connection_Backend_connection backend = backend_of(c);
  TLS13_IO_channel ch = (TLS13_IO_channel)backend;
  if (backend == NULL) {
    return 1;
  }
  mark_application_ready(c);
  bool ok =
      client_read_exact(c, ch, first, sizeof first) &&
      client_read_exact(c, ch, second, sizeof second);
  int failed =
      !ok ||
      first[0] != 0x5a ||
      second[0] != 0x5a ||
      backend->read_header_calls != 2;
  client_free(c);
  if (failed) {
    fprintf(stderr, "connection wrapper buffered reads failed\n");
    return 1;
  }
  return 0;
}

int main(void) {
  if (test_success_path() != 0 ||
      test_failure_return() != 0 ||
      test_close_notify_read_returns_zero() != 0 ||
      test_mapped_alert_reads_return_zero() != 0 ||
      test_padded_application_read() != 0 ||
      test_multi_record_read_exact() != 0 ||
      test_buffered_application_reads() != 0) {
    return 1;
  }
  printf("connection wrapper binding test passed\n");
  return 0;
}
