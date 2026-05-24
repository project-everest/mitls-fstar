#include "tls13_connection_external_layer.h"
#include "tls13_hacl_stubs.h"
#include "tls13_handshake_external_layer.h"
#include "tls13_io_stubs.h"
#include "tls13_openssl_stubs.h"

#include "TLS13_KeySchedule.h"
#include "TLS13_Handshake_Framing.h"
#include "TLS13_Handshake_FlightState.h"
#include "TLS13_Handshake_Transcript.h"
#include "TLS13_Handshake_ByteDriver.h"
#include "TLS13_Record_Framing.h"
#include "TLS13_Record.h"
#include "tls13_connection_external_layer.h"

#undef TLS13_Record_Framing_decode_inner_plaintext_no_padding
#undef TLS13_Record_Framing_serialize_application_data_header
#undef TLS13_Record_Framing_parse_record_header

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

static int read_exact_fd(int fd, uint8_t *buf, size_t len) {
  size_t off = 0;
  while (off < len) {
    ssize_t n = tls13_io_read_fd(fd, buf + off, len - off);
    if (n <= 0) {
      return -1;
    }
    off += (size_t)n;
  }
  return 0;
}

static int read_record(
    int fd,
    uint8_t header[TLS13_WIRE_RECORD_HEADER_LEN],
    uint8_t *fragment,
    size_t fragment_capacity,
    uint8_t *content_type,
    uint16_t *legacy_version,
    uint16_t *fragment_len) {
  if (read_exact_fd(fd, header, TLS13_WIRE_RECORD_HEADER_LEN) != 0) {
    return -1;
  }
  uint8_t content_type_buf[1] = {0};
  uint8_t fragment_len_buf[2] = {0};
  if (!TLS13_Record_Framing_parse_record_header(
          header,
          TLS13_WIRE_RECORD_HEADER_LEN,
          content_type_buf,
          sizeof content_type_buf,
          fragment_len_buf,
          sizeof fragment_len_buf)) {
    return -1;
  }
  *content_type = content_type_buf[0];
  *legacy_version = 0x0303;
  *fragment_len = ((uint16_t)fragment_len_buf[0] << 8) | fragment_len_buf[1];
  if (*fragment_len > fragment_capacity) {
    return -1;
  }
  return read_exact_fd(fd, fragment, *fragment_len);
}

static int derive_server_handshake_keys(
    const uint8_t *client_hello,
    size_t client_hello_len,
    const uint8_t *server_hello,
    size_t server_hello_len,
    const uint8_t server_key_share[32],
    uint8_t handshake_secret[32],
    uint8_t client_handshake_traffic_secret[32],
    uint8_t server_handshake_traffic_secret[32],
    uint8_t client_key[32],
    uint8_t client_iv[12],
    uint8_t server_key[32],
    uint8_t server_iv[12]) {
  static const uint8_t client_private_key[32] = {
      0x49, 0xaf, 0x42, 0xba, 0x7f, 0x79, 0x94, 0x85,
      0x2d, 0x71, 0x3e, 0xf2, 0x78, 0x4b, 0xcb, 0xca,
      0xa7, 0x91, 0x1d, 0xe2, 0x6a, 0xdc, 0x56, 0x42,
      0xcb, 0x63, 0x45, 0x40, 0xe7, 0xea, 0x50, 0x05};
  static const uint8_t zero_secret[32] = {0};

  uint8_t early_secret[32];
  uint8_t shared_secret[32];
  uint8_t transcript_hash[32];

  if (!tls13_hacl_hkdf_extract_sha256(
          early_secret, NULL, 0, zero_secret, sizeof zero_secret) ||
      !tls13_hacl_x25519_shared(shared_secret, client_private_key, server_key_share)) {
    return -1;
  }

  if (!TLS13_Handshake_Transcript_hash_client_server_hello(
          (uint8_t *)client_hello,
          client_hello_len,
          (uint8_t *)server_hello,
          server_hello_len,
          transcript_hash)) {
    return -1;
  }

  TLS13_KeySchedule_handshake_secret(
      early_secret, shared_secret, sizeof shared_secret, handshake_secret);
  TLS13_KeySchedule_client_handshake_traffic_secret(
      handshake_secret, transcript_hash, client_handshake_traffic_secret);
  TLS13_KeySchedule_server_handshake_traffic_secret(
      handshake_secret, transcript_hash, server_handshake_traffic_secret);
  TLS13_KeySchedule_derive_traffic_key(
      client_handshake_traffic_secret, client_key);
  TLS13_KeySchedule_derive_traffic_iv(
      client_handshake_traffic_secret, client_iv);
  TLS13_KeySchedule_derive_traffic_key(
      server_handshake_traffic_secret, server_key);
  TLS13_KeySchedule_derive_traffic_iv(
      server_handshake_traffic_secret, server_iv);
  return 0;
}

static int compute_transcript_hash(
    const uint8_t *client_hello,
    size_t client_hello_len,
    const uint8_t *server_hello,
    size_t server_hello_len,
    const uint8_t *server_handshake_messages,
    size_t server_handshake_len,
    uint8_t transcript_hash[32]) {
  return TLS13_Handshake_Transcript_hash_client_server_handshake(
             (uint8_t *)client_hello,
             client_hello_len,
             (uint8_t *)server_hello,
             server_hello_len,
             (uint8_t *)server_handshake_messages,
             server_handshake_len,
             transcript_hash)
             ? 0
             : -1;
}

static int verify_server_finished(
    const uint8_t *client_hello,
    size_t client_hello_len,
    const uint8_t *server_hello,
    size_t server_hello_len,
    const uint8_t *server_handshake_messages,
    size_t server_handshake_before_finished_len,
    const uint8_t finished_verify_data[32],
    const uint8_t server_handshake_traffic_secret[32]) {
  uint8_t transcript_hash[32];
  uint8_t expected[32];

  if (compute_transcript_hash(
          client_hello,
          client_hello_len,
          server_hello,
          server_hello_len,
          server_handshake_messages,
          server_handshake_before_finished_len,
          transcript_hash) != 0) {
    return -1;
  }
  TLS13_KeySchedule_finished_verify_data(
      (uint8_t *)server_handshake_traffic_secret, transcript_hash, expected);
  return TLS13_Handshake_Transcript_equal32(expected, (uint8_t *)finished_verify_data) ? 0 : -1;
}

static int derive_application_keys(
    const uint8_t handshake_secret[32],
    const uint8_t transcript_hash[32],
    uint8_t client_key[32],
    uint8_t client_iv[12],
    uint8_t server_key[32],
    uint8_t server_iv[12]) {
  uint8_t master_secret[32];
  uint8_t client_application_traffic_secret[32];
  uint8_t server_application_traffic_secret[32];

  TLS13_KeySchedule_master_secret((uint8_t *)handshake_secret, master_secret);
  TLS13_KeySchedule_client_application_traffic_secret(
      master_secret, (uint8_t *)transcript_hash, client_application_traffic_secret);
  TLS13_KeySchedule_server_application_traffic_secret(
      master_secret, (uint8_t *)transcript_hash, server_application_traffic_secret);
  TLS13_KeySchedule_derive_traffic_key(client_application_traffic_secret, client_key);
  TLS13_KeySchedule_derive_traffic_iv(client_application_traffic_secret, client_iv);
  TLS13_KeySchedule_derive_traffic_key(server_application_traffic_secret, server_key);
  TLS13_KeySchedule_derive_traffic_iv(server_application_traffic_secret, server_iv);
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

static bool copy_hello_messages(
    TLS13_Connection_connection c,
    uint8_t client_hello[PROBE_CLIENT_HELLO_CAPACITY],
    size_t *client_hello_len,
    uint8_t server_hello[PROBE_SERVER_HELLO_CAPACITY],
    size_t *server_hello_len) {
  if (c == NULL || client_hello == NULL || client_hello_len == NULL ||
      server_hello == NULL || server_hello_len == NULL) {
    return false;
  }
  *client_hello_len =
      TLS13_Handshake_FlightState_client_hello_len(c->server_handshake_flight_state);
  *server_hello_len =
      TLS13_Handshake_FlightState_server_hello_len(c->server_handshake_flight_state);
  if (*client_hello_len > PROBE_CLIENT_HELLO_CAPACITY ||
      *server_hello_len > PROBE_SERVER_HELLO_CAPACITY) {
    return false;
  }
  TLS13_Handshake_FlightState_copy_client_hello(
      c->server_handshake_flight_state,
      client_hello,
      PROBE_CLIENT_HELLO_CAPACITY);
  TLS13_Handshake_FlightState_copy_server_hello(
      c->server_handshake_flight_state,
      server_hello,
      PROBE_SERVER_HELLO_CAPACITY);
  return true;
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

static bool read_next_encrypted_handshake_record(TLS13_Connection_connection c) {
  uint8_t encrypted_header[TLS13_WIRE_RECORD_HEADER_LEN];
  uint8_t encrypted_fragment[20000];
  uint8_t content_type = 0;
  uint16_t legacy_version = 0;
  uint16_t fragment_len = 0;
  if (read_record(
          c->fd,
          encrypted_header,
          encrypted_fragment,
          sizeof encrypted_fragment,
          &content_type,
          &legacy_version,
          &fragment_len) != 0) {
    fprintf(stderr, "failed to read encrypted handshake record\n");
    return false;
  }
  if (content_type == 20 && fragment_len == 1 && encrypted_fragment[0] == 1) {
    return true;
  }
  if (content_type != 23 || fragment_len < 16) {
    fprintf(stderr, "unexpected record before server Finished: %u\n", content_type);
    return false;
  }

  size_t inner_plaintext_len = (size_t)fragment_len - 16u;
  uint8_t inner_plaintext[inner_plaintext_len];
  if (!TLS13_Handshake_FlightState_open_server_handshake_record(
          c->server_handshake_flight_state,
          encrypted_header,
          TLS13_WIRE_RECORD_HEADER_LEN,
          encrypted_fragment,
          fragment_len,
          inner_plaintext)) {
    fprintf(stderr, "failed to decrypt OpenSSL encrypted handshake record\n");
    return false;
  }

  uint8_t inner_content_type_buf[1] = {0};
  if (inner_plaintext_len == 0) {
    fprintf(stderr, "failed to decode OpenSSL handshake inner plaintext\n");
    return false;
  }
  size_t handshake_plaintext_len =
      TLS13_Record_Framing_decode_inner_plaintext_no_padding(
          inner_plaintext,
          inner_plaintext_len,
          inner_content_type_buf,
          sizeof inner_content_type_buf);
  uint8_t inner_content_type = inner_content_type_buf[0];
  size_t server_handshake_len =
      TLS13_Handshake_FlightState_handshake_len(c->server_handshake_flight_state);
  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!copy_server_handshake_messages(c, server_handshake_messages)) {
    fprintf(stderr, "failed to copy OpenSSL handshake messages\n");
    return false;
  }
  if (inner_content_type != 22 ||
      handshake_plaintext_len > sizeof server_handshake_messages - server_handshake_len ||
      !TLS13_Handshake_FlightState_append_handshake_len(
          c->server_handshake_flight_state,
          handshake_plaintext_len,
          sizeof server_handshake_messages)) {
    fprintf(stderr, "failed to decode OpenSSL handshake inner plaintext\n");
    return false;
  }
  memcpy(
      server_handshake_messages + server_handshake_len,
      inner_plaintext,
      handshake_plaintext_len);
  TLS13_Handshake_FlightState_set_server_handshake(
      c->server_handshake_flight_state,
      server_handshake_messages,
      sizeof server_handshake_messages);
  return true;
}

static bool pending_handshake_metadata(
    TLS13_Connection_connection c,
    uint8_t *handshake_type,
    uint32_t *handshake_body_len,
    size_t *message_len) {
  if (c == NULL) {
    return false;
  }
  size_t server_handshake_len =
      TLS13_Handshake_FlightState_handshake_len(c->server_handshake_flight_state);
  size_t parsed_handshake_len =
      TLS13_Handshake_FlightState_parsed_len(c->server_handshake_flight_state);
  if (server_handshake_len - parsed_handshake_len < TLS13_WIRE_HANDSHAKE_HEADER_LEN) {
    return false;
  }

  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!copy_server_handshake_messages(c, server_handshake_messages)) {
    return false;
  }
  uint8_t handshake_type_buf[1] = {0};
  uint8_t handshake_body_len_buf[3] = {0};
  if (!TLS13_Handshake_Framing_parse_handshake_header(
          server_handshake_messages + parsed_handshake_len,
          server_handshake_len - parsed_handshake_len,
          handshake_type_buf,
          sizeof handshake_type_buf,
          handshake_body_len_buf,
          sizeof handshake_body_len_buf)) {
    return false;
  }
  *handshake_type = handshake_type_buf[0];
  *handshake_body_len =
        ((uint32_t)handshake_body_len_buf[0] << 16) |
        ((uint32_t)handshake_body_len_buf[1] << 8) |
        (uint32_t)handshake_body_len_buf[2];
  *message_len = TLS13_WIRE_HANDSHAKE_HEADER_LEN + (size_t)*handshake_body_len;
  return *message_len <= server_handshake_len - parsed_handshake_len;
}

static bool pending_handshake_body(
    TLS13_Connection_connection c,
    uint8_t expected_type,
    uint8_t messages[PROBE_SERVER_HANDSHAKE_CAPACITY],
    const uint8_t **body,
    uint32_t *body_len,
    size_t *message_len) {
  uint8_t handshake_type = 0;
  if (!pending_handshake_metadata(c, &handshake_type, body_len, message_len) ||
      handshake_type != expected_type) {
    return false;
  }
  size_t parsed_handshake_len =
      TLS13_Handshake_FlightState_parsed_len(c->server_handshake_flight_state);
  if (!copy_server_handshake_messages(c, messages)) {
    return false;
  }
  *body = messages +
          parsed_handshake_len +
          TLS13_WIRE_HANDSHAKE_HEADER_LEN;
  return true;
}

static void probe_handshake_send_client_hello(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (c == NULL || c->fd >= 0) {
    fail_handshake(c);
    return;
  }

  static const uint8_t random[32] = {
      0xcb, 0x34, 0xec, 0xb1, 0xe7, 0x81, 0x63, 0xba,
      0x1c, 0x38, 0xc6, 0xda, 0xcb, 0x19, 0x6a, 0x6d,
      0xff, 0xa2, 0x1a, 0x8d, 0x99, 0x12, 0xec, 0x18,
      0xa2, 0xef, 0x62, 0x83, 0x02, 0x4d, 0xec, 0xe7};
  static const uint8_t key_share[32] = {
      0x99, 0x38, 0x1d, 0xe5, 0x60, 0xe4, 0xbd, 0x43,
      0xd2, 0x3d, 0x8e, 0x43, 0x5a, 0x7d, 0xba, 0xfe,
      0xb3, 0xc0, 0x6e, 0x51, 0xc1, 0x3c, 0xae, 0x4d,
      0x54, 0x13, 0x69, 0x1e, 0x52, 0x9a, 0xaf, 0x2c};

  uint8_t client_hello[PROBE_CLIENT_HELLO_CAPACITY];
  size_t client_hello_len = 130u;
  if (!TLS13_Handshake_Framing_build_supported_client_hello_localhost(
          (uint8_t *)random,
          (uint8_t *)key_share,
          client_hello,
          sizeof client_hello)) {
    fprintf(stderr, "failed to serialize ClientHello\n");
    fail_handshake(c);
    return;
  }
  TLS13_Handshake_FlightState_set_client_hello(
      c->server_handshake_flight_state,
      client_hello,
      sizeof client_hello,
      client_hello_len);

  uint8_t record[TLS13_WIRE_RECORD_HEADER_LEN + PROBE_CLIENT_HELLO_CAPACITY];
  TLS13_Handshake_Framing_serialize_client_hello_record_header(
      record, TLS13_WIRE_RECORD_HEADER_LEN);
  memcpy(record + TLS13_WIRE_RECORD_HEADER_LEN, client_hello, client_hello_len);
  size_t record_len = TLS13_WIRE_RECORD_HEADER_LEN + client_hello_len;

  c->fd = tls13_io_connect_tcp(c->host, c->port);
  if (c->fd < 0) {
    perror("connect");
    fail_handshake(c);
    return;
  }
  if (write_all_fd(c->fd, record, record_len) != 0) {
    perror("write ClientHello");
    fail_handshake(c);
  }
}

static bool probe_handshake_recv_server_hello(
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

  uint8_t header[TLS13_WIRE_RECORD_HEADER_LEN];
  uint8_t content_type = 0;
  uint16_t legacy_version = 0;
  uint16_t fragment_len = 0;
  uint8_t client_hello[PROBE_CLIENT_HELLO_CAPACITY];
  uint8_t server_hello_fragment[PROBE_SERVER_HELLO_CAPACITY];
  size_t client_hello_len = 0;
  size_t server_hello_len = 0;
  uint8_t server_random[32];
  uint8_t server_key_share[32];
  if (read_record(
          c->fd,
          header,
          server_hello_fragment,
          sizeof server_hello_fragment,
          &content_type,
          &legacy_version,
          &fragment_len) != 0 ||
      content_type != 22) {
    fprintf(stderr, "bad ServerHello record header\n");
    fail_handshake(c);
    return false;
  }
  if (!TLS13_Handshake_Framing_parse_supported_server_hello(
          server_hello_fragment,
          fragment_len,
          server_random,
          sizeof server_random,
          server_key_share,
          sizeof server_key_share)) {
    fprintf(stderr, "failed to parse supported OpenSSL ServerHello\n");
    fail_handshake(c);
    return false;
  }
  TLS13_Handshake_FlightState_set_server_hello(
      c->server_handshake_flight_state,
      server_hello_fragment,
      sizeof server_hello_fragment,
      fragment_len);
  if (!copy_hello_messages(
          c,
          client_hello,
          &client_hello_len,
          server_hello_fragment,
          &server_hello_len)) {
    fprintf(stderr, "failed to copy hello transcript bytes\n");
    fail_handshake(c);
    return false;
  }
  uint8_t handshake_secret[32];
  uint8_t client_handshake_traffic_secret[32];
  uint8_t client_handshake_key[32];
  uint8_t client_handshake_iv[12];
  uint8_t server_handshake_traffic_secret[32];
  uint8_t server_handshake_key[32];
  uint8_t server_handshake_iv[12];
  if (derive_server_handshake_keys(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_key_share,
          handshake_secret,
          client_handshake_traffic_secret,
          server_handshake_traffic_secret,
          client_handshake_key,
          client_handshake_iv,
          server_handshake_key,
          server_handshake_iv) != 0) {
    fprintf(stderr, "failed to derive handshake traffic keys\n");
    fail_handshake(c);
    return false;
  }
  TLS13_Handshake_FlightState_set_handshake_secret(
      c->server_handshake_flight_state, handshake_secret, sizeof handshake_secret);
  TLS13_Handshake_FlightState_set_client_handshake_traffic_secret(
      c->server_handshake_flight_state,
      client_handshake_traffic_secret,
      sizeof client_handshake_traffic_secret);
  TLS13_Handshake_FlightState_set_client_handshake_key_iv(
      c->server_handshake_flight_state,
      client_handshake_key,
      sizeof client_handshake_key,
      client_handshake_iv,
      sizeof client_handshake_iv);
  TLS13_Handshake_FlightState_set_server_handshake_traffic_secret(
      c->server_handshake_flight_state,
      server_handshake_traffic_secret,
      sizeof server_handshake_traffic_secret);
  TLS13_Handshake_FlightState_set_server_handshake_key_iv(
      c->server_handshake_flight_state,
      server_handshake_key,
      sizeof server_handshake_key,
      server_handshake_iv,
      sizeof server_handshake_iv);
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
  uint8_t transcript_hash[32];
  uint8_t certificate_verify_input[TLS13_WIRE_CERTIFICATE_VERIFY_INPUT_LEN];
  uint8_t client_hello[PROBE_CLIENT_HELLO_CAPACITY];
  uint8_t server_hello_fragment[PROBE_SERVER_HELLO_CAPACITY];
  size_t client_hello_len = 0;
  size_t server_hello_len = 0;
  if (!copy_hello_messages(
          c,
          client_hello,
          &client_hello_len,
          server_hello_fragment,
          &server_hello_len)) {
    fprintf(stderr, "failed to copy hello transcript bytes\n");
    tls13_openssl_peer_identity_free(peer);
    fail_handshake(c);
    return false;
  }
  if (compute_transcript_hash(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_handshake_messages,
          TLS13_Handshake_FlightState_certificate_verify_offset(c->server_handshake_flight_state),
          transcript_hash) != 0) {
    fprintf(stderr, "failed to build CertificateVerify input\n");
    tls13_openssl_peer_identity_free(peer);
    fail_handshake(c);
    return false;
  }
  TLS13_Handshake_Framing_build_server_certificate_verify_input(
      transcript_hash,
      certificate_verify_input,
      sizeof certificate_verify_input);
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
  uint8_t server_finished_verify_data[32] = {0};
  uint8_t server_handshake_traffic_secret[32] = {0};
  uint8_t client_hello[PROBE_CLIENT_HELLO_CAPACITY];
  uint8_t server_hello_fragment[PROBE_SERVER_HELLO_CAPACITY];
  size_t client_hello_len = 0;
  size_t server_hello_len = 0;
  if (!copy_hello_messages(
          c,
          client_hello,
          &client_hello_len,
          server_hello_fragment,
          &server_hello_len)) {
    fprintf(stderr, "failed to copy hello transcript bytes\n");
    fail_handshake(c);
    return false;
  }
  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!copy_server_handshake_messages(c, server_handshake_messages)) {
    fprintf(stderr, "failed to copy server handshake transcript bytes\n");
    fail_handshake(c);
    return false;
  }
  TLS13_Handshake_FlightState_copy_server_finished_verify_data(
      c->server_handshake_flight_state,
      server_finished_verify_data,
      sizeof server_finished_verify_data);
  TLS13_Handshake_FlightState_copy_server_handshake_traffic_secret(
      c->server_handshake_flight_state,
      server_handshake_traffic_secret,
      sizeof server_handshake_traffic_secret);
  if (verify_server_finished(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_handshake_messages,
          TLS13_Handshake_FlightState_server_before_finished_len(c->server_handshake_flight_state),
          server_finished_verify_data,
          server_handshake_traffic_secret) != 0) {
    fprintf(stderr, "failed to verify OpenSSL server Finished\n");
    fail_handshake(c);
    return false;
  }
  return true;
}

static bool probe_handshake_send_client_finished(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) || c->fd < 0) {
    fail_handshake(c);
    return false;
  }

  uint8_t transcript_hash_through_server_finished[32];
  uint8_t client_hello[PROBE_CLIENT_HELLO_CAPACITY];
  uint8_t server_hello_fragment[PROBE_SERVER_HELLO_CAPACITY];
  size_t client_hello_len = 0;
  size_t server_hello_len = 0;
  if (!copy_hello_messages(
          c,
          client_hello,
          &client_hello_len,
          server_hello_fragment,
          &server_hello_len)) {
    fprintf(stderr, "failed to copy hello transcript bytes\n");
    fail_handshake(c);
    return false;
  }
  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!copy_server_handshake_messages(c, server_handshake_messages)) {
    fprintf(stderr, "failed to copy server handshake transcript bytes\n");
    fail_handshake(c);
    return false;
  }
  if (compute_transcript_hash(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_handshake_messages,
          TLS13_Handshake_FlightState_server_through_finished_len(c->server_handshake_flight_state),
          transcript_hash_through_server_finished) != 0) {
    fprintf(stderr, "failed to hash transcript through server Finished\n");
    fail_handshake(c);
    return false;
  }

  uint8_t client_finished[36] = {20, 0, 0, 32};
  uint8_t client_handshake_traffic_secret[32] = {0};
  TLS13_Handshake_FlightState_copy_client_handshake_traffic_secret(
      c->server_handshake_flight_state,
      client_handshake_traffic_secret,
      sizeof client_handshake_traffic_secret);
  TLS13_KeySchedule_finished_verify_data(
      client_handshake_traffic_secret,
      transcript_hash_through_server_finished,
      client_finished + TLS13_WIRE_HANDSHAKE_HEADER_LEN);

  uint8_t client_record[20000];
  size_t client_record_len = 0;
  uint8_t client_inner_plaintext[sizeof client_finished + 1u];
  size_t client_inner_plaintext_len = sizeof client_finished + 1u;
  size_t client_ciphertext_len = client_inner_plaintext_len + 16u;
  client_record_len = TLS13_WIRE_RECORD_HEADER_LEN + client_ciphertext_len;
  if (client_ciphertext_len > UINT16_MAX || client_record_len > sizeof client_record) {
    fprintf(stderr, "failed to send client Finished\n");
    fail_handshake(c);
    return false;
  }
  TLS13_Record_Framing_serialize_application_data_header(
      (uint16_t)client_ciphertext_len,
      client_record,
      TLS13_WIRE_RECORD_HEADER_LEN);
  TLS13_Record_Framing_encode_inner_plaintext_no_padding(
      client_finished,
      sizeof client_finished,
      22,
      client_inner_plaintext,
      client_inner_plaintext_len);
  bool sealed = TLS13_Handshake_FlightState_seal_client_handshake_record(
      c->server_handshake_flight_state,
      client_record,
      TLS13_WIRE_RECORD_HEADER_LEN,
      client_inner_plaintext,
      client_inner_plaintext_len,
      client_record + TLS13_WIRE_RECORD_HEADER_LEN);
  if (!sealed || write_all_fd(c->fd, client_record, client_record_len) != 0) {
    fprintf(stderr, "failed to send client Finished\n");
    fail_handshake(c);
    return false;
  }

  return true;
}

void TLS13_Handshake_External_send_client_hello(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  probe_handshake_send_client_hello((TLS13_Handshake_handshake_context)ctx, ch, NULL, NULL);
}

bool TLS13_Handshake_External_recv_server_hello(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  return probe_handshake_recv_server_hello((TLS13_Handshake_handshake_context)ctx, ch, NULL, NULL);
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

bool TLS13_Handshake_External_send_client_finished(
    TLS13_Handshake_External_handshake_context ctx,
    TLS13_IO_channel ch) {
  return probe_handshake_send_client_finished((TLS13_Handshake_handshake_context)ctx, ch, NULL, NULL);
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
  uint8_t transcript_hash_through_server_finished[32];
  uint8_t handshake_secret[32] = {0};
  uint8_t client_hello[PROBE_CLIENT_HELLO_CAPACITY];
  uint8_t server_hello_fragment[PROBE_SERVER_HELLO_CAPACITY];
  size_t client_hello_len = 0;
  size_t server_hello_len = 0;
  if (!copy_hello_messages(
          c,
          client_hello,
          &client_hello_len,
          server_hello_fragment,
          &server_hello_len)) {
    fprintf(stderr, "failed to copy hello transcript bytes\n");
    fail_handshake(c);
    return false;
  }
  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!copy_server_handshake_messages(c, server_handshake_messages)) {
    fprintf(stderr, "failed to copy server handshake transcript bytes\n");
    fail_handshake(c);
    return false;
  }
  TLS13_Handshake_FlightState_copy_handshake_secret(
      c->server_handshake_flight_state, handshake_secret, sizeof handshake_secret);
  if (compute_transcript_hash(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_handshake_messages,
          TLS13_Handshake_FlightState_server_through_finished_len(c->server_handshake_flight_state),
          transcript_hash_through_server_finished) != 0 ||
      derive_application_keys(
          handshake_secret,
          transcript_hash_through_server_finished,
          client_key,
          client_iv,
          server_key,
          server_iv) != 0) {
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

bool TLS13_Handshake_ByteDriver_External_read_next_encrypted_handshake_record(
    TLS13_Handshake_ByteDriver_External_context ctx,
    TLS13_IO_channel ch,
    void *progress) {
  (void)ch;
  (void)progress;
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  if (!handshake_can_continue(c) || c->fd < 0) {
    return false;
  }
  return read_next_encrypted_handshake_record(c);
}

bool TLS13_Handshake_ByteDriver_External_pending_handshake_message_complete(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *progress) {
  (void)progress;
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  uint8_t handshake_type = 0;
  uint32_t handshake_body_len = 0;
  size_t message_len = 0;
  return pending_handshake_metadata(c, &handshake_type, &handshake_body_len, &message_len);
}

uint8_t TLS13_Handshake_ByteDriver_External_pending_handshake_message_type(
    TLS13_Handshake_ByteDriver_External_context ctx,
    void *progress) {
  (void)progress;
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  uint8_t handshake_type = 0;
  uint32_t handshake_body_len = 0;
  size_t message_len = 0;
  if (!pending_handshake_metadata(c, &handshake_type, &handshake_body_len, &message_len)) {
    return 0;
  }
  return handshake_type;
}

bool TLS13_Handshake_ByteDriver_External_accept_encrypted_extensions(
    TLS13_Handshake_ByteDriver_External_context ctx) {
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  const uint8_t *body = NULL;
  uint32_t body_len = 0;
  size_t message_len = 0;
  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!pending_handshake_body(c, 8, server_handshake_messages, &body, &body_len, &message_len) ||
      !TLS13_Handshake_FlightState_accept_encrypted_extensions(
          c->server_handshake_flight_state, message_len)) {
    fprintf(stderr, "decrypted first OpenSSL handshake message is not EncryptedExtensions\n");
    return false;
  }
  (void)body;
  (void)body_len;
  return true;
}

bool TLS13_Handshake_ByteDriver_External_accept_certificate(
    TLS13_Handshake_ByteDriver_External_context ctx) {
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  const uint8_t *body = NULL;
  uint32_t body_len = 0;
  size_t message_len = 0;
  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!pending_handshake_body(c, 11, server_handshake_messages, &body, &body_len, &message_len)) {
    fprintf(stderr, "failed to parse server Certificate\n");
    return false;
  }
  uint8_t leaf_offset_bytes[2] = {0};
  uint8_t leaf_len_bytes[2] = {0};
  if (!TLS13_Handshake_Framing_parse_certificate_leaf_der_offsets(
          (uint8_t *)body,
          body_len,
          leaf_offset_bytes,
          sizeof leaf_offset_bytes,
          leaf_len_bytes,
          sizeof leaf_len_bytes)) {
    fprintf(stderr, "failed to parse server Certificate\n");
    return false;
  }
  size_t leaf_offset = ((size_t)leaf_offset_bytes[0] << 8) | (size_t)leaf_offset_bytes[1];
  size_t leaf_len = ((size_t)leaf_len_bytes[0] << 8) | (size_t)leaf_len_bytes[1];
  size_t certificate_body_offset = (size_t)(body - server_handshake_messages);
  TLS13_Handshake_FlightState_set_certificate_leaf(
      c->server_handshake_flight_state,
      certificate_body_offset + leaf_offset,
      leaf_len);
  if (!TLS13_Handshake_FlightState_accept_certificate(
          c->server_handshake_flight_state, message_len)) {
    fprintf(stderr, "failed to parse server Certificate\n");
    return false;
  }
  return true;
}

bool TLS13_Handshake_ByteDriver_External_accept_certificate_verify(
    TLS13_Handshake_ByteDriver_External_context ctx) {
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  const uint8_t *body = NULL;
  uint32_t body_len = 0;
  size_t message_len = 0;
  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!pending_handshake_body(c, 15, server_handshake_messages, &body, &body_len, &message_len)) {
    fprintf(stderr, "failed to parse server CertificateVerify\n");
    return false;
  }
  uint8_t signature_scheme_bytes[2] = {0};
  uint8_t signature_len_bytes[2] = {0};
  if (!TLS13_Handshake_Framing_parse_certificate_verify_body(
          (uint8_t *)body,
          body_len,
          signature_scheme_bytes,
          sizeof signature_scheme_bytes,
          signature_len_bytes,
          sizeof signature_len_bytes)) {
    fprintf(stderr, "failed to parse server CertificateVerify\n");
    return false;
  }
  uint16_t signature_scheme =
      ((uint16_t)signature_scheme_bytes[0] << 8) | (uint16_t)signature_scheme_bytes[1];
  size_t signature_len =
      ((size_t)signature_len_bytes[0] << 8) | (size_t)signature_len_bytes[1];
  size_t signature_body_offset = (size_t)(body - server_handshake_messages);
  TLS13_Handshake_FlightState_set_certificate_verify_signature(
      c->server_handshake_flight_state,
      signature_scheme,
      signature_body_offset + 4u,
      signature_len);
  if (!TLS13_Handshake_FlightState_accept_certificate_verify(
          c->server_handshake_flight_state, message_len)) {
    fprintf(stderr, "failed to parse server CertificateVerify\n");
    return false;
  }
  return true;
}

bool TLS13_Handshake_ByteDriver_External_accept_finished(
    TLS13_Handshake_ByteDriver_External_context ctx) {
  TLS13_Connection_connection c = (TLS13_Connection_connection)ctx;
  const uint8_t *body = NULL;
  uint32_t body_len = 0;
  size_t message_len = 0;
  uint8_t server_handshake_messages[PROBE_SERVER_HANDSHAKE_CAPACITY];
  if (!pending_handshake_body(c, 20, server_handshake_messages, &body, &body_len, &message_len) ||
      body_len != 32) {
    fprintf(stderr, "OpenSSL Finished has unexpected length\n");
    return false;
  }
  if (!TLS13_Handshake_FlightState_accept_finished(
          c->server_handshake_flight_state, message_len, body_len)) {
    fprintf(stderr, "OpenSSL Finished has unexpected length\n");
    return false;
  }
  TLS13_Handshake_FlightState_set_server_finished_verify_data(
      c->server_handshake_flight_state, (uint8_t *)body, body_len);
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
