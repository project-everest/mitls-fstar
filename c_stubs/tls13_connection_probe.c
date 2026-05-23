#include "tls13_connection_probe.h"

#include "tls13_hacl_stubs.h"
#include "tls13_handshake_external.h"
#include "tls13_io_stubs.h"
#include "tls13_openssl_stubs.h"
#include "tls13_wire_stubs.h"

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_CONNECTION_WRAPPER
#include "TLS13_KeySchedule.h"
#include "TLS13_Record.h"
#include "tls13_connection_external_layer.h"
#endif

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_HANDSHAKE
#include "TLS13_Handshake_Driver.h"
#endif

#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PROBE_APP_RECORD_CHUNK_LEN 4096u

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_CONNECTION_WRAPPER
#define TLS13_Connection_connection TLS13_Connection_External_connection
#define TLS13_Connection_connection_s TLS13_Connection_External_connection_s
#endif

struct TLS13_Connection_connection_s {
  const char *host;
  uint16_t port;
  const char *ca_pem_path;
  int fd;
  bool handshake_failed;
  bool application_ready;
  uint8_t client_hello[512];
  size_t client_hello_len;
  uint8_t server_hello_fragment[4096];
  size_t server_hello_len;
  uint8_t handshake_secret[32];
  uint8_t client_handshake_traffic_secret[32];
  uint8_t server_handshake_traffic_secret[32];
  uint8_t client_handshake_key[32];
  uint8_t client_handshake_iv[12];
  uint8_t server_handshake_key[32];
  uint8_t server_handshake_iv[12];
  uint8_t server_handshake_messages[32768];
  size_t server_handshake_len;
  size_t server_handshake_before_finished_len;
  size_t server_handshake_through_finished_len;
  uint8_t server_finished_verify_data[32];
  bool saw_encrypted_extensions;
  bool saw_certificate;
  bool saw_certificate_verify;
  bool saw_finished;
  const uint8_t *leaf_der;
  size_t leaf_der_len;
  uint16_t signature_scheme;
  const uint8_t *signature;
  size_t signature_len;
  size_t certificate_verify_offset;
  tls13_peer_identity *peer;
  uint8_t client_application_key[32];
  uint8_t client_application_iv[12];
  uint8_t server_application_key[32];
  uint8_t server_application_iv[12];
  uint64_t client_application_sequence_number;
  uint64_t server_application_sequence_number;
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
  if (!tls13_wire_parse_record_header(
          header, TLS13_WIRE_RECORD_HEADER_LEN, content_type, legacy_version, fragment_len) ||
      *fragment_len > fragment_capacity) {
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
  static const uint8_t label_derived[] = {'d', 'e', 'r', 'i', 'v', 'e', 'd'};
  static const uint8_t label_c_hs_traffic[] = {
      'c', ' ', 'h', 's', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t label_s_hs_traffic[] = {
      's', ' ', 'h', 's', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t label_key[] = {'k', 'e', 'y'};
  static const uint8_t label_iv[] = {'i', 'v'};

  uint8_t empty_hash[32];
  uint8_t early_secret[32];
  uint8_t derived_secret[32];
  uint8_t shared_secret[32];
  uint8_t transcript[1024];
  uint8_t transcript_hash[32];

  if (client_hello_len > sizeof transcript ||
      server_hello_len > sizeof transcript - client_hello_len) {
    return -1;
  }
  if (!tls13_hacl_sha256(empty_hash, NULL, 0) ||
      !tls13_hacl_hkdf_extract_sha256(
          early_secret, NULL, 0, zero_secret, sizeof zero_secret) ||
      !tls13_hacl_x25519_shared(shared_secret, client_private_key, server_key_share)) {
    return -1;
  }

  memcpy(transcript, client_hello, client_hello_len);
  memcpy(transcript + client_hello_len, server_hello, server_hello_len);
  if (!tls13_hacl_sha256(transcript_hash, transcript, client_hello_len + server_hello_len)) {
    return -1;
  }

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_KEY_SCHEDULE
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
#else
  if (!tls13_hacl_hkdf_expand_label_sha256(
          derived_secret,
          sizeof derived_secret,
          early_secret,
          label_derived,
          sizeof label_derived,
          empty_hash,
          sizeof empty_hash) ||
      !tls13_hacl_hkdf_extract_sha256(
          handshake_secret,
          derived_secret,
          sizeof derived_secret,
          shared_secret,
          sizeof shared_secret) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_handshake_traffic_secret,
          32,
          handshake_secret,
          label_c_hs_traffic,
          sizeof label_c_hs_traffic,
          transcript_hash,
          sizeof transcript_hash) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_handshake_traffic_secret,
          32,
          handshake_secret,
          label_s_hs_traffic,
          sizeof label_s_hs_traffic,
          transcript_hash,
          sizeof transcript_hash) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_key,
          32,
          client_handshake_traffic_secret,
          label_key,
          sizeof label_key,
          NULL,
          0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_iv,
          12,
          client_handshake_traffic_secret,
          label_iv,
          sizeof label_iv,
          NULL,
          0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_key,
          32,
          server_handshake_traffic_secret,
          label_key,
          sizeof label_key,
          NULL,
          0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_iv,
          12,
          server_handshake_traffic_secret,
          label_iv,
          sizeof label_iv,
          NULL,
          0)) {
    return -1;
  }
#endif
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
  uint8_t transcript[32768];
  if (client_hello_len > sizeof transcript ||
      server_hello_len > sizeof transcript - client_hello_len ||
      server_handshake_len > sizeof transcript - client_hello_len - server_hello_len) {
    return -1;
  }
  size_t pos = 0;
  memcpy(transcript + pos, client_hello, client_hello_len);
  pos += client_hello_len;
  memcpy(transcript + pos, server_hello, server_hello_len);
  pos += server_hello_len;
  memcpy(transcript + pos, server_handshake_messages, server_handshake_len);
  pos += server_handshake_len;
  return tls13_hacl_sha256(transcript_hash, transcript, pos) ? 0 : -1;
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
#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_KEY_SCHEDULE
  TLS13_KeySchedule_finished_verify_data(
      (uint8_t *)server_handshake_traffic_secret, transcript_hash, expected);
#else
  if (!tls13_hacl_finished_verify_data_sha256(
          expected, server_handshake_traffic_secret, transcript_hash)) {
    return -1;
  }
#endif
  return memcmp(expected, finished_verify_data, 32) == 0 ? 0 : -1;
}

static int derive_application_keys(
    const uint8_t handshake_secret[32],
    const uint8_t transcript_hash[32],
    uint8_t client_key[32],
    uint8_t client_iv[12],
    uint8_t server_key[32],
    uint8_t server_iv[12]) {
  static const uint8_t zero_secret[32] = {0};
  static const uint8_t label_derived[] = {'d', 'e', 'r', 'i', 'v', 'e', 'd'};
  static const uint8_t label_c_ap_traffic[] = {
      'c', ' ', 'a', 'p', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t label_s_ap_traffic[] = {
      's', ' ', 'a', 'p', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t label_key[] = {'k', 'e', 'y'};
  static const uint8_t label_iv[] = {'i', 'v'};
  uint8_t empty_hash[32];
  uint8_t derived_secret[32];
  uint8_t master_secret[32];
  uint8_t client_application_traffic_secret[32];
  uint8_t server_application_traffic_secret[32];

  if (!tls13_hacl_sha256(empty_hash, NULL, 0)) {
    return -1;
  }

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_KEY_SCHEDULE
  TLS13_KeySchedule_master_secret((uint8_t *)handshake_secret, master_secret);
  TLS13_KeySchedule_client_application_traffic_secret(
      master_secret, (uint8_t *)transcript_hash, client_application_traffic_secret);
  TLS13_KeySchedule_server_application_traffic_secret(
      master_secret, (uint8_t *)transcript_hash, server_application_traffic_secret);
  TLS13_KeySchedule_derive_traffic_key(client_application_traffic_secret, client_key);
  TLS13_KeySchedule_derive_traffic_iv(client_application_traffic_secret, client_iv);
  TLS13_KeySchedule_derive_traffic_key(server_application_traffic_secret, server_key);
  TLS13_KeySchedule_derive_traffic_iv(server_application_traffic_secret, server_iv);
#else
  if (!tls13_hacl_hkdf_expand_label_sha256(
          derived_secret,
          sizeof derived_secret,
          handshake_secret,
          label_derived,
          sizeof label_derived,
          empty_hash,
          sizeof empty_hash) ||
      !tls13_hacl_hkdf_extract_sha256(
          master_secret, derived_secret, sizeof derived_secret, zero_secret, sizeof zero_secret) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_application_traffic_secret,
          sizeof client_application_traffic_secret,
          master_secret,
          label_c_ap_traffic,
          sizeof label_c_ap_traffic,
          transcript_hash,
          32) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_application_traffic_secret,
          sizeof server_application_traffic_secret,
          master_secret,
          label_s_ap_traffic,
          sizeof label_s_ap_traffic,
          transcript_hash,
          32) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_key, 32, client_application_traffic_secret, label_key, sizeof label_key, NULL, 0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          client_iv, 12, client_application_traffic_secret, label_iv, sizeof label_iv, NULL, 0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_key, 32, server_application_traffic_secret, label_key, sizeof label_key, NULL, 0) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_iv, 12, server_application_traffic_secret, label_iv, sizeof label_iv, NULL, 0)) {
    return -1;
  }
#endif
  return 0;
}

static int seal_record(
    const uint8_t key[32],
    const uint8_t iv[12],
    uint64_t sequence_number,
    uint8_t inner_content_type,
    const uint8_t *plaintext,
    size_t plaintext_len,
    uint8_t *record,
    size_t record_capacity,
    size_t *record_len) {
  uint8_t inner_plaintext[20000];
  uint8_t nonce[12];
  if (plaintext_len > sizeof inner_plaintext - 1u ||
      plaintext_len > UINT16_MAX - 17u ||
      record_capacity < TLS13_WIRE_RECORD_HEADER_LEN + plaintext_len + 1u + 16u) {
    return -1;
  }
  memcpy(inner_plaintext, plaintext, plaintext_len);
  inner_plaintext[plaintext_len] = inner_content_type;
  size_t inner_plaintext_len = plaintext_len + 1u;
  size_t ciphertext_len = inner_plaintext_len + 16u;
  if (!tls13_wire_serialize_record_header(record, 23, 0x0303, (uint16_t)ciphertext_len) ||
      !tls13_record_nonce(nonce, iv, sequence_number) ||
      !tls13_hacl_chacha20_poly1305_seal_combined(
          record + TLS13_WIRE_RECORD_HEADER_LEN,
          ciphertext_len,
          key,
          nonce,
          record,
          TLS13_WIRE_RECORD_HEADER_LEN,
          inner_plaintext,
          inner_plaintext_len)) {
    return -1;
  }
  *record_len = TLS13_WIRE_RECORD_HEADER_LEN + ciphertext_len;
  return 0;
}

static TLS13_Connection_connection from_handshake_context(
    TLS13_Handshake_handshake_context ctx) {
  return (TLS13_Connection_connection)ctx;
}

static bool handshake_can_continue(TLS13_Connection_connection c) {
  return c != NULL && !c->handshake_failed && !c->application_ready;
}

static void fail_handshake(TLS13_Connection_connection c) {
  if (c == NULL) {
    return;
  }
  c->handshake_failed = true;
  if (c->fd >= 0) {
    tls13_io_close_fd(c->fd);
    c->fd = -1;
  }
}

void TLS13_Handshake_send_client_hello(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (c == NULL || c->application_ready || c->fd >= 0) {
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
  static const uint8_t hostname[] = {'l', 'o', 'c', 'a', 'l', 'h', 'o', 's', 't'};

  if (!tls13_wire_serialize_supported_client_hello(
          c->client_hello,
          sizeof c->client_hello,
          random,
          key_share,
          hostname,
          sizeof hostname,
          &c->client_hello_len)) {
    fprintf(stderr, "failed to serialize ClientHello\n");
    fail_handshake(c);
    return;
  }

  uint8_t record[TLS13_WIRE_RECORD_HEADER_LEN + sizeof c->client_hello];
  if (!tls13_wire_serialize_record_header(
          record, 22, 0x0301, (uint16_t)c->client_hello_len)) {
    fprintf(stderr, "failed to serialize ClientHello record header\n");
    fail_handshake(c);
    return;
  }
  memcpy(record + TLS13_WIRE_RECORD_HEADER_LEN, c->client_hello, c->client_hello_len);
  size_t record_len = TLS13_WIRE_RECORD_HEADER_LEN + c->client_hello_len;

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

bool TLS13_Handshake_recv_server_hello(
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
  uint8_t server_random[32];
  uint8_t server_key_share[32];
  if (read_record(
          c->fd,
          header,
          c->server_hello_fragment,
          sizeof c->server_hello_fragment,
          &content_type,
          &legacy_version,
          &fragment_len) != 0 ||
      content_type != 22) {
    fprintf(stderr, "bad ServerHello record header\n");
    fail_handshake(c);
    return false;
  }
  if (!tls13_wire_parse_supported_server_hello(
          c->server_hello_fragment, fragment_len, server_random, server_key_share)) {
    fprintf(stderr, "failed to parse supported OpenSSL ServerHello\n");
    fail_handshake(c);
    return false;
  }
  c->server_hello_len = fragment_len;
  if (derive_server_handshake_keys(
          c->client_hello,
          c->client_hello_len,
          c->server_hello_fragment,
          c->server_hello_len,
          server_key_share,
          c->handshake_secret,
          c->client_handshake_traffic_secret,
          c->server_handshake_traffic_secret,
          c->client_handshake_key,
          c->client_handshake_iv,
          c->server_handshake_key,
          c->server_handshake_iv) != 0) {
    fprintf(stderr, "failed to derive handshake traffic keys\n");
    fail_handshake(c);
    return false;
  }
  return true;
}

bool TLS13_Handshake_recv_encrypted_extensions(
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

  c->server_handshake_len = 0;
  c->server_handshake_before_finished_len = 0;
  c->server_handshake_through_finished_len = 0;
  c->saw_encrypted_extensions = false;
  c->saw_certificate = false;
  c->saw_certificate_verify = false;
  c->saw_finished = false;
  c->leaf_der = NULL;
  c->leaf_der_len = 0;
  c->signature = NULL;
  c->signature_len = 0;
  c->certificate_verify_offset = 0;

  size_t parsed_handshake_len = 0;
  uint64_t server_sequence_number = 0;
  for (unsigned attempts = 0; attempts < 8 && !c->saw_finished; ++attempts) {
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
      fail_handshake(c);
      return false;
    }
    if (content_type == 20 && fragment_len == 1 && encrypted_fragment[0] == 1) {
      continue;
    }
    if (content_type != 23 || fragment_len < 16) {
      fprintf(stderr, "unexpected record before server Finished: %u\n", content_type);
      fail_handshake(c);
      return false;
    }

    uint8_t nonce[12];
    uint8_t inner_plaintext[20000];
    size_t inner_plaintext_len = (size_t)fragment_len - 16u;
    if (!tls13_record_nonce(nonce, c->server_handshake_iv, server_sequence_number++) ||
        !tls13_hacl_chacha20_poly1305_open_combined(
            inner_plaintext,
            inner_plaintext_len,
            c->server_handshake_key,
            nonce,
            encrypted_header,
            TLS13_WIRE_RECORD_HEADER_LEN,
            encrypted_fragment,
            fragment_len)) {
      fprintf(stderr, "failed to decrypt OpenSSL encrypted handshake record\n");
      fail_handshake(c);
      return false;
    }

    uint8_t inner_content_type = 0;
    size_t handshake_plaintext_len = 0;
    if (!tls13_wire_decode_inner_plaintext(
            inner_plaintext, inner_plaintext_len, &inner_content_type, &handshake_plaintext_len) ||
        inner_content_type != 22 ||
        handshake_plaintext_len > sizeof c->server_handshake_messages - c->server_handshake_len) {
      fprintf(stderr, "failed to decode OpenSSL handshake inner plaintext\n");
      fail_handshake(c);
      return false;
    }
    memcpy(
        c->server_handshake_messages + c->server_handshake_len,
        inner_plaintext,
        handshake_plaintext_len);
    c->server_handshake_len += handshake_plaintext_len;

    while (c->server_handshake_len - parsed_handshake_len >= TLS13_WIRE_HANDSHAKE_HEADER_LEN) {
      uint8_t handshake_type = 0;
      uint32_t handshake_body_len = 0;
      if (!tls13_wire_parse_handshake_header(
              c->server_handshake_messages + parsed_handshake_len,
              c->server_handshake_len - parsed_handshake_len,
              &handshake_type,
              &handshake_body_len)) {
        fprintf(stderr, "failed to parse decrypted handshake header\n");
        fail_handshake(c);
        return false;
      }
      size_t message_len = TLS13_WIRE_HANDSHAKE_HEADER_LEN + (size_t)handshake_body_len;
      if (message_len > c->server_handshake_len - parsed_handshake_len) {
        break;
      }
      if (parsed_handshake_len == 0 && handshake_type != 8) {
        fprintf(stderr, "decrypted first OpenSSL handshake message is not EncryptedExtensions\n");
        fail_handshake(c);
        return false;
      }

      const uint8_t *body =
          c->server_handshake_messages + parsed_handshake_len + TLS13_WIRE_HANDSHAKE_HEADER_LEN;
      switch (handshake_type) {
      case 8:
        c->saw_encrypted_extensions = true;
        break;
      case 11:
        if (!tls13_wire_parse_certificate_leaf_der(
                body, handshake_body_len, &c->leaf_der, &c->leaf_der_len)) {
          fprintf(stderr, "failed to parse server Certificate\n");
          fail_handshake(c);
          return false;
        }
        c->saw_certificate = true;
        break;
      case 15:
        c->certificate_verify_offset = parsed_handshake_len;
        if (!tls13_wire_parse_certificate_verify(
                body,
                handshake_body_len,
                &c->signature_scheme,
                &c->signature,
                &c->signature_len)) {
          fprintf(stderr, "failed to parse server CertificateVerify\n");
          fail_handshake(c);
          return false;
        }
        c->saw_certificate_verify = true;
        break;
      case 20:
        if (handshake_body_len != 32) {
          fprintf(stderr, "OpenSSL Finished has unexpected length\n");
          fail_handshake(c);
          return false;
        }
        c->server_handshake_before_finished_len = parsed_handshake_len;
        c->server_handshake_through_finished_len = parsed_handshake_len + message_len;
        memcpy(
            c->server_finished_verify_data,
            c->server_handshake_messages + parsed_handshake_len + TLS13_WIRE_HANDSHAKE_HEADER_LEN,
            sizeof c->server_finished_verify_data);
        c->saw_finished = true;
        break;
      default:
        fprintf(stderr, "unexpected server handshake message before Finished: %u\n", handshake_type);
        fail_handshake(c);
        return false;
      }
      if (c->saw_finished) {
        break;
      }
      parsed_handshake_len += message_len;
    }
  }

  if (!c->saw_finished || !c->saw_encrypted_extensions) {
    fprintf(stderr, "OpenSSL encrypted handshake messages were incomplete\n");
    fail_handshake(c);
    return false;
  }
  return true;
}

bool TLS13_Handshake_recv_certificate(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) || !c->saw_certificate) {
    fail_handshake(c);
    return false;
  }
  return true;
}

bool TLS13_Handshake_validate_certificate(
    TLS13_Handshake_handshake_context ctx,
    void *erased_state_ref,
    void *erased_state) {
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) || !c->saw_certificate) {
    fail_handshake(c);
    return false;
  }
  size_t ca_pem_len = 0;
  uint8_t *ca_pem = read_file(c->ca_pem_path, &ca_pem_len);
  if (ca_pem == NULL) {
    fail_handshake(c);
    return false;
  }
  tls13_openssl_peer_identity_free(c->peer);
  c->peer = NULL;
  bool ok = tls13_openssl_validate_leaf_der(
      "localhost", ca_pem, ca_pem_len, c->leaf_der, c->leaf_der_len, &c->peer);
  free(ca_pem);
  if (!ok || c->peer == NULL) {
    fprintf(stderr, "failed to validate server certificate\n");
    fail_handshake(c);
    return false;
  }
  return true;
}

bool TLS13_Handshake_recv_certificate_verify(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) || !c->saw_certificate_verify || c->peer == NULL) {
    fail_handshake(c);
    return false;
  }
  uint8_t transcript_hash[32];
  uint8_t certificate_verify_input[TLS13_WIRE_CERTIFICATE_VERIFY_INPUT_LEN];
  if (compute_transcript_hash(
          c->client_hello,
          c->client_hello_len,
          c->server_hello_fragment,
          c->server_hello_len,
          c->server_handshake_messages,
          c->certificate_verify_offset,
          transcript_hash) != 0 ||
      !tls13_wire_build_server_certificate_verify_input(
          certificate_verify_input, transcript_hash)) {
    fprintf(stderr, "failed to build CertificateVerify input\n");
    fail_handshake(c);
    return false;
  }
  if (!tls13_openssl_peer_verify_signature(
          c->peer,
          c->signature_scheme,
          certificate_verify_input,
          sizeof certificate_verify_input,
          c->signature,
          c->signature_len)) {
    fprintf(stderr, "failed to verify server CertificateVerify\n");
    fail_handshake(c);
    return false;
  }
  return true;
}

bool TLS13_Handshake_recv_server_finished(
    TLS13_Handshake_handshake_context ctx,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_state_ref;
  (void)erased_state;
  TLS13_Connection_connection c = from_handshake_context(ctx);
  if (!handshake_can_continue(c) || !c->saw_finished) {
    fail_handshake(c);
    return false;
  }
  if (verify_server_finished(
          c->client_hello,
          c->client_hello_len,
          c->server_hello_fragment,
          c->server_hello_len,
          c->server_handshake_messages,
          c->server_handshake_before_finished_len,
          c->server_finished_verify_data,
          c->server_handshake_traffic_secret) != 0) {
    fprintf(stderr, "failed to verify OpenSSL server Finished\n");
    fail_handshake(c);
    return false;
  }
  return true;
}

bool TLS13_Handshake_send_client_finished(
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
  if (compute_transcript_hash(
          c->client_hello,
          c->client_hello_len,
          c->server_hello_fragment,
          c->server_hello_len,
          c->server_handshake_messages,
          c->server_handshake_through_finished_len,
          transcript_hash_through_server_finished) != 0) {
    fprintf(stderr, "failed to hash transcript through server Finished\n");
    fail_handshake(c);
    return false;
  }

  uint8_t client_finished[36] = {20, 0, 0, 32};
#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_KEY_SCHEDULE
  TLS13_KeySchedule_finished_verify_data(
      c->client_handshake_traffic_secret,
      transcript_hash_through_server_finished,
      client_finished + TLS13_WIRE_HANDSHAKE_HEADER_LEN);
#else
  if (!tls13_hacl_finished_verify_data_sha256(
          client_finished + TLS13_WIRE_HANDSHAKE_HEADER_LEN,
          c->client_handshake_traffic_secret,
          transcript_hash_through_server_finished)) {
    fprintf(stderr, "failed to compute client Finished\n");
    fail_handshake(c);
    return false;
  }
#endif

  uint8_t client_record[20000];
  size_t client_record_len = 0;
  if (seal_record(
          c->client_handshake_key,
          c->client_handshake_iv,
          0,
          22,
          client_finished,
          sizeof client_finished,
          client_record,
          sizeof client_record,
          &client_record_len) != 0 ||
      write_all_fd(c->fd, client_record, client_record_len) != 0) {
    fprintf(stderr, "failed to send client Finished\n");
    fail_handshake(c);
    return false;
  }

  if (derive_application_keys(
          c->handshake_secret,
          transcript_hash_through_server_finished,
          c->client_application_key,
          c->client_application_iv,
          c->server_application_key,
          c->server_application_iv) != 0) {
    fprintf(stderr, "failed to derive application traffic keys\n");
    fail_handshake(c);
    return false;
  }

  c->application_ready = true;
  c->client_application_sequence_number = 0;
  c->server_application_sequence_number = 0;
  return true;
}

TLS13_Connection_connection tls13_connection_probe_new(
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
  c->host = host;
  c->port = port;
  c->ca_pem_path = ca_pem_path;
  c->fd = -1;
  return c;
}

void tls13_connection_probe_free(TLS13_Connection_connection c) {
  if (c == NULL) {
    return;
  }
  if (c->fd >= 0) {
    tls13_io_close_fd(c->fd);
  }
  tls13_openssl_peer_identity_free(c->peer);
  free(c);
}

#ifndef TLS13_CONNECTION_PROBE_USE_EXTRACTED_CONNECTION_WRAPPER
bool TLS13_Connection_client_connect(
    TLS13_Connection_connection c,
    TLS13_IO_channel ch,
    void *erased_state_ref,
    void *erased_state) {
  (void)erased_state_ref;
  (void)erased_state;
  if (c == NULL || c->application_ready || c->fd >= 0) {
    return false;
  }
  c->handshake_failed = false;

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_HANDSHAKE
  bool ok = TLS13_Handshake_Driver_run_client_handshake(
      (TLS13_Handshake_handshake_context)c, ch);
#else
  TLS13_Handshake_send_client_hello((TLS13_Handshake_handshake_context)c, ch, NULL, NULL);
  bool ok =
      TLS13_Handshake_recv_server_hello((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_recv_encrypted_extensions((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_recv_certificate((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_validate_certificate((TLS13_Handshake_handshake_context)c, NULL, NULL) &&
      TLS13_Handshake_recv_certificate_verify((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_recv_server_finished((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_send_client_finished((TLS13_Handshake_handshake_context)c, ch, NULL, NULL);
#endif

  if (!ok || c->handshake_failed || !c->application_ready) {
    fail_handshake(c);
    return false;
  }
  return true;
}
#endif

#ifndef TLS13_CONNECTION_PROBE_USE_EXTRACTED_CONNECTION_WRAPPER
bool TLS13_Connection_client_write_all(
    TLS13_Connection_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *erased_bytes,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_bytes;
  (void)erased_state_ref;
  (void)erased_state;
  if (c == NULL || !c->application_ready || c->fd < 0 || (len != 0 && buf == NULL)) {
    return false;
  }

  uint8_t record[20000];
  size_t sent = 0;
  while (sent < len) {
    size_t remaining = len - sent;
    size_t chunk_len = remaining < PROBE_APP_RECORD_CHUNK_LEN
                           ? remaining
                           : PROBE_APP_RECORD_CHUNK_LEN;
    size_t record_len = 0;
    if (seal_record(
            c->client_application_key,
            c->client_application_iv,
            c->client_application_sequence_number++,
            23,
            buf + sent,
            chunk_len,
            record,
            sizeof record,
            &record_len) != 0 ||
        write_all_fd(c->fd, record, record_len) != 0) {
      fprintf(stderr, "failed to send application-data record\n");
      c->application_ready = false;
      return false;
    }
    sent += chunk_len;
  }
  return true;
}
#endif

#ifndef TLS13_CONNECTION_PROBE_USE_EXTRACTED_CONNECTION_WRAPPER
bool TLS13_Connection_client_read_exact(
    TLS13_Connection_connection c,
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t len,
    void *erased_old_bytes,
    void *erased_state_ref,
    void *erased_state) {
  (void)ch;
  (void)erased_old_bytes;
  (void)erased_state_ref;
  (void)erased_state;
  if (c == NULL || !c->application_ready || c->fd < 0 || (len != 0 && out == NULL)) {
    return false;
  }

  size_t received = 0;
  unsigned max_attempts = (unsigned)(len / PROBE_APP_RECORD_CHUNK_LEN + 128u);
  for (unsigned attempts = 0; attempts < max_attempts && received < len; ++attempts) {
    uint8_t header[TLS13_WIRE_RECORD_HEADER_LEN];
    uint8_t encrypted_fragment[20000];
    uint8_t content_type = 0;
    uint16_t legacy_version = 0;
    uint16_t fragment_len = 0;
    if (read_record(
            c->fd,
            header,
            encrypted_fragment,
            sizeof encrypted_fragment,
            &content_type,
            &legacy_version,
            &fragment_len) != 0 ||
        content_type != 23 ||
        fragment_len < 16) {
      fprintf(stderr, "failed to read application-data response record\n");
      c->application_ready = false;
      return false;
    }

    uint8_t nonce[12];
    uint8_t inner_plaintext[20000];
    size_t inner_plaintext_len = (size_t)fragment_len - 16u;
    if (!tls13_record_nonce(nonce, c->server_application_iv, c->server_application_sequence_number++) ||
        !tls13_hacl_chacha20_poly1305_open_combined(
            inner_plaintext,
            inner_plaintext_len,
            c->server_application_key,
            nonce,
            header,
            TLS13_WIRE_RECORD_HEADER_LEN,
            encrypted_fragment,
            fragment_len)) {
      fprintf(stderr, "failed to decrypt application-data response record\n");
      c->application_ready = false;
      return false;
    }

    uint8_t inner_content_type = 0;
    size_t response_len = 0;
    if (!tls13_wire_decode_inner_plaintext(
            inner_plaintext, inner_plaintext_len, &inner_content_type, &response_len)) {
      fprintf(stderr, "failed to decode application-data response record\n");
      c->application_ready = false;
      return false;
    }
    if (inner_content_type == 22) {
      continue;
    }
    if (inner_content_type != 23 || response_len > len - received) {
      fprintf(stderr, "unexpected application-data response record\n");
      c->application_ready = false;
      return false;
    }
    memcpy(out + received, inner_plaintext, response_len);
    received += response_len;
  }

  if (received != len) {
    fprintf(stderr, "OpenSSL echo application data was not received\n");
    c->application_ready = false;
    return false;
  }
  return true;
}
#endif

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_CONNECTION_WRAPPER
TLS13_Connection_External_connection TLS13_Connection_External_client_new(
    uint8_t *hostname,
    size_t hostname_len,
    TLS13_X509_Spec_trust_store trust_store,
    void *hostname_bytes) {
  (void)trust_store;
  (void)hostname_bytes;
  char host[256];
  if (hostname == NULL || hostname_len == 0 || hostname_len >= sizeof host) {
    return NULL;
  }
  memcpy(host, hostname, hostname_len);
  host[hostname_len] = '\0';
  return tls13_connection_probe_new(host, 443, "");
}

void TLS13_Connection_External_client_free(TLS13_Connection_External_connection c) {
  tls13_connection_probe_free(c);
}

bool TLS13_Connection_External_client_connect(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch) {
  if (c == NULL || c->application_ready || c->fd >= 0) {
    return false;
  }
  c->handshake_failed = false;

#ifdef TLS13_CONNECTION_PROBE_USE_EXTRACTED_HANDSHAKE
  bool ok = TLS13_Handshake_Driver_run_client_handshake(
      (TLS13_Handshake_handshake_context)c, ch);
#else
  TLS13_Handshake_send_client_hello((TLS13_Handshake_handshake_context)c, ch, NULL, NULL);
  bool ok =
      TLS13_Handshake_recv_server_hello((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_recv_encrypted_extensions((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_recv_certificate((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_validate_certificate((TLS13_Handshake_handshake_context)c, NULL, NULL) &&
      TLS13_Handshake_recv_certificate_verify((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_recv_server_finished((TLS13_Handshake_handshake_context)c, ch, NULL, NULL) &&
      TLS13_Handshake_send_client_finished((TLS13_Handshake_handshake_context)c, ch, NULL, NULL);
#endif

  if (!ok || c->handshake_failed || !c->application_ready) {
    fail_handshake(c);
    return false;
  }
  return true;
}

size_t TLS13_Connection_External_client_write(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *bytes) {
  (void)bytes;
  return TLS13_Connection_External_client_write_all(c, ch, buf, len, bytes) ? len : 0;
}

bool TLS13_Connection_External_client_write_all(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *bytes) {
  (void)ch;
  (void)bytes;
  if (c == NULL || !c->application_ready || c->fd < 0 || (len != 0 && buf == NULL)) {
    return false;
  }

  TLS13_Record_record_state record_state = TLS13_Record_record_state_new();
  TLS13_Record_install_keys(record_state, 2, c->client_application_key, c->client_application_iv);

  uint8_t record[20000];
  size_t sent = 0;
  while (sent < len) {
    uint8_t inner_plaintext[PROBE_APP_RECORD_CHUNK_LEN + 1u];
    size_t remaining = len - sent;
    size_t chunk_len = remaining < PROBE_APP_RECORD_CHUNK_LEN
                           ? remaining
                           : PROBE_APP_RECORD_CHUNK_LEN;
    size_t inner_plaintext_len = chunk_len + 1u;
    size_t ciphertext_len = inner_plaintext_len + 16u;
    size_t record_len = TLS13_WIRE_RECORD_HEADER_LEN + ciphertext_len;
    if (sizeof record < record_len ||
        chunk_len > sizeof inner_plaintext - 1u ||
        !tls13_wire_serialize_record_header(record, 23, 0x0303, (uint16_t)ciphertext_len)) {
      TLS13_Record_record_state_free(record_state);
      c->application_ready = false;
      return false;
    }
    memcpy(inner_plaintext, buf + sent, chunk_len);
    inner_plaintext[chunk_len] = 23;
    if (!TLS13_Record_seal_application(
            record_state,
            record,
            TLS13_WIRE_RECORD_HEADER_LEN,
            inner_plaintext,
            inner_plaintext_len,
            record + TLS13_WIRE_RECORD_HEADER_LEN) ||
        write_all_fd(c->fd, record, record_len) != 0) {
      TLS13_Record_record_state_free(record_state);
      fprintf(stderr, "failed to send application-data record\n");
      c->application_ready = false;
      return false;
    }
    sent += chunk_len;
  }
  TLS13_Record_record_state_free(record_state);
  return true;
}

size_t TLS13_Connection_External_client_read(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t max_len,
    void *old_bytes) {
  (void)old_bytes;
  return TLS13_Connection_External_client_read_exact(c, ch, out, max_len, old_bytes) ? max_len : 0;
}

bool TLS13_Connection_External_client_read_exact(
    TLS13_Connection_External_connection c,
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t len,
    void *old_bytes) {
  (void)ch;
  (void)old_bytes;
  if (c == NULL || !c->application_ready || c->fd < 0 || (len != 0 && out == NULL)) {
    return false;
  }

  TLS13_Record_record_state record_state = TLS13_Record_record_state_new();
  TLS13_Record_install_keys(record_state, 2, c->server_application_key, c->server_application_iv);

  size_t received = 0;
  unsigned max_attempts = (unsigned)(len / PROBE_APP_RECORD_CHUNK_LEN + 128u);
  for (unsigned attempts = 0; attempts < max_attempts && received < len; ++attempts) {
    uint8_t header[TLS13_WIRE_RECORD_HEADER_LEN];
    uint8_t encrypted_fragment[20000];
    uint8_t inner_plaintext[20000];
    uint8_t content_type = 0;
    uint16_t legacy_version = 0;
    uint16_t fragment_len = 0;
    if (read_record(
            c->fd,
            header,
            encrypted_fragment,
            sizeof encrypted_fragment,
            &content_type,
            &legacy_version,
            &fragment_len) != 0 ||
        content_type != 23 ||
        fragment_len < 16 ||
        (size_t)fragment_len - 16u > sizeof inner_plaintext) {
      TLS13_Record_record_state_free(record_state);
      fprintf(stderr, "failed to read application-data response record\n");
      c->application_ready = false;
      return false;
    }

    size_t inner_plaintext_len = (size_t)fragment_len - 16u;
    if (!TLS13_Record_open_application(
            record_state,
            header,
            TLS13_WIRE_RECORD_HEADER_LEN,
            encrypted_fragment,
            fragment_len,
            inner_plaintext)) {
      TLS13_Record_record_state_free(record_state);
      fprintf(stderr, "failed to decrypt application-data response record\n");
      c->application_ready = false;
      return false;
    }

    uint8_t inner_content_type = 0;
    size_t response_len = 0;
    if (!tls13_wire_decode_inner_plaintext(
            inner_plaintext, inner_plaintext_len, &inner_content_type, &response_len)) {
      TLS13_Record_record_state_free(record_state);
      fprintf(stderr, "failed to decode application-data response record\n");
      c->application_ready = false;
      return false;
    }
    if (inner_content_type == 22) {
      continue;
    }
    if (inner_content_type != 23 || response_len > len - received) {
      TLS13_Record_record_state_free(record_state);
      fprintf(stderr, "unexpected application-data response record\n");
      c->application_ready = false;
      return false;
    }
    memcpy(out + received, inner_plaintext, response_len);
    received += response_len;
  }

  TLS13_Record_record_state_free(record_state);
  if (received != len) {
    fprintf(stderr, "OpenSSL echo application data was not received\n");
    c->application_ready = false;
    return false;
  }
  return true;
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
  c->application_ready = false;
  return true;
}
#endif
