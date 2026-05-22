#include "tls13_hacl_stubs.h"
#include "tls13_io_stubs.h"
#include "tls13_wire_stubs.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int write_all(int fd, const uint8_t *buf, size_t len) {
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

static int read_exact(int fd, uint8_t *buf, size_t len) {
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
  if (read_exact(fd, header, TLS13_WIRE_RECORD_HEADER_LEN) != 0) {
    return -1;
  }
  if (!tls13_wire_parse_record_header(
          header, TLS13_WIRE_RECORD_HEADER_LEN, content_type, legacy_version, fragment_len) ||
      *fragment_len > fragment_capacity) {
    return -1;
  }
  return read_exact(fd, fragment, *fragment_len);
}

static int derive_server_handshake_keys(
    const uint8_t *client_hello,
    size_t client_hello_len,
    const uint8_t *server_hello,
    size_t server_hello_len,
    const uint8_t server_key_share[32],
    uint8_t server_handshake_traffic_secret[32],
    uint8_t server_key[32],
    uint8_t server_iv[12]) {
  static const uint8_t client_private_key[32] = {
      0x49, 0xaf, 0x42, 0xba, 0x7f, 0x79, 0x94, 0x85,
      0x2d, 0x71, 0x3e, 0xf2, 0x78, 0x4b, 0xcb, 0xca,
      0xa7, 0x91, 0x1d, 0xe2, 0x6a, 0xdc, 0x56, 0x42,
      0xcb, 0x63, 0x45, 0x40, 0xe7, 0xea, 0x50, 0x05};
  static const uint8_t zero_secret[32] = {0};
  static const uint8_t label_derived[] = {'d', 'e', 'r', 'i', 'v', 'e', 'd'};
  static const uint8_t label_s_hs_traffic[] = {
      's', ' ', 'h', 's', ' ', 't', 'r', 'a', 'f', 'f', 'i', 'c'};
  static const uint8_t label_key[] = {'k', 'e', 'y'};
  static const uint8_t label_iv[] = {'i', 'v'};

  uint8_t empty_hash[32];
  uint8_t early_secret[32];
  uint8_t derived_secret[32];
  uint8_t shared_secret[32];
  uint8_t handshake_secret[32];
  uint8_t transcript[1024];
  uint8_t transcript_hash[32];

  if (client_hello_len > sizeof transcript ||
      server_hello_len > sizeof transcript - client_hello_len) {
    return -1;
  }
  if (!tls13_hacl_sha256(empty_hash, NULL, 0) ||
      !tls13_hacl_hkdf_extract_sha256(
          early_secret, NULL, 0, zero_secret, sizeof zero_secret) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          derived_secret,
          sizeof derived_secret,
          early_secret,
          label_derived,
          sizeof label_derived,
          empty_hash,
          sizeof empty_hash) ||
      !tls13_hacl_x25519_shared(shared_secret, client_private_key, server_key_share) ||
      !tls13_hacl_hkdf_extract_sha256(
          handshake_secret,
          derived_secret,
          sizeof derived_secret,
          shared_secret,
          sizeof shared_secret)) {
    return -1;
  }

  memcpy(transcript, client_hello, client_hello_len);
  memcpy(transcript + client_hello_len, server_hello, server_hello_len);
  if (!tls13_hacl_sha256(transcript_hash, transcript, client_hello_len + server_hello_len) ||
      !tls13_hacl_hkdf_expand_label_sha256(
          server_handshake_traffic_secret,
          32,
          handshake_secret,
          label_s_hs_traffic,
          sizeof label_s_hs_traffic,
          transcript_hash,
          sizeof transcript_hash) ||
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
  return 0;
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
  uint8_t transcript[32768];
  uint8_t transcript_hash[32];
  uint8_t expected[32];

  if (client_hello_len > sizeof transcript ||
      server_hello_len > sizeof transcript - client_hello_len ||
      server_handshake_before_finished_len >
          sizeof transcript - client_hello_len - server_hello_len) {
    return -1;
  }
  size_t pos = 0;
  memcpy(transcript + pos, client_hello, client_hello_len);
  pos += client_hello_len;
  memcpy(transcript + pos, server_hello, server_hello_len);
  pos += server_hello_len;
  memcpy(transcript + pos, server_handshake_messages, server_handshake_before_finished_len);
  pos += server_handshake_before_finished_len;

  if (!tls13_hacl_sha256(transcript_hash, transcript, pos) ||
      !tls13_hacl_finished_verify_data_sha256(
          expected, server_handshake_traffic_secret, transcript_hash)) {
    return -1;
  }
  return memcmp(expected, finished_verify_data, 32) == 0 ? 0 : -1;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s HOST PORT\n", argv[0]);
    return 1;
  }

  char *end = NULL;
  long port_long = strtol(argv[2], &end, 10);
  if (*argv[2] == '\0' || *end != '\0' || port_long <= 0 || port_long > 65535) {
    fprintf(stderr, "invalid port\n");
    return 1;
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

  uint8_t client_hello[512];
  size_t client_hello_len = 0;
  if (!tls13_wire_serialize_supported_client_hello(
          client_hello,
          sizeof client_hello,
          random,
          key_share,
          hostname,
          sizeof hostname,
          &client_hello_len)) {
    fprintf(stderr, "failed to serialize ClientHello\n");
    return 1;
  }

  uint8_t record[TLS13_WIRE_RECORD_HEADER_LEN + sizeof client_hello];
  if (!tls13_wire_serialize_record_header(
          record, 22, 0x0301, (uint16_t)client_hello_len)) {
    fprintf(stderr, "failed to serialize ClientHello record header\n");
    return 1;
  }
  memcpy(record + TLS13_WIRE_RECORD_HEADER_LEN, client_hello, client_hello_len);
  size_t record_len = TLS13_WIRE_RECORD_HEADER_LEN + client_hello_len;

  int fd = tls13_io_connect_tcp(argv[1], (uint16_t)port_long);
  if (fd < 0) {
    perror("connect");
    return 1;
  }

  int rc = 1;
  uint8_t header[TLS13_WIRE_RECORD_HEADER_LEN];
  uint8_t server_hello_fragment[4096];
  uint8_t encrypted_fragment[20000];
  uint8_t encrypted_header[TLS13_WIRE_RECORD_HEADER_LEN];
  uint8_t content_type = 0;
  uint16_t legacy_version = 0;
  uint16_t fragment_len = 0;
  uint8_t server_random[32];
  uint8_t server_key_share[32];

  if (write_all(fd, record, record_len) != 0) {
    perror("write ClientHello");
    goto done;
  }
  if (read_record(
          fd,
          header,
          server_hello_fragment,
          sizeof server_hello_fragment,
          &content_type,
          &legacy_version,
          &fragment_len) != 0 ||
      content_type != 22) {
    fprintf(stderr, "bad ServerHello record header\n");
    goto done;
  }
  if (!tls13_wire_parse_supported_server_hello(
          server_hello_fragment, fragment_len, server_random, server_key_share)) {
    fprintf(stderr, "failed to parse supported OpenSSL ServerHello\n");
    goto done;
  }
  size_t server_hello_len = fragment_len;

  uint8_t server_handshake_traffic_secret[32];
  uint8_t server_key[32];
  uint8_t server_iv[12];
  if (derive_server_handshake_keys(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_key_share,
          server_handshake_traffic_secret,
          server_key,
          server_iv) != 0) {
    fprintf(stderr, "failed to derive server handshake traffic keys\n");
    goto done;
  }

  uint8_t server_handshake_messages[32768];
  size_t server_handshake_len = 0;
  size_t parsed_handshake_len = 0;
  size_t server_handshake_before_finished_len = 0;
  uint8_t server_finished_verify_data[32];
  bool saw_finished = false;
  uint64_t server_sequence_number = 0;

  for (unsigned attempts = 0; attempts < 8 && !saw_finished; ++attempts) {
    if (read_record(
            fd,
            encrypted_header,
            encrypted_fragment,
            sizeof encrypted_fragment,
            &content_type,
            &legacy_version,
            &fragment_len) != 0) {
      fprintf(stderr, "failed to read encrypted handshake record\n");
      goto done;
    }
    if (content_type == 20 && fragment_len == 1 && encrypted_fragment[0] == 1) {
      continue;
    }
    if (content_type != 23 || fragment_len < 16) {
      fprintf(stderr, "unexpected record before server Finished: %u\n", content_type);
      goto done;
    }

    uint8_t nonce[12];
    uint8_t inner_plaintext[20000];
    size_t inner_plaintext_len = (size_t)fragment_len - 16u;
    if (!tls13_record_nonce(nonce, server_iv, server_sequence_number++) ||
        !tls13_hacl_chacha20_poly1305_open_combined(
            inner_plaintext,
            inner_plaintext_len,
            server_key,
            nonce,
            encrypted_header,
            TLS13_WIRE_RECORD_HEADER_LEN,
            encrypted_fragment,
            fragment_len)) {
      fprintf(stderr, "failed to decrypt OpenSSL encrypted handshake record\n");
      goto done;
    }

    uint8_t inner_content_type = 0;
    size_t handshake_plaintext_len = 0;
    if (!tls13_wire_decode_inner_plaintext(
            inner_plaintext, inner_plaintext_len, &inner_content_type, &handshake_plaintext_len) ||
        inner_content_type != 22 ||
        handshake_plaintext_len > sizeof server_handshake_messages - server_handshake_len) {
      fprintf(stderr, "failed to decode OpenSSL handshake inner plaintext\n");
      goto done;
    }
    memcpy(server_handshake_messages + server_handshake_len, inner_plaintext, handshake_plaintext_len);
    server_handshake_len += handshake_plaintext_len;

    while (server_handshake_len - parsed_handshake_len >= TLS13_WIRE_HANDSHAKE_HEADER_LEN) {
      uint8_t handshake_type = 0;
      uint32_t handshake_body_len = 0;
      if (!tls13_wire_parse_handshake_header(
              server_handshake_messages + parsed_handshake_len,
              server_handshake_len - parsed_handshake_len,
              &handshake_type,
              &handshake_body_len)) {
        fprintf(stderr, "failed to parse decrypted handshake header\n");
        goto done;
      }
      size_t message_len = TLS13_WIRE_HANDSHAKE_HEADER_LEN + (size_t)handshake_body_len;
      if (message_len > server_handshake_len - parsed_handshake_len) {
        break;
      }
      if (parsed_handshake_len == 0 && handshake_type != 8) {
        fprintf(stderr, "decrypted first OpenSSL handshake message is not EncryptedExtensions\n");
        goto done;
      }
      if (handshake_type == 20) {
        if (handshake_body_len != 32) {
          fprintf(stderr, "OpenSSL Finished has unexpected length\n");
          goto done;
        }
        server_handshake_before_finished_len = parsed_handshake_len;
        memcpy(
            server_finished_verify_data,
            server_handshake_messages + parsed_handshake_len + TLS13_WIRE_HANDSHAKE_HEADER_LEN,
            sizeof server_finished_verify_data);
        saw_finished = true;
        break;
      }
      parsed_handshake_len += message_len;
    }
  }

  if (!saw_finished ||
      verify_server_finished(
          client_hello,
          client_hello_len,
          server_hello_fragment,
          server_hello_len,
          server_handshake_messages,
          server_handshake_before_finished_len,
          server_finished_verify_data,
          server_handshake_traffic_secret) != 0) {
    fprintf(stderr, "failed to verify OpenSSL server Finished\n");
    goto done;
  }

  printf("ClientHello/OpenSSL server Finished probe passed\n");
  rc = 0;

done:
  tls13_io_close_fd(fd);
  return rc;
}
