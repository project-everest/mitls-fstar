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
  uint8_t fragment[4096];
  uint8_t content_type = 0;
  uint16_t legacy_version = 0;
  uint16_t fragment_len = 0;
  uint8_t server_random[32];
  uint8_t server_key_share[32];

  if (write_all(fd, record, record_len) != 0) {
    perror("write ClientHello");
    goto done;
  }
  if (read_exact(fd, header, sizeof header) != 0) {
    perror("read ServerHello header");
    goto done;
  }
  if (!tls13_wire_parse_record_header(
          header, sizeof header, &content_type, &legacy_version, &fragment_len) ||
      content_type != 22 || fragment_len > sizeof fragment) {
    fprintf(stderr, "bad ServerHello record header\n");
    goto done;
  }
  if (read_exact(fd, fragment, fragment_len) != 0) {
    perror("read ServerHello fragment");
    goto done;
  }
  if (!tls13_wire_parse_supported_server_hello(
          fragment, fragment_len, server_random, server_key_share)) {
    fprintf(stderr, "failed to parse supported OpenSSL ServerHello\n");
    goto done;
  }

  printf("ClientHello/OpenSSL ServerHello probe passed\n");
  rc = 0;

done:
  tls13_io_close_fd(fd);
  return rc;
}
