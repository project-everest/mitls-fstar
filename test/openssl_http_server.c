#include <arpa/inet.h>
#include <netinet/in.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

static int make_listener(uint16_t requested_port, uint16_t *actual_port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    perror("socket");
    return -1;
  }
  int one = 1;
  if (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one) != 0) {
    perror("setsockopt");
    close(fd);
    return -1;
  }

  struct sockaddr_in address;
  memset(&address, 0, sizeof address);
  address.sin_family = AF_INET;
  address.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  address.sin_port = htons(requested_port);
  if (bind(fd, (struct sockaddr *)&address, sizeof address) != 0 ||
      listen(fd, 1) != 0) {
    perror("bind/listen");
    close(fd);
    return -1;
  }

  socklen_t address_len = sizeof address;
  if (getsockname(fd, (struct sockaddr *)&address, &address_len) != 0) {
    perror("getsockname");
    close(fd);
    return -1;
  }
  *actual_port = ntohs(address.sin_port);
  return fd;
}

int main(int argc, char **argv) {
  static const char response[] =
      "HTTP/1.1 200 OK\r\n"
      "Content-Length: 23\r\n"
      "Connection: close\r\n"
      "\r\n"
      "verified chromium demo\n";
  if (argc != 5) {
    fprintf(stderr, "usage: %s PORT CERT_PEM KEY_PEM PORT_FILE\n", argv[0]);
    return 1;
  }

  char *end = NULL;
  long port_long = strtol(argv[1], &end, 10);
  if (end == argv[1] || *end != '\0' || port_long < 0 ||
      port_long > 65535) {
    fprintf(stderr, "invalid port\n");
    return 1;
  }

  SSL_CTX *context = SSL_CTX_new(TLS_server_method());
  SSL *ssl = NULL;
  int listener = -1;
  int client = -1;
  int result = 1;
  if (context == NULL ||
      SSL_CTX_set_min_proto_version(context, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_max_proto_version(context, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_ciphersuites(
          context,
          "TLS_CHACHA20_POLY1305_SHA256") != 1 ||
      SSL_CTX_set1_groups_list(context, "X25519") != 1 ||
      SSL_CTX_use_certificate_file(context, argv[2], SSL_FILETYPE_PEM) != 1 ||
      SSL_CTX_use_PrivateKey_file(context, argv[3], SSL_FILETYPE_PEM) != 1 ||
      SSL_CTX_check_private_key(context) != 1) {
    ERR_print_errors_fp(stderr);
    goto done;
  }

  uint16_t actual_port = 0u;
  listener = make_listener((uint16_t)port_long, &actual_port);
  if (listener < 0) {
    goto done;
  }
  FILE *port_file = fopen(argv[4], "w");
  if (port_file == NULL) {
    perror("fopen");
    goto done;
  }
  fprintf(port_file, "%u\n", actual_port);
  fclose(port_file);

  client = accept(listener, NULL, NULL);
  ssl = SSL_new(context);
  if (client < 0 || ssl == NULL || SSL_set_fd(ssl, client) != 1 ||
      SSL_accept(ssl) != 1) {
    ERR_print_errors_fp(stderr);
    goto done;
  }

  uint8_t request[16384];
  size_t request_len = 0u;
  bool complete = false;
  while (!complete && request_len < sizeof request) {
    int read_len =
        SSL_read(ssl, request + request_len, sizeof request - request_len);
    if (read_len <= 0) {
      ERR_print_errors_fp(stderr);
      goto done;
    }
    request_len += (size_t)read_len;
    for (size_t i = 0u; !complete && i + 4u <= request_len; ++i) {
      complete = memcmp(request + i, "\r\n\r\n", 4u) == 0;
    }
  }
  if (!complete || request_len < strlen("GET / HTTP/1.1\r\n") ||
      memcmp(request, "GET / HTTP/1.1\r\n", strlen("GET / HTTP/1.1\r\n")) !=
          0) {
    fprintf(stderr, "invalid HTTP request\n");
    goto done;
  }

  size_t written = 0u;
  while (written < sizeof response - 1u) {
    int write_len = SSL_write(
        ssl,
        response + written,
        sizeof response - 1u - written);
    if (write_len <= 0) {
      ERR_print_errors_fp(stderr);
      goto done;
    }
    written += (size_t)write_len;
  }
  (void)SSL_shutdown(ssl);
  result = 0;

done:
  SSL_free(ssl);
  if (client >= 0) {
    close(client);
  }
  if (listener >= 0) {
    close(listener);
  }
  SSL_CTX_free(context);
  return result;
}
