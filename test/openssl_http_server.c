#include <arpa/inet.h>
#include <netinet/in.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

#define MAX_CONNECTION_ATTEMPTS 16
#define CLIENT_TIMEOUT_SECONDS 2

enum connection_result {
  CONNECTION_RETRY,
  CONNECTION_SERVED,
  CONNECTION_FATAL
};

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
      listen(fd, MAX_CONNECTION_ATTEMPTS) != 0) {
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

static enum connection_result serve_connection(SSL_CTX *context, int client) {
  static const char response[] =
      "HTTP/1.1 200 OK\r\n"
      "Content-Length: 23\r\n"
      "Connection: close\r\n"
      "\r\n"
      "verified chromium demo\n";

  struct timeval timeout = {
      .tv_sec = CLIENT_TIMEOUT_SECONDS,
      .tv_usec = 0,
  };
  if (setsockopt(client, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof timeout) !=
          0 ||
      setsockopt(client, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof timeout) !=
          0) {
    perror("setsockopt timeout");
    return CONNECTION_FATAL;
  }

  SSL *ssl = SSL_new(context);
  if (ssl == NULL || SSL_set_fd(ssl, client) != 1) {
    ERR_print_errors_fp(stderr);
    SSL_free(ssl);
    return CONNECTION_FATAL;
  }

  int accept_result = SSL_accept(ssl);
  if (accept_result != 1) {
    int ssl_error = SSL_get_error(ssl, accept_result);
    fprintf(stderr,
            "Ignoring incomplete TLS connection during handshake "
            "(SSL error %d)\n",
            ssl_error);
    ERR_clear_error();
    SSL_free(ssl);
    return CONNECTION_RETRY;
  }

  uint8_t request[16384];
  size_t request_len = 0u;
  bool complete = false;
  while (!complete && request_len < sizeof request) {
    int read_len =
        SSL_read(ssl, request + request_len, sizeof request - request_len);
    if (read_len <= 0) {
      int ssl_error = SSL_get_error(ssl, read_len);
      fprintf(stderr,
              "Ignoring TLS connection closed before an HTTP request "
              "(SSL error %d)\n",
              ssl_error);
      ERR_clear_error();
      SSL_free(ssl);
      return CONNECTION_RETRY;
    }
    request_len += (size_t)read_len;
    for (size_t i = 0u; !complete && i + 4u <= request_len; ++i) {
      complete = memcmp(request + i, "\r\n\r\n", 4u) == 0;
    }
  }
  if (!complete || request_len < strlen("GET / HTTP/1.1\r\n") ||
      memcmp(request, "GET / HTTP/1.1\r\n", strlen("GET / HTTP/1.1\r\n")) !=
          0) {
    fprintf(stderr, "Ignoring unsupported HTTP request\n");
    SSL_free(ssl);
    return CONNECTION_RETRY;
  }

  size_t written = 0u;
  while (written < sizeof response - 1u) {
    int write_len = SSL_write(
        ssl,
        response + written,
        sizeof response - 1u - written);
    if (write_len <= 0) {
      int ssl_error = SSL_get_error(ssl, write_len);
      fprintf(stderr,
              "TLS connection closed while writing the HTTP response "
              "(SSL error %d)\n",
              ssl_error);
      ERR_clear_error();
      SSL_free(ssl);
      return CONNECTION_RETRY;
    }
    written += (size_t)write_len;
  }
  (void)SSL_shutdown(ssl);
  SSL_free(ssl);
  return CONNECTION_SERVED;
}

int main(int argc, char **argv) {
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

  (void)signal(SIGPIPE, SIG_IGN);

  SSL_CTX *context = SSL_CTX_new(TLS_server_method());
  int listener = -1;
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

  for (unsigned attempt = 0u; attempt < MAX_CONNECTION_ATTEMPTS; ++attempt) {
    int client = accept(listener, NULL, NULL);
    if (client < 0) {
      perror("accept");
      goto done;
    }
    enum connection_result connection = serve_connection(context, client);
    close(client);
    if (connection == CONNECTION_FATAL) {
      goto done;
    }
    if (connection == CONNECTION_SERVED) {
      result = 0;
      goto done;
    }
  }
  fprintf(stderr, "Too many incomplete TLS connections\n");

done:
  if (listener >= 0) {
    close(listener);
  }
  SSL_CTX_free(context);
  return result;
}
