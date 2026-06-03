#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
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

  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = htons(requested_port);

  if (bind(fd, (struct sockaddr *)&addr, sizeof addr) != 0) {
    perror("bind");
    close(fd);
    return -1;
  }
  if (listen(fd, 1) != 0) {
    perror("listen");
    close(fd);
    return -1;
  }

  socklen_t len = sizeof addr;
  if (getsockname(fd, (struct sockaddr *)&addr, &len) != 0) {
    perror("getsockname");
    close(fd);
    return -1;
  }
  *actual_port = ntohs(addr.sin_port);
  return fd;
}

int main(int argc, char **argv) {
  if (argc != 4 && argc != 5) {
    fprintf(stderr, "usage: %s PORT CERT_PEM KEY_PEM [PORT_FILE]\n", argv[0]);
    return 1;
  }

  long port_long = strtol(argv[1], NULL, 10);
  if (port_long < 0 || port_long > 65535) {
    fprintf(stderr, "invalid port\n");
    return 1;
  }

  SSL_CTX *ctx = SSL_CTX_new(TLS_server_method());
  if (ctx == NULL) {
    ERR_print_errors_fp(stderr);
    return 1;
  }
  int rc = 1;
  int listen_fd = -1;
  int client_fd = -1;
  SSL *ssl = NULL;

  if (SSL_CTX_set_min_proto_version(ctx, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_max_proto_version(ctx, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_ciphersuites(ctx, "TLS_CHACHA20_POLY1305_SHA256") != 1 ||
      SSL_CTX_set1_groups_list(ctx, "X25519") != 1 ||
      SSL_CTX_use_certificate_file(ctx, argv[2], SSL_FILETYPE_PEM) != 1 ||
      SSL_CTX_use_PrivateKey_file(ctx, argv[3], SSL_FILETYPE_PEM) != 1 ||
      SSL_CTX_check_private_key(ctx) != 1) {
    ERR_print_errors_fp(stderr);
    goto done;
  }
  SSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, NULL);

  uint16_t actual_port = 0;
  listen_fd = make_listener((uint16_t)port_long, &actual_port);
  if (listen_fd < 0) {
    goto done;
  }
  printf("%u\n", actual_port);
  fflush(stdout);
  if (argc == 5) {
    FILE *port_file = fopen(argv[4], "w");
    if (port_file == NULL) {
      perror("fopen port file");
      goto done;
    }
    fprintf(port_file, "%u\n", actual_port);
    fclose(port_file);
  }

  client_fd = accept(listen_fd, NULL, NULL);
  if (client_fd < 0) {
    perror("accept");
    goto done;
  }

  ssl = SSL_new(ctx);
  if (ssl == NULL || SSL_set_fd(ssl, client_fd) != 1 || SSL_accept(ssl) != 1) {
    ERR_print_errors_fp(stderr);
    goto done;
  }

  struct timeval read_timeout = {.tv_sec = 10, .tv_usec = 0};
  if (setsockopt(client_fd, SOL_SOCKET, SO_RCVTIMEO, &read_timeout, sizeof read_timeout) != 0) {
    perror("setsockopt SO_RCVTIMEO");
    goto done;
  }

  uint8_t buf[4096];
  bool saw_data = false;
  bool requested_key_update = false;
  for (;;) {
    int n = SSL_read(ssl, buf, sizeof buf);
    if (n <= 0) {
      int err = SSL_get_error(ssl, n);
      if (err == SSL_ERROR_ZERO_RETURN || (err == SSL_ERROR_SYSCALL && errno == 0)) {
        break;
      }
      if (saw_data &&
          (err == SSL_ERROR_WANT_READ ||
           (err == SSL_ERROR_SYSCALL && (errno == EAGAIN || errno == EWOULDBLOCK)))) {
        break;
      }
      ERR_print_errors_fp(stderr);
      goto done;
    }
    saw_data = true;
    if (!requested_key_update) {
      if (SSL_key_update(ssl, SSL_KEY_UPDATE_REQUESTED) != 1 ||
          SSL_do_handshake(ssl) != 1) {
        ERR_print_errors_fp(stderr);
        goto done;
      }
      requested_key_update = true;
    }
    int written = 0;
    while (written < n) {
      int m = SSL_write(ssl, buf + written, n - written);
      if (m <= 0) {
        ERR_print_errors_fp(stderr);
        goto done;
      }
      written += m;
    }
  }

  SSL_shutdown(ssl);
  rc = 0;

done:
  SSL_free(ssl);
  if (client_fd >= 0) close(client_fd);
  if (listen_fd >= 0) close(listen_fd);
  SSL_CTX_free(ctx);
  return rc;
}
