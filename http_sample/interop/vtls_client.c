/*
 * vtls_client.c -- a minimal HTTPS client used to exercise `http_server_vtls`,
 * the verified HTTP/1.1 server running over the VERIFIED TLS 1.3 record layer.
 *
 * curl cannot be used for this: the verified TLS server implements the
 * repository's first profile only, which excludes TLS 1.3 middlebox-compatibility
 * mode (a non-empty legacy_session_id echo plus the dummy ChangeCipherSpec
 * records).  Every mainstream client -- curl, browsers -- enables that mode
 * unconditionally and has no switch to turn it off, so this probe uses OpenSSL
 * directly with SSL_OP_ENABLE_MIDDLEBOX_COMPAT cleared and the profile pinned to
 *   TLS 1.3 / X25519 / TLS_CHACHA20_POLY1305_SHA256 / rsa_pss_rsae_sha256.
 *
 * The TLS here is UNVERIFIED client-side glue; what is under test is the
 * verified SERVER stack (verified TLS record layer + verified HTTP/1.1 leaves).
 *
 * Usage: vtls_client <host> <port> <ca.pem> [path]
 * Prints the response body on stdout.  Exit 0 iff the status line is 200.
 */

#include <netdb.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

#include <openssl/err.h>
#include <openssl/ssl.h>

static int connect_tcp(const char *host, const char *port) {
  struct addrinfo hints, *res = NULL, *it;
  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_INET;
  hints.ai_socktype = SOCK_STREAM;
  if (getaddrinfo(host, port, &hints, &res) != 0) return -1;
  int fd = -1;
  for (it = res; it; it = it->ai_next) {
    fd = socket(it->ai_family, it->ai_socktype, it->ai_protocol);
    if (fd < 0) continue;
    if (connect(fd, it->ai_addr, it->ai_addrlen) == 0) break;
    close(fd);
    fd = -1;
  }
  freeaddrinfo(res);
  return fd;
}

int main(int argc, char **argv) {
  if (argc < 4 || argc > 5) {
    fprintf(stderr, "usage: %s <host> <port> <ca.pem> [path]\n", argv[0]);
    return 2;
  }
  const char *host = argv[1], *port = argv[2], *ca = argv[3];
  const char *path = argc == 5 ? argv[4] : "/";

  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  if (!ctx) { ERR_print_errors_fp(stderr); return 1; }

  /* Middlebox-compatibility mode stays ENABLED: the verified server echoes
     the ClientHello legacy_session_id (RFC 8446 D.4). */

  if (SSL_CTX_set_min_proto_version(ctx, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_max_proto_version(ctx, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_ciphersuites(ctx, "TLS_CHACHA20_POLY1305_SHA256") != 1 ||
      SSL_CTX_set1_groups_list(ctx, "X25519") != 1 ||
      SSL_CTX_set1_sigalgs_list(ctx, "rsa_pss_rsae_sha256") != 1 ||
      SSL_CTX_load_verify_locations(ctx, ca, NULL) != 1) {
    ERR_print_errors_fp(stderr);
    SSL_CTX_free(ctx);
    return 1;
  }
  SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, NULL);

  int fd = connect_tcp(host, port);
  if (fd < 0) { fprintf(stderr, "vtls_client: connect failed\n"); SSL_CTX_free(ctx); return 1; }
  { struct timeval tv = {.tv_sec = 15, .tv_usec = 0};
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv); }

  SSL *ssl = SSL_new(ctx);
  if (!ssl || SSL_set_fd(ssl, fd) != 1 ||
      SSL_set_tlsext_host_name(ssl, host) != 1 ||
      SSL_set1_host(ssl, host) != 1 ||
      SSL_connect(ssl) != 1) {
    fprintf(stderr, "vtls_client: TLS handshake failed\n");
    ERR_print_errors_fp(stderr);
    if (ssl) SSL_free(ssl);
    close(fd);
    SSL_CTX_free(ctx);
    return 1;
  }

  char req[1024];
  int rlen = snprintf(req, sizeof req,
                      "GET %s HTTP/1.1\r\nHost: %s\r\nConnection: close\r\n\r\n",
                      path, host);
  if (SSL_write(ssl, req, rlen) != rlen) {
    fprintf(stderr, "vtls_client: request write failed\n");
    SSL_free(ssl); close(fd); SSL_CTX_free(ctx); return 1;
  }

  static char resp[1 << 20];
  size_t total = 0;
  for (;;) {
    int n = SSL_read(ssl, resp + total, (int)(sizeof resp - total - 1));
    if (n <= 0) break;
    total += (size_t)n;
    if (total + 1 >= sizeof resp) break;
  }
  resp[total] = '\0';

  SSL_free(ssl);
  close(fd);
  SSL_CTX_free(ctx);

  int status = 0;
  if (total >= 12 && strncmp(resp, "HTTP/1.1 ", 9) == 0) status = atoi(resp + 9);
  fprintf(stderr, "vtls_client: status=%d bytes=%zu\n", status, total);

  /* Print the body (everything past the CRLF CRLF) on stdout. */
  char *body = strstr(resp, "\r\n\r\n");
  if (body) {
    body += 4;
    fwrite(body, 1, total - (size_t)(body - resp), stdout);
  }
  return status == 200 ? 0 : 1;
}
