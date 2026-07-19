#include "tls13_server_driver.h"

#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <unistd.h>

static int read_file(const char *path, uint8_t **out, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    perror(path);
    return 1;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    perror("fseek");
    fclose(f);
    return 1;
  }
  long len = ftell(f);
  if (len < 0) {
    perror("ftell");
    fclose(f);
    return 1;
  }
  rewind(f);
  uint8_t *buf = calloc((size_t)len == 0u ? 1u : (size_t)len, sizeof(uint8_t));
  if (buf == NULL) {
    fclose(f);
    return 1;
  }
  if (fread(buf, 1u, (size_t)len, f) != (size_t)len) {
    perror("fread");
    free(buf);
    fclose(f);
    return 1;
  }
  fclose(f);
  *out = buf;
  *out_len = (size_t)len;
  return 0;
}

static int reserve_loopback_port(uint16_t *port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) {
    perror("socket");
    return -1;
  }
  int one = 1;
  (void)setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = htons(0);
  if (bind(fd, (struct sockaddr *)&addr, sizeof addr) != 0) {
    perror("bind");
    close(fd);
    return -1;
  }
  socklen_t len = sizeof addr;
  if (getsockname(fd, (struct sockaddr *)&addr, &len) != 0) {
    perror("getsockname");
    close(fd);
    return -1;
  }
  *port = ntohs(addr.sin_port);
  close(fd);
  return 0;
}

static int connect_with_retry(uint16_t port) {
  for (unsigned attempt = 0; attempt < 100u; ++attempt) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) {
      return -1;
    }
    struct sockaddr_in addr;
    memset(&addr, 0, sizeof addr);
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = htons(port);
    if (connect(fd, (struct sockaddr *)&addr, sizeof addr) == 0) {
      return fd;
    }
    close(fd);
    usleep(50000u);
  }
  return -1;
}

struct tls_msg_trace {
  int last_write_content_type;
  int last_write_detail;
  size_t last_write_len;
  int last_read_content_type;
  int last_read_detail;
  size_t last_read_len;
};

static void trace_tls_msg(
    int write_p,
    int version,
    int content_type,
    const void *buf,
    size_t len,
    SSL *ssl,
    void *arg) {
  (void)version;
  (void)ssl;
  struct tls_msg_trace *trace = (struct tls_msg_trace *)arg;
  if (trace == NULL) {
    return;
  }
  int detail = -1;
  if (buf != NULL && len > 0u &&
      (content_type == SSL3_RT_HANDSHAKE || content_type == SSL3_RT_ALERT)) {
    detail = ((const uint8_t *)buf)[content_type == SSL3_RT_ALERT && len > 1u ? 1u : 0u];
  }
  if (write_p) {
    trace->last_write_content_type = content_type;
    trace->last_write_detail = detail;
    trace->last_write_len = len;
  } else {
    trace->last_read_content_type = content_type;
    trace->last_read_detail = detail;
    trace->last_read_len = len;
  }
}

static void print_tls_msg_trace(const struct tls_msg_trace *trace) {
  if (trace == NULL) {
    return;
  }
  fprintf(
      stderr,
      "OpenSSL TLS trace: last_write ct=%d detail=%d len=%zu; last_read ct=%d detail=%d len=%zu\n",
      trace->last_write_content_type,
      trace->last_write_detail,
      trace->last_write_len,
      trace->last_read_content_type,
      trace->last_read_detail,
      trace->last_read_len);
}

static int run_extracted_server(
    uint16_t port,
    const uint8_t *certificate_chain,
    size_t certificate_chain_len,
    const uint8_t *private_key,
    size_t private_key_len) {
  alarm(20);
  tls13_server_driver *server = NULL;
  static const uint8_t expected[] = {'p', 'i', 'n', 'g'};
  uint8_t received[TLS13_SERVER_DRIVER_RECEIVE_BUFFER_SIZE] = {0};
  size_t received_len = 0;
  int rc = 1;

  if (tls13_server_driver_accept(
          &server,
          "127.0.0.1",
          port,
          certificate_chain,
          certificate_chain_len,
          private_key,
          private_key_len) == 0 &&
      tls13_server_driver_receive_application_data(
          server,
          received,
          sizeof received,
          &received_len) == 0 &&
      received_len == sizeof expected &&
      memcmp(received, expected, sizeof expected) == 0 &&
      tls13_server_driver_send_application_data(server, received, received_len) == 0 &&
      tls13_server_driver_close(server, false) == 0) {
    rc = 0;
  } else if (server != NULL) {
    fprintf(stderr, "extracted server failed: %s\n", tls13_server_driver_last_error(server));
  } else {
    fprintf(stderr, "extracted server failed during accept\n");
  }

  tls13_server_driver_free(server);
  return rc;
}

static int run_openssl_client(uint16_t port, const char *ca_path) {
  alarm(20);
  SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
  if (ctx == NULL) {
    ERR_print_errors_fp(stderr);
    return 1;
  }
  SSL_CTX_clear_options(ctx, SSL_OP_ENABLE_MIDDLEBOX_COMPAT);
  int rc = 1;
  int fd = -1;
  SSL *ssl = NULL;
  struct tls_msg_trace trace = {
      .last_write_content_type = -1,
      .last_write_detail = -1,
      .last_write_len = 0,
      .last_read_content_type = -1,
      .last_read_detail = -1,
      .last_read_len = 0,
  };
  SSL_CTX_set_msg_callback(ctx, trace_tls_msg);
  SSL_CTX_set_msg_callback_arg(ctx, &trace);

  if (SSL_CTX_set_min_proto_version(ctx, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_max_proto_version(ctx, TLS1_3_VERSION) != 1 ||
      SSL_CTX_set_ciphersuites(ctx, "TLS_CHACHA20_POLY1305_SHA256") != 1 ||
      SSL_CTX_set1_groups_list(ctx, "X25519") != 1 ||
      SSL_CTX_set1_sigalgs_list(ctx, "rsa_pss_rsae_sha256") != 1 ||
      SSL_CTX_load_verify_locations(ctx, ca_path, NULL) != 1) {
    ERR_print_errors_fp(stderr);
    goto done;
  }
  SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, NULL);

  fd = connect_with_retry(port);
  if (fd < 0) {
    perror("connect");
    goto done;
  }
  struct timeval timeout = {.tv_sec = 10, .tv_usec = 0};
  (void)setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof timeout);
  (void)setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof timeout);

  ssl = SSL_new(ctx);
  if (ssl == NULL ||
      SSL_set_fd(ssl, fd) != 1 ||
      SSL_set_tlsext_host_name(ssl, "localhost") != 1 ||
      SSL_set1_host(ssl, "localhost") != 1 ||
      SSL_connect(ssl) != 1) {
    ERR_print_errors_fp(stderr);
    print_tls_msg_trace(&trace);
    goto done;
  }

  static const uint8_t ping[] = {'p', 'i', 'n', 'g'};
  uint8_t received[sizeof ping] = {0};
  if (SSL_write(ssl, ping, sizeof ping) != (int)sizeof ping) {
    ERR_print_errors_fp(stderr);
    goto done;
  }
  int n = SSL_read(ssl, received, sizeof received);
  if (n != (int)sizeof ping || memcmp(received, ping, sizeof ping) != 0) {
    ERR_print_errors_fp(stderr);
    goto done;
  }

  (void)SSL_shutdown(ssl);
  rc = 0;

done:
  SSL_free(ssl);
  if (fd >= 0) {
    close(fd);
  }
  SSL_CTX_free(ctx);
  return rc;
}

int main(void) {
  uint8_t *certificate_chain = NULL;
  uint8_t *private_key = NULL;
  size_t certificate_chain_len = 0;
  size_t private_key_len = 0;
  uint16_t port = 0;
  int rc = 1;

  if (read_file("test/certs/leaf.der", &certificate_chain, &certificate_chain_len) != 0 ||
      read_file("test/certs/leaf.key", &private_key, &private_key_len) != 0 ||
      reserve_loopback_port(&port) != 0) {
    goto done;
  }

  pid_t child = fork();
  if (child < 0) {
    perror("fork");
    goto done;
  }
  if (child == 0) {
    int child_rc =
        run_extracted_server(port, certificate_chain, certificate_chain_len, private_key, private_key_len);
    _exit(child_rc == 0 ? 0 : 1);
  }

  int client_rc = run_openssl_client(port, "test/certs/ca.pem");
  int status = 0;
  if (waitpid(child, &status, 0) < 0) {
    perror("waitpid");
    goto done;
  }
  if (client_rc == 0 && WIFEXITED(status) && WEXITSTATUS(status) == 0) {
    printf("extracted server OpenSSL client interop test passed\n");
    rc = 0;
  } else {
    fprintf(stderr, "extracted server OpenSSL client interop test failed\n");
  }

done:
  free(certificate_chain);
  free(private_key);
  return rc;
}
