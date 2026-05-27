#include "tls13_connection_backend.h"
#include "tls13_io_stubs.h"
#include "tls13_openssl_stubs.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct TLS13_Connection_Backend_connection_s {
  char *host;
  uint16_t port;
  char *ca_pem_path;
  int fd;
  tls13_peer_identity *peer;
};

struct TLS13_IO_channel_s {
  int unused;
};

static char *dup_cstr(const char *src) {
  if (src == NULL) {
    return NULL;
  }
  size_t len = strlen(src);
  char *dst = malloc(len + 1u);
  if (dst != NULL) {
    memcpy(dst, src, len + 1u);
  }
  return dst;
}

static char *dup_hostname(const uint8_t *hostname, size_t hostname_len) {
  if (hostname == NULL || hostname_len == 0) {
    errno = EINVAL;
    return NULL;
  }
  char *host = malloc(hostname_len + 1u);
  if (host == NULL) {
    return NULL;
  }
  memcpy(host, hostname, hostname_len);
  host[hostname_len] = '\0';
  return host;
}

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

static void backend_drop_peer(TLS13_Connection_Backend_connection c) {
  if (c != NULL && c->peer != NULL) {
    tls13_openssl_peer_identity_free(c->peer);
    c->peer = NULL;
  }
}

static void backend_close_fd(TLS13_Connection_Backend_connection c) {
  if (c != NULL && c->fd >= 0) {
    tls13_io_close_fd(c->fd);
    c->fd = -1;
  }
}

static void backend_fail(TLS13_Connection_Backend_connection c) {
  backend_close_fd(c);
}

TLS13_Connection_Backend_connection TLS13_Connection_Backend_client_new(
    uint8_t *hostname,
    size_t hostname_len,
    TLS13_Connection_Backend_config cfg,
    void *hostname_bytes) {
  (void)hostname_bytes;
  if (cfg == NULL || cfg->port == 0 || cfg->ca_pem_path == NULL) {
    errno = EINVAL;
    return NULL;
  }

  TLS13_Connection_Backend_connection c = calloc(1, sizeof *c);
  if (c == NULL) {
    return NULL;
  }
  c->host = dup_hostname(hostname, hostname_len);
  c->ca_pem_path = dup_cstr(cfg->ca_pem_path);
  if (c->host == NULL || c->ca_pem_path == NULL) {
    free(c->host);
    free(c->ca_pem_path);
    free(c);
    return NULL;
  }
  c->port = cfg->port;
  c->fd = -1;
  return c;
}

void TLS13_Connection_Backend_client_free(
    TLS13_Connection_Backend_connection c,
    void *raw) {
  (void)raw;
  if (c == NULL) {
    return;
  }
  backend_close_fd(c);
  backend_drop_peer(c);
  free(c->ca_pem_path);
  free(c->host);
  free(c);
}

bool TLS13_Connection_Backend_connect(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    void *raw) {
  (void)ch;
  (void)raw;
  if (c == NULL || c->fd >= 0) {
    return false;
  }
  c->fd = tls13_io_connect_tcp(c->host, c->port);
  if (c->fd < 0) {
    perror("connect");
    backend_fail(c);
    return false;
  }
  return true;
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
  (void)buf_bytes;
  (void)raw;
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

bool TLS13_Connection_Backend_validate_certificate(
    TLS13_Connection_Backend_connection c,
    uint8_t *leaf_der,
    size_t leaf_der_capacity,
    size_t leaf_der_len,
    void *leaf_der_bytes,
    void *raw) {
  (void)leaf_der_bytes;
  (void)raw;
  if (c == NULL || leaf_der == NULL || leaf_der_len > leaf_der_capacity ||
      c->ca_pem_path == NULL || c->host == NULL) {
    backend_fail(c);
    return false;
  }

  size_t ca_pem_len = 0;
  uint8_t *ca_pem = read_file(c->ca_pem_path, &ca_pem_len);
  if (ca_pem == NULL) {
    backend_fail(c);
    return false;
  }

  tls13_peer_identity *peer = NULL;
  bool ok = tls13_openssl_validate_leaf_der(
      c->host, ca_pem, ca_pem_len, leaf_der, leaf_der_len, &peer);
  free(ca_pem);
  if (!ok || peer == NULL) {
    fprintf(stderr, "failed to validate server certificate\n");
    if (peer != NULL) {
      tls13_openssl_peer_identity_free(peer);
    }
    backend_fail(c);
    return false;
  }

  backend_drop_peer(c);
  c->peer = peer;
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
  (void)input_bytes;
  (void)signature_bytes;
  (void)raw;
  if (c == NULL || c->peer == NULL ||
      certificate_verify_input == NULL || certificate_verify_input_len != 130 ||
      signature == NULL || signature_len > signature_capacity) {
    backend_fail(c);
    return false;
  }

  bool ok = tls13_openssl_peer_verify_signature(
      c->peer,
      signature_scheme,
      certificate_verify_input,
      certificate_verify_input_len,
      signature,
      signature_len);
  if (!ok) {
    fprintf(stderr, "failed to verify server CertificateVerify\n");
    backend_fail(c);
  }
  return ok;
}

bool TLS13_Connection_Backend_close(
    TLS13_Connection_Backend_connection c,
    TLS13_IO_channel ch,
    void *raw) {
  (void)ch;
  (void)raw;
  if (c == NULL) {
    return false;
  }
  backend_close_fd(c);
  return true;
}
