#include "tls13_io_karamel.h"

#include "tls13_io_stubs.h"

#include <stdlib.h>
#include <string.h>

#ifndef FStar_Pervasives_Native_None
#define FStar_Pervasives_Native_None 0
#endif

#ifndef FStar_Pervasives_Native_Some
#define FStar_Pervasives_Native_Some 1
#endif

struct TLS13_IO_channel_s {
  int fd;
};

struct option__TLS13_IO_channel_s {
  uint8_t tag;
  TLS13_IO_channel v;
};

TLS13_IO_channel tls13_io_channel_from_fd(int fd) {
  TLS13_IO_channel ch = malloc(sizeof *ch);
  if (ch == NULL) {
    return NULL;
  }
  ch->fd = fd;
  return ch;
}

void tls13_io_channel_free(TLS13_IO_channel ch) {
  free(ch);
}

option__TLS13_IO_channel TLS13_IO_connect_tcp(
    uint8_t *hostname,
    size_t hostname_len,
    uint16_t port,
    void *hostname_bytes) {
  (void)hostname_bytes;
  if (hostname == NULL || hostname_len == SIZE_MAX) {
    return (option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  char *host = malloc(hostname_len + 1u);
  if (host == NULL) {
    return (option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  memcpy(host, hostname, hostname_len);
  host[hostname_len] = '\0';
  int fd = tls13_io_connect_tcp(host, port);
  free(host);
  if (fd < 0) {
    return (option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  TLS13_IO_channel ch = tls13_io_channel_from_fd(fd);
  if (ch == NULL) {
    (void)tls13_io_close_fd(fd);
    return (option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  return (option__TLS13_IO_channel){
      .tag = FStar_Pervasives_Native_Some,
      .v = ch,
  };
}

size_t TLS13_IO_read(
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t max_len,
    void *old) {
  (void)old;
  if (ch == NULL) {
    return 0;
  }
  ssize_t n = tls13_io_read_fd(ch->fd, out, max_len);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

size_t TLS13_IO_write(
    TLS13_IO_channel ch,
    uint8_t *buf,
    size_t len,
    void *bytes) {
  (void)bytes;
  if (ch == NULL) {
    return 0;
  }
  ssize_t n = tls13_io_write_fd(ch->fd, buf, len);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

void TLS13_IO_close(TLS13_IO_channel ch) {
  if (ch == NULL) {
    return;
  }
  if (ch->fd >= 0) {
    (void)tls13_io_close_fd(ch->fd);
  }
  free(ch);
}
