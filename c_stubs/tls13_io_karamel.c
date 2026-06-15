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

struct TLS13_IO_listener_s {
  int fd;
};

typedef struct FStar_Pervasives_Native_option__TLS13_IO_channel_s {
  uint8_t tag;
  TLS13_IO_channel v;
} FStar_Pervasives_Native_option__TLS13_IO_channel;

typedef struct FStar_Pervasives_Native_option__TLS13_IO_listener_s {
  uint8_t tag;
  TLS13_IO_listener v;
} FStar_Pervasives_Native_option__TLS13_IO_listener;

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

static TLS13_IO_listener tls13_io_listener_from_fd(int fd) {
  TLS13_IO_listener l = malloc(sizeof *l);
  if (l == NULL) {
    return NULL;
  }
  l->fd = fd;
  return l;
}

FStar_Pervasives_Native_option__TLS13_IO_channel TLS13_IO_connect_tcp(
    uint8_t *hostname,
    size_t hostname_len,
    uint16_t port) {
  if (hostname == NULL || hostname_len == SIZE_MAX) {
    return (FStar_Pervasives_Native_option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  char *host = malloc(hostname_len + 1u);
  if (host == NULL) {
    return (FStar_Pervasives_Native_option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  memcpy(host, hostname, hostname_len);
  host[hostname_len] = '\0';
  int fd = tls13_io_connect_tcp(host, port);
  free(host);
  if (fd < 0) {
    return (FStar_Pervasives_Native_option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  TLS13_IO_channel ch = tls13_io_channel_from_fd(fd);
  if (ch == NULL) {
    (void)tls13_io_close_fd(fd);
    return (FStar_Pervasives_Native_option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__TLS13_IO_channel){
      .tag = FStar_Pervasives_Native_Some,
      .v = ch,
  };
}

FStar_Pervasives_Native_option__TLS13_IO_listener TLS13_IO_listen_tcp(
    uint8_t *bind_host,
    size_t bind_host_len,
    uint16_t port) {
  if (bind_host == NULL || bind_host_len == SIZE_MAX) {
    return (FStar_Pervasives_Native_option__TLS13_IO_listener){.tag = FStar_Pervasives_Native_None};
  }
  char *host = malloc(bind_host_len + 1u);
  if (host == NULL) {
    return (FStar_Pervasives_Native_option__TLS13_IO_listener){.tag = FStar_Pervasives_Native_None};
  }
  memcpy(host, bind_host, bind_host_len);
  host[bind_host_len] = '\0';
  int fd = tls13_io_listen_tcp(host, port);
  free(host);
  if (fd < 0) {
    return (FStar_Pervasives_Native_option__TLS13_IO_listener){.tag = FStar_Pervasives_Native_None};
  }
  TLS13_IO_listener l = tls13_io_listener_from_fd(fd);
  if (l == NULL) {
    (void)tls13_io_close_fd(fd);
    return (FStar_Pervasives_Native_option__TLS13_IO_listener){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__TLS13_IO_listener){
      .tag = FStar_Pervasives_Native_Some,
      .v = l,
  };
}

FStar_Pervasives_Native_option__TLS13_IO_channel TLS13_IO_accept_tcp(
    TLS13_IO_listener l) {
  if (l == NULL) {
    return (FStar_Pervasives_Native_option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  int fd = tls13_io_accept_tcp(l->fd);
  if (fd < 0) {
    return (FStar_Pervasives_Native_option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  TLS13_IO_channel ch = tls13_io_channel_from_fd(fd);
  if (ch == NULL) {
    (void)tls13_io_close_fd(fd);
    return (FStar_Pervasives_Native_option__TLS13_IO_channel){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__TLS13_IO_channel){
      .tag = FStar_Pervasives_Native_Some,
      .v = ch,
  };
}

void TLS13_IO_close_listener(TLS13_IO_listener l) {
  if (l == NULL) {
    return;
  }
  if (l->fd >= 0) {
    (void)tls13_io_close_fd(l->fd);
  }
  free(l);
}

size_t TLS13_IO_read(
    TLS13_IO_channel ch,
    uint8_t *out,
    size_t max_len) {
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
    size_t len) {
  if (ch == NULL) {
    return 0;
  }
  size_t off = 0;
  while (off < len) {
    ssize_t n = tls13_io_write_fd(ch->fd, buf + off, len - off);
    if (n <= 0) {
      return off;
    }
    off += (size_t)n;
  }
  return off;
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
