#include "common_tcp_karamel.h"

#include "common_tcp_stubs.h"

#include <stdlib.h>
#include <string.h>

#ifndef FStar_Pervasives_Native_None
#define FStar_Pervasives_Native_None 0
#endif

#ifndef FStar_Pervasives_Native_Some
#define FStar_Pervasives_Native_Some 1
#endif

struct Common_TCP_channel_s {
  int fd;
};

struct Common_TCP_listener_s {
  int fd;
};

typedef struct FStar_Pervasives_Native_option__Common_TCP_channel_s {
  uint8_t tag;
  Common_TCP_channel v;
} FStar_Pervasives_Native_option__Common_TCP_channel;

typedef struct FStar_Pervasives_Native_option__Common_TCP_listener_s {
  uint8_t tag;
  Common_TCP_listener v;
} FStar_Pervasives_Native_option__Common_TCP_listener;

static Common_TCP_channel common_tcp_channel_from_fd(int fd) {
  Common_TCP_channel ch = malloc(sizeof *ch);
  if (ch == NULL) {
    return NULL;
  }
  ch->fd = fd;
  return ch;
}

Common_TCP_channel Common_TCP_channel_of_fd(int fd) {
  return common_tcp_channel_from_fd(fd);
}

static Common_TCP_listener common_tcp_listener_from_fd(int fd) {
  Common_TCP_listener l = malloc(sizeof *l);
  if (l == NULL) {
    return NULL;
  }
  l->fd = fd;
  return l;
}

FStar_Pervasives_Native_option__Common_TCP_channel Common_TCP_connect_tcp(
    uint8_t *hostname,
    size_t hostname_len,
    uint16_t port) {
  if (hostname == NULL || hostname_len == SIZE_MAX) {
    return (FStar_Pervasives_Native_option__Common_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  char *host = malloc(hostname_len + 1u);
  if (host == NULL) {
    return (FStar_Pervasives_Native_option__Common_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  memcpy(host, hostname, hostname_len);
  host[hostname_len] = '\0';
  int fd = common_tcp_connect(host, port);
  free(host);
  if (fd < 0) {
    return (FStar_Pervasives_Native_option__Common_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  Common_TCP_channel ch = common_tcp_channel_from_fd(fd);
  if (ch == NULL) {
    (void)common_tcp_close_fd(fd);
    return (FStar_Pervasives_Native_option__Common_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__Common_TCP_channel){
      .tag = FStar_Pervasives_Native_Some,
      .v = ch,
  };
}

FStar_Pervasives_Native_option__Common_TCP_listener Common_TCP_listen_tcp(
    uint8_t *bind_host,
    size_t bind_host_len,
    uint16_t port) {
  if (bind_host == NULL || bind_host_len == SIZE_MAX) {
    return (FStar_Pervasives_Native_option__Common_TCP_listener){.tag = FStar_Pervasives_Native_None};
  }
  char *host = malloc(bind_host_len + 1u);
  if (host == NULL) {
    return (FStar_Pervasives_Native_option__Common_TCP_listener){.tag = FStar_Pervasives_Native_None};
  }
  memcpy(host, bind_host, bind_host_len);
  host[bind_host_len] = '\0';
  int fd = common_tcp_listen(host, port);
  free(host);
  if (fd < 0) {
    return (FStar_Pervasives_Native_option__Common_TCP_listener){.tag = FStar_Pervasives_Native_None};
  }
  Common_TCP_listener l = common_tcp_listener_from_fd(fd);
  if (l == NULL) {
    (void)common_tcp_close_fd(fd);
    return (FStar_Pervasives_Native_option__Common_TCP_listener){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__Common_TCP_listener){
      .tag = FStar_Pervasives_Native_Some,
      .v = l,
  };
}

FStar_Pervasives_Native_option__Common_TCP_channel Common_TCP_accept_tcp(
    Common_TCP_listener l) {
  if (l == NULL) {
    return (FStar_Pervasives_Native_option__Common_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  int fd = common_tcp_accept(l->fd);
  if (fd < 0) {
    return (FStar_Pervasives_Native_option__Common_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  Common_TCP_channel ch = common_tcp_channel_from_fd(fd);
  if (ch == NULL) {
    (void)common_tcp_close_fd(fd);
    return (FStar_Pervasives_Native_option__Common_TCP_channel){.tag = FStar_Pervasives_Native_None};
  }
  return (FStar_Pervasives_Native_option__Common_TCP_channel){
      .tag = FStar_Pervasives_Native_Some,
      .v = ch,
  };
}

void Common_TCP_close_listener(Common_TCP_listener l) {
  if (l == NULL) {
    return;
  }
  if (l->fd >= 0) {
    (void)common_tcp_close_fd(l->fd);
  }
  free(l);
}

size_t Common_TCP_read(
    Common_TCP_channel ch,
    uint8_t *out,
    size_t max_len) {
  if (ch == NULL) {
    return 0;
  }
  ssize_t n = common_tcp_read_fd(ch->fd, out, max_len);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

size_t Common_TCP_read_full(
    Common_TCP_channel ch,
    uint8_t *out,
    size_t len,
    void *erased0,
    void *erased1,
    void *erased2) {
  (void)erased0;
  (void)erased1;
  (void)erased2;
  if (ch == NULL) {
    return 0;
  }
  size_t off = 0;
  while (off < len) {
    ssize_t n = common_tcp_read_fd(ch->fd, out + off, len - off);
    if (n <= 0) {
      return off;
    }
    off += (size_t)n;
  }
  return off;
}

size_t Common_TCP_write(
    Common_TCP_channel ch,
    uint8_t *buf,
    size_t len,
    void *erased0,
    void *erased1,
    void *erased2) {
  (void)erased0;
  (void)erased1;
  (void)erased2;
  if (ch == NULL) {
    return 0;
  }
  size_t off = 0;
  while (off < len) {
    ssize_t n = common_tcp_write_fd(ch->fd, buf + off, len - off);
    if (n <= 0) {
      return off;
    }
    off += (size_t)n;
  }
  return off;
}

void Common_TCP_close(Common_TCP_channel ch, void *erased0, void *erased1) {
  (void)erased0;
  (void)erased1;
  if (ch == NULL) {
    return;
  }
  if (ch->fd >= 0) {
    (void)common_tcp_close_fd(ch->fd);
  }
  free(ch);
}
