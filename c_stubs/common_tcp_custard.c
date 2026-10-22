#include "common_tcp_custard.h"
#include "custard_option.h"

#include "common_tcp_stubs.h"

#include <stdlib.h>
#include <string.h>

struct Common_TCP_channel_s {
  int rfd;
  int wfd;
};

struct Common_TCP_listener_s {
  int fd;
};


CUSTARD_OPTION_TYPE(option_channel, Common_TCP_channel);
CUSTARD_OPTION_TYPE(option_listener, Common_TCP_listener);

static Common_TCP_channel common_tcp_channel_from_fd(int fd) {
  Common_TCP_channel ch = malloc(sizeof *ch);
  if (ch == NULL) {
    return NULL;
  }
  ch->rfd = fd;
  ch->wfd = fd;
  return ch;
}

Common_TCP_channel Common_TCP_channel_of_fd(int fd) {
  return common_tcp_channel_from_fd(fd);
}

/* A channel that reads from one fd and writes to another (e.g. stdin/stdout).
   The single-fd constructors above set rfd == wfd (a bidirectional socket), so
   existing callers are unaffected. */
Common_TCP_channel Common_TCP_channel_of_fds(int rfd, int wfd) {
  Common_TCP_channel ch = malloc(sizeof *ch);
  if (ch == NULL) {
    return NULL;
  }
  ch->rfd = rfd;
  ch->wfd = wfd;
  return ch;
}

static Common_TCP_listener common_tcp_listener_from_fd(int fd) {
  Common_TCP_listener l = malloc(sizeof *l);
  if (l == NULL) {
    return NULL;
  }
  l->fd = fd;
  return l;
}

option_channel Common_TCP_connect_tcp(
    uint8_t *hostname,
    size_t hostname_len,
    uint16_t port) {
  if (hostname == NULL || hostname_len == SIZE_MAX) {
    return (option_channel){.tag = CUSTARD_NONE};
  }
  char *host = malloc(hostname_len + 1u);
  if (host == NULL) {
    return (option_channel){.tag = CUSTARD_NONE};
  }
  memcpy(host, hostname, hostname_len);
  host[hostname_len] = '\0';
  int fd = common_tcp_connect(host, port);
  free(host);
  if (fd < 0) {
    return (option_channel){.tag = CUSTARD_NONE};
  }
  Common_TCP_channel ch = common_tcp_channel_from_fd(fd);
  if (ch == NULL) {
    (void)common_tcp_close_fd(fd);
    return (option_channel){.tag = CUSTARD_NONE};
  }
  return (option_channel){
      .tag = CUSTARD_SOME,
      .val.Some = ch,
  };
}

option_listener Common_TCP_listen_tcp(
    uint8_t *bind_host,
    size_t bind_host_len,
    uint16_t port) {
  if (bind_host == NULL || bind_host_len == SIZE_MAX) {
    return (option_listener){.tag = CUSTARD_NONE};
  }
  char *host = malloc(bind_host_len + 1u);
  if (host == NULL) {
    return (option_listener){.tag = CUSTARD_NONE};
  }
  memcpy(host, bind_host, bind_host_len);
  host[bind_host_len] = '\0';
  int fd = common_tcp_listen(host, port);
  free(host);
  if (fd < 0) {
    return (option_listener){.tag = CUSTARD_NONE};
  }
  Common_TCP_listener l = common_tcp_listener_from_fd(fd);
  if (l == NULL) {
    (void)common_tcp_close_fd(fd);
    return (option_listener){.tag = CUSTARD_NONE};
  }
  return (option_listener){
      .tag = CUSTARD_SOME,
      .val.Some = l,
  };
}

option_channel Common_TCP_accept_tcp(
    Common_TCP_listener l) {
  if (l == NULL) {
    return (option_channel){.tag = CUSTARD_NONE};
  }
  int fd = common_tcp_accept(l->fd);
  if (fd < 0) {
    return (option_channel){.tag = CUSTARD_NONE};
  }
  Common_TCP_channel ch = common_tcp_channel_from_fd(fd);
  if (ch == NULL) {
    (void)common_tcp_close_fd(fd);
    return (option_channel){.tag = CUSTARD_NONE};
  }
  return (option_channel){
      .tag = CUSTARD_SOME,
      .val.Some = ch,
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
  ssize_t n = common_tcp_read_fd(ch->rfd, out, max_len);
  if (n <= 0) {
    return 0;
  }
  return (size_t)n;
}

size_t Common_TCP_read_full(
    Common_TCP_channel ch,
    uint8_t *out,
    size_t len) {
  if (ch == NULL) {
    return 0;
  }
  size_t off = 0;
  while (off < len) {
    ssize_t n = common_tcp_read_fd(ch->rfd, out + off, len - off);
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
    size_t len) {
  if (ch == NULL) {
    return 0;
  }
  size_t off = 0;
  while (off < len) {
    ssize_t n = common_tcp_write_fd(ch->wfd, buf + off, len - off);
    if (n <= 0) {
      return off;
    }
    off += (size_t)n;
  }
  return off;
}

void Common_TCP_close(Common_TCP_channel ch) {
  if (ch == NULL) {
    return;
  }
  if (ch->rfd >= 0) {
    (void)common_tcp_close_fd(ch->rfd);
  }
  if (ch->wfd >= 0 && ch->wfd != ch->rfd) {
    (void)common_tcp_close_fd(ch->wfd);
  }
  free(ch);
}
