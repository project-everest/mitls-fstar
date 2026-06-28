#include "common_tcp_stubs.h"

#include <errno.h>
#include <netdb.h>
#include <netinet/in.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

int common_tcp_connect(const char *hostname, uint16_t port) {
  if (hostname == NULL) {
    errno = EINVAL;
    return -1;
  }

  char port_string[6];
  int n = snprintf(port_string, sizeof port_string, "%u", (unsigned)port);
  if (n < 0 || (size_t)n >= sizeof port_string) {
    errno = EINVAL;
    return -1;
  }

  struct addrinfo hints;
  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;

  struct addrinfo *result = NULL;
  int gai = getaddrinfo(hostname, port_string, &hints, &result);
  if (gai != 0) {
    errno = EHOSTUNREACH;
    return -1;
  }

  int fd = -1;
  for (struct addrinfo *rp = result; rp != NULL; rp = rp->ai_next) {
    fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
    if (fd < 0) {
      continue;
    }
    if (connect(fd, rp->ai_addr, rp->ai_addrlen) == 0) {
      break;
    }
    close(fd);
    fd = -1;
  }
  freeaddrinfo(result);
  return fd;
}

int common_tcp_listen(const char *bind_host, uint16_t port) {
  if (bind_host == NULL) {
    errno = EINVAL;
    return -1;
  }

  char port_string[6];
  int n = snprintf(port_string, sizeof port_string, "%u", (unsigned)port);
  if (n < 0 || (size_t)n >= sizeof port_string) {
    errno = EINVAL;
    return -1;
  }

  struct addrinfo hints;
  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_flags = AI_PASSIVE;

  struct addrinfo *result = NULL;
  int gai = getaddrinfo(bind_host[0] == '\0' ? NULL : bind_host, port_string, &hints, &result);
  if (gai != 0) {
    errno = EADDRNOTAVAIL;
    return -1;
  }

  int fd = -1;
  for (struct addrinfo *rp = result; rp != NULL; rp = rp->ai_next) {
    fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);
    if (fd < 0) {
      continue;
    }
    int one = 1;
    (void)setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    if (bind(fd, rp->ai_addr, rp->ai_addrlen) == 0 && listen(fd, 1) == 0) {
      break;
    }
    close(fd);
    fd = -1;
  }
  freeaddrinfo(result);
  return fd;
}

int common_tcp_accept(int listener_fd) {
  int fd;
  do {
    fd = accept(listener_fd, NULL, NULL);
  } while (fd < 0 && errno == EINTR);
  return fd;
}

ssize_t common_tcp_read_fd(int fd, uint8_t *out, size_t max_len) {
  if (max_len != 0 && out == NULL) {
    errno = EINVAL;
    return -1;
  }

  ssize_t n;
  do {
    n = read(fd, out, max_len);
  } while (n < 0 && errno == EINTR);
  return n;
}

int common_tcp_close_fd(int fd) {
  int r;
  do {
    r = close(fd);
  } while (r < 0 && errno == EINTR);
  return r;
}

ssize_t common_tcp_write_fd(int fd, const uint8_t *buf, size_t len) {
  if (len != 0 && buf == NULL) {
    errno = EINVAL;
    return -1;
  }

  ssize_t n;
  do {
    n = write(fd, buf, len);
  } while (n < 0 && errno == EINTR);
  return n;
}
