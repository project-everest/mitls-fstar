#include "tls13_io_stubs.h"

#include <errno.h>
#include <netdb.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

int tls13_io_connect_tcp(const char *hostname, uint16_t port) {
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

ssize_t tls13_io_read_fd(int fd, uint8_t *out, size_t max_len) {
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

int tls13_io_close_fd(int fd) {
  int r;
  do {
    r = close(fd);
  } while (r < 0 && errno == EINTR);
  return r;
}

ssize_t tls13_io_write_fd(int fd, const uint8_t *buf, size_t len) {
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
