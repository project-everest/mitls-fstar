#include "tls13_io_stubs.h"

#include <errno.h>
#include <unistd.h>

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

