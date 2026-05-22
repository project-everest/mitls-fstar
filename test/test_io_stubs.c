#include "tls13_io_stubs.h"

#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

static int test_pipe_roundtrip(void) {
  int fds[2];
  if (pipe(fds) != 0) {
    perror("pipe");
    return 1;
  }

  static const uint8_t msg[] = "agentic tls io smoke";
  uint8_t out[sizeof msg];
  ssize_t written = tls13_io_write_fd(fds[1], msg, sizeof msg);
  if (written != (ssize_t)sizeof msg) {
    fprintf(stderr, "write returned %zd\n", written);
    close(fds[0]);
    close(fds[1]);
    return 1;
  }
  ssize_t read = tls13_io_read_fd(fds[0], out, sizeof out);
  close(fds[0]);
  close(fds[1]);
  if (read != (ssize_t)sizeof out) {
    fprintf(stderr, "read returned %zd\n", read);
    return 1;
  }
  if (memcmp(out, msg, sizeof msg) != 0) {
    fprintf(stderr, "pipe roundtrip mismatch\n");
    return 1;
  }
  return 0;
}

static int test_rejects_null_buffers(void) {
  errno = 0;
  if (tls13_io_write_fd(-1, NULL, 1) != -1 || errno != EINVAL) {
    fprintf(stderr, "write did not reject null buffer\n");
    return 1;
  }
  errno = 0;
  if (tls13_io_read_fd(-1, NULL, 1) != -1 || errno != EINVAL) {
    fprintf(stderr, "read did not reject null buffer\n");
    return 1;
  }
  return 0;
}

int main(void) {
  int failed = 0;
  failed |= test_pipe_roundtrip();
  failed |= test_rejects_null_buffers();
  if (failed != 0) {
    return 1;
  }
  printf("I/O stub tests passed\n");
  return 0;
}

