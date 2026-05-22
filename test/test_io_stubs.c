#include "tls13_io_stubs.h"

#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
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

static int test_tcp_connect_roundtrip(void) {
  int listener = socket(AF_INET, SOCK_STREAM, 0);
  if (listener < 0) {
    perror("socket");
    return 1;
  }
  int one = 1;
  if (setsockopt(listener, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one) != 0) {
    perror("setsockopt");
    close(listener);
    return 1;
  }

  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = 0;
  if (bind(listener, (struct sockaddr *)&addr, sizeof addr) != 0 || listen(listener, 1) != 0) {
    perror("bind/listen");
    close(listener);
    return 1;
  }

  socklen_t addr_len = sizeof addr;
  if (getsockname(listener, (struct sockaddr *)&addr, &addr_len) != 0) {
    perror("getsockname");
    close(listener);
    return 1;
  }
  uint16_t port = ntohs(addr.sin_port);

  pid_t child = fork();
  if (child < 0) {
    perror("fork");
    close(listener);
    return 1;
  }
  if (child == 0) {
    int accepted = accept(listener, NULL, NULL);
    if (accepted < 0) {
      _exit(2);
    }
    uint8_t buf[32];
    ssize_t n = tls13_io_read_fd(accepted, buf, sizeof buf);
    if (n <= 0 || tls13_io_write_fd(accepted, buf, (size_t)n) != n) {
      close(accepted);
      _exit(3);
    }
    close(accepted);
    _exit(0);
  }

  int client = tls13_io_connect_tcp("127.0.0.1", port);
  close(listener);
  if (client < 0) {
    perror("tls13_io_connect_tcp");
    waitpid(child, NULL, 0);
    return 1;
  }

  static const uint8_t msg[] = "tcp io smoke";
  uint8_t out[sizeof msg];
  if (tls13_io_write_fd(client, msg, sizeof msg) != (ssize_t)sizeof msg ||
      tls13_io_read_fd(client, out, sizeof out) != (ssize_t)sizeof out) {
    fprintf(stderr, "TCP roundtrip I/O failed\n");
    tls13_io_close_fd(client);
    waitpid(child, NULL, 0);
    return 1;
  }
  tls13_io_close_fd(client);

  int status = 0;
  if (waitpid(child, &status, 0) != child || !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
    fprintf(stderr, "TCP echo child failed\n");
    return 1;
  }
  if (memcmp(out, msg, sizeof msg) != 0) {
    fprintf(stderr, "TCP roundtrip mismatch\n");
    return 1;
  }
  return 0;
}

int main(void) {
  int failed = 0;
  failed |= test_pipe_roundtrip();
  failed |= test_rejects_null_buffers();
  failed |= test_tcp_connect_roundtrip();
  if (failed != 0) {
    return 1;
  }
  printf("I/O stub tests passed\n");
  return 0;
}
