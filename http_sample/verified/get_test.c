/*
 * get_test.c — end-to-end test of the *verified* HTTP/1.1 GET client
 * `http_get` (HTTP.Impl.Client.Loop.Get) against a mock server.
 *
 * The child process is a mock HTTP server: it writes a canned, real-style HTTP
 * response (status line + Content-Length + Connection: close head, then a body)
 * and closes the connection.  The parent is the extracted, verified
 * `http_get`, which emits a `GET / HTTP/1.1\r\nHost: example.com\r\n...`
 * request via the verified `http_emit_request_host`, reads the whole response
 * to EOF (`recv_to_eof`), then parses the response head
 * (`http_parse_response_head`).  We check that the verified client recovers
 * status code 200, Content-Length framing with cl==13, and the full response
 * byte count.
 */

#include "HTTP_Verified.h"
#include "common_tcp_karamel.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <signal.h>
#include <unistd.h>

static const char RESP[] =
  "HTTP/1.1 200 OK\r\n"
  "Content-Length: 13\r\n"
  "Connection: close\r\n"
  "\r\n"
  "Hello, world!";

int main(void) {
  signal(SIGPIPE, SIG_IGN);

  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) != 0) { perror("socketpair"); return 1; }

  pid_t pid = fork();
  if (pid < 0) { perror("fork"); return 1; }

  if (pid == 0) {
    /* ── child: mock server ──────────────────────────────────────────────── */
    close(sv[1]);
    size_t total = sizeof(RESP) - 1;   /* drop trailing NUL */
    /* (optionally read+discard the client's request first, but the client
       writes then reads, so we can just write immediately) */
    const char *p = RESP;
    size_t left = total;
    while (left > 0) {
      ssize_t w = write(sv[0], p, left);
      if (w <= 0) break;
      p += w; left -= (size_t)w;
    }
    close(sv[0]);   /* EOF so recv_to_eof terminates */
    _exit(0);
  }

  /* ── parent: the VERIFIED GET client ──────────────────────────────────── */
  close(sv[0]);
  Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[1]);

  uint8_t target[] = { '/' };
  size_t target_len = 1;
  uint8_t host[] = { 'e','x','a','m','p','l','e','.','c','o','m' };
  size_t host_len = 11;

  /* reqbuf length must be 4 + target_len + 17 + host_len + 23 */
  size_t reqlen = 4 + target_len + 17 + host_len + 23;
  uint8_t *reqbuf = malloc(reqlen);

  size_t cap = 4096;
  uint8_t *buf = malloc(cap);
  size_t tmpcap = 256;
  uint8_t *tmp = malloc(tmpcap);
  if (!reqbuf || !buf || !tmp) { free(reqbuf); free(buf); free(tmp); return 1; }

  size_t   rlen    = 0;
  uint16_t code    = 0;
  bool     chunked = false;
  bool     has_cl  = false;
  uint32_t cl      = 0;

  bool ok = http_get(ch, target, target_len, host, host_len,
                     reqbuf, buf, cap, tmp, tmpcap,
                     &rlen, &code, &chunked, &has_cl, &cl);

  Common_TCP_close(ch);

  int status = 0;
  waitpid(pid, &status, 0);

  size_t expected_rlen = sizeof(RESP) - 1;
  int pass = ok
          && code == 200
          && !chunked
          && has_cl
          && cl == 13
          && rlen == expected_rlen;

  printf("verified GET: ok=%d code=%u chunked=%d has_cl=%d cl=%u rlen=%zu (expected code=200 has_cl=1 cl=13 rlen=%zu) => %s\n",
         ok, code, chunked, has_cl, cl, rlen, expected_rlen,
         pass ? "PASS" : "FAIL");

  free(reqbuf); free(buf); free(tmp);
  return pass ? 0 : 1;
}
