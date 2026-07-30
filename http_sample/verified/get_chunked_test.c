/*
 * get_chunked_test.c — end-to-end test of the *verified* HTTP/1.1 GET client
 * against a mock server returning a **chunked** response, exercising both
 * `http_get` (HTTP.Impl.Client.Loop.Get) and `http_get_body_chunked` (the
 * verified chunked-body decoder).
 *
 * The child mock server writes a real-style chunked response:
 *   HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n
 *   <chunk stream>
 * then closes.  The parent runs the verified `http_get` (recovering code==200
 * and pchunked==true), then `http_get_body_chunked` to reassemble the payload
 * from buf[headlen..rlen), and checks the decoded bytes equal the original.
 *
 * NOTE: the codec's chunk headers are a fixed 4-hex-digit size + CRLF (see
 * HTTP.Impl.Codec.Chunked.Stream), so the mock server emits sizes as %04x.
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

static const char HEAD[] =
  "HTTP/1.1 200 OK\r\n"
  "Transfer-Encoding: chunked\r\n"
  "Connection: close\r\n"
  "\r\n";

/* The payload we expect to reassemble. */
static const char PAYLOAD[] = "Hello, chunked world!";

static void write_all(int fd, const void *p, size_t n) {
  const char *c = (const char *)p;
  while (n > 0) {
    ssize_t w = write(fd, c, n);
    if (w <= 0) break;
    c += w; n -= (size_t)w;
  }
}

/* emit one chunk: "%04x\r\n<data>\r\n" */
static void write_chunk(int fd, const char *data, size_t len) {
  char hdr[8];
  snprintf(hdr, sizeof hdr, "%04zx\r\n", len);
  write_all(fd, hdr, 6);
  write_all(fd, data, len);
  write_all(fd, "\r\n", 2);
}

int main(void) {
  signal(SIGPIPE, SIG_IGN);

  int sv[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) != 0) { perror("socketpair"); return 1; }

  pid_t pid = fork();
  if (pid < 0) { perror("fork"); return 1; }

  if (pid == 0) {
    /* ── child: mock chunked server ──────────────────────────────────────── */
    close(sv[1]);
    write_all(sv[0], HEAD, sizeof(HEAD) - 1);
    size_t plen = sizeof(PAYLOAD) - 1;
    /* split the payload into two chunks to exercise multi-chunk reassembly */
    size_t first = plen / 2;
    write_chunk(sv[0], PAYLOAD, first);
    write_chunk(sv[0], PAYLOAD + first, plen - first);
    write_chunk(sv[0], "", 0);     /* 0000\r\n\r\n : last chunk */
    close(sv[0]);                  /* EOF so recv_to_eof terminates */
    _exit(0);
  }

  /* ── parent: the VERIFIED GET client ──────────────────────────────────── */
  close(sv[0]);
  Common_TCP_channel ch = Common_TCP_channel_of_fd(sv[1]);

  uint8_t target[] = { '/' };
  size_t target_len = 1;
  uint8_t host[] = { 'e','x','a','m','p','l','e','.','c','o','m' };
  size_t host_len = 11;

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
  size_t   headlen = 0;

  bool ok = http_get(ch, target, target_len, host, host_len,
                     reqbuf, buf, cap, tmp, tmpcap,
                     &rlen, &code, &chunked, &has_cl, &cl, &headlen);

  Common_TCP_close(ch);

  int status = 0;
  waitpid(pid, &status, 0);

  /* decode the chunked body span buf[headlen..rlen) */
  size_t rawcap = 4096, outcap = 4096;
  uint8_t *raw = malloc(rawcap);
  uint8_t *out = malloc(outcap);
  size_t outlen = 0;
  int decode_ok = 0;
  if (ok && chunked && headlen <= rlen && (rlen - headlen) <= rawcap && raw && out) {
    decode_ok = http_get_body_chunked(buf, headlen, rlen, raw, rawcap, out, outcap, &outlen);
  }

  size_t plen = sizeof(PAYLOAD) - 1;
  int pass = ok
          && code == 200
          && chunked
          && !has_cl
          && decode_ok
          && outlen == plen
          && memcmp(out, PAYLOAD, plen) == 0;

  printf("verified chunked GET: ok=%d code=%u chunked=%d decode_ok=%d outlen=%zu (expected code=200 chunked=1 outlen=%zu) => %s\n",
         ok, code, chunked, decode_ok, outlen, plen,
         pass ? "PASS" : "FAIL");

  free(reqbuf); free(buf); free(tmp); free(raw); free(out);
  return pass ? 0 : 1;
}
