/*
 * http_server.c -- an HTTP/1.1 origin SERVER whose response is produced by the
 * VERIFIED, extracted Pulse driver `http_server_run_length_full`.
 *
 * The response head + body -- "HTTP/1.1 200 \r\nContent-Length: <8-digit>\r\n\r\n"
 * followed by the body bytes -- is framed and written by the verified FStar/Pulse
 * code extracted to C in HTTP_Verified.c (http_server_run_length_full, which
 * reuses the verified head emitter http_emit_response and body copy
 * http_emit_body, over the verified Common.TCP channel).  This program is the
 * thin, UNVERIFIED glue around it:
 *
 *   1. bind a TCP socket to loopback:<port> and listen;
 *   2. for each accepted connection, DRAIN the client's request head (up to the
 *      CRLF-CRLF terminator).  A real client (curl) always sends a Host header
 *      and others, and its request length is not known ahead of time, so the
 *      verified fixed-format request parser (http_recv_request, which accepts
 *      only a header-less "GET <target> HTTP/1.1\r\n\r\n" of known length) can't
 *      parse it -- the request read is therefore out-of-model glue.  The bytes
 *      are drained (not interpreted) so the connection closes cleanly;
 *   3. wrap the connected fd into a Common_TCP_channel and hand it to the
 *      VERIFIED http_server_run_length_full, which writes the 200 response head
 *      + body and closes the channel.
 *
 * The server serves the SAME fixed body to every request (a built-in string, or
 * the contents of an optional file argument).  It loops, serving connections
 * until killed.
 *
 * Usage:  http_server <bind_port> [body_file]
 */

#include "HTTP_Verified.h"
#include "common_tcp_karamel.h"

#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#define RESP_HEAD_LEN 43       /* fixed size of the verified response head */
#define REQ_CAP       65536    /* max request-head bytes we will drain */

static const char DEFAULT_BODY[] =
  "Hello from the verified FStar/Pulse HTTP/1.1 server!\n";

/* Read a whole file into a freshly malloc'd buffer; sets *out_len. */
static uint8_t *read_file(const char *path, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (!f) return NULL;
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  rewind(f);
  if (n < 0) { fclose(f); return NULL; }
  uint8_t *buf = malloc((size_t)n ? (size_t)n : 1);
  if (!buf) { fclose(f); return NULL; }
  if (n > 0 && fread(buf, 1, (size_t)n, f) != (size_t)n) { fclose(f); free(buf); return NULL; }
  fclose(f);
  *out_len = (size_t)n;
  return buf;
}

/* Drain the request head from `fd` up to and including the CRLF-CRLF that ends
   it (or until EOF / cap / error).  The bytes are discarded -- see the file
   header for why the request is out-of-model glue.  Returns the number of bytes
   read, or -1 on a hard error. */
static ssize_t drain_request_head(int fd) {
  uint8_t buf[4096];
  size_t total = 0;
  int match = 0;                       /* how much of "\r\n\r\n" matched so far */
  static const uint8_t term[4] = { '\r', '\n', '\r', '\n' };
  while (total < REQ_CAP) {
    ssize_t r = recv(fd, buf, sizeof buf, 0);
    if (r < 0) { if (errno == EINTR) continue; return -1; }
    if (r == 0) break;                 /* client closed without a full head */
    total += (size_t)r;
    for (ssize_t i = 0; i < r; i++) {
      match = (buf[i] == term[match]) ? match + 1 : (buf[i] == term[0] ? 1 : 0);
      if (match == 4) return (ssize_t)total;   /* end of request head */
    }
  }
  return (ssize_t)total;
}

int main(int argc, char **argv) {
  if (argc < 2 || argc > 3) {
    fprintf(stderr, "usage: %s <bind_port> [body_file]\n", argv[0]);
    return 2;
  }
  signal(SIGPIPE, SIG_IGN);

  uint16_t port = (uint16_t)atoi(argv[1]);

  /* Resolve the response body: an optional file, else the built-in string. */
  uint8_t *body = NULL;
  size_t   body_len = 0;
  if (argc == 3) {
    body = read_file(argv[2], &body_len);
    if (!body) { fprintf(stderr, "cannot read body file %s: %s\n", argv[2], strerror(errno)); return 1; }
  } else {
    body_len = sizeof DEFAULT_BODY - 1;      /* drop the trailing NUL */
    body = malloc(body_len ? body_len : 1);
    if (!body) return 1;
    memcpy(body, DEFAULT_BODY, body_len);
  }
  if (body_len >= 100000000u) {               /* 8-digit Content-Length bound */
    fprintf(stderr, "body too large for the fixed 8-digit Content-Length head\n");
    free(body);
    return 1;
  }

  /* 1. Bind loopback:<port> and listen. */
  int lfd = socket(AF_INET, SOCK_STREAM, 0);
  if (lfd < 0) { perror("socket"); free(body); return 1; }
  int one = 1;
  setsockopt(lfd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof addr);
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = htons(port);
  if (bind(lfd, (struct sockaddr *)&addr, sizeof addr) != 0) { perror("bind"); free(body); return 1; }
  if (listen(lfd, 16) != 0) { perror("listen"); free(body); return 1; }

  fprintf(stderr, "http_server: listening on 127.0.0.1:%u, serving %zu-byte body (verified response)\n",
          port, body_len);

  /* Staging buffers for the verified emitter: 43-byte head + body_len body. */
  uint8_t *headbuf = malloc(RESP_HEAD_LEN);
  uint8_t *scratch = malloc(body_len ? body_len : 1);
  if (!headbuf || !scratch) { free(headbuf); free(scratch); free(body); close(lfd); return 1; }

  /* 2. Accept loop. */
  for (;;) {
    int fd = accept(lfd, NULL, NULL);
    if (fd < 0) { if (errno == EINTR) continue; perror("accept"); break; }

    /* Drain the client's request head (out-of-model glue). */
    (void)drain_request_head(fd);

    /* 3. Hand the connected fd to the VERIFIED response driver, which writes the
       200 head + body and closes the channel (and thus the fd). */
    Common_TCP_channel ch = Common_TCP_channel_of_fd(fd);
    http_server_run_length_full(ch, (uint16_t)200, body, body_len, headbuf, scratch);

    fprintf(stderr, "http_server: served one request (200, %zu-byte body)\n", body_len);
  }

  free(headbuf); free(scratch); free(body);
  close(lfd);
  return 0;
}
