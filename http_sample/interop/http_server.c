/*
 * http_server.c -- an HTTP/1.1 origin SERVER whose request PARSE and response
 * are BOTH produced by VERIFIED, extracted Pulse code.
 *
 * Each exchange runs through the verified driver `http_server_exchange_length_head`
 * (in HTTP_Verified.c), which:
 *   - parses the client's request head with the verified headers-tolerant codec
 *     leaf `http_recv_request_head` -- it locates the space-free request target
 *     between "GET " and the " HTTP/1.1\r\n" version token and IGNORES all header
 *     lines, so a REAL client (curl, browsers, sending Host/User-Agent/Accept and
 *     a request of a-priori-unknown length) is parsed.  On success the recovered
 *     target provably matches `parse_request_line` of the received bytes;
 *   - then writes the response head + body -- "HTTP/1.1 200 \r\nContent-Length:
 *     <8-digit>\r\n\r\n" followed by the body bytes -- via the verified head
 *     emitter http_emit_response and body copy http_emit_body, over the verified
 *     Common.TCP channel, and closes it.
 *
 * This program is the thin, UNVERIFIED glue around that driver:
 *   1. bind a TCP socket to loopback:<port> and listen;
 *   2. for each accepted connection, READ the client's request head into a buffer
 *      up to the CRLF-CRLF terminator (the socket read is glue -- the request
 *      length is not known ahead of time -- but the buffered bytes are then
 *      parsed by the VERIFIED leaf, so the parse itself is in-model);
 *   3. wrap the connected fd into a Common_TCP_channel and hand it, with the
 *      request buffer, to the VERIFIED http_server_exchange_length_head.
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
#define REQ_CAP       65536    /* max request-head bytes we will buffer */

static const char DEFAULT_BODY[] =
  "Served by the verified FStar/Pulse HTTP/1.1 server!\n";

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

/* Read the request head from `fd` into `out` (capacity `cap`), up to and
   including the CRLF-CRLF that ends it (or until EOF / cap / error).  Unlike a
   plain drain, the bytes are KEPT so the verified parser can inspect them.
   Returns the number of bytes stored, or -1 on a hard error. */
static ssize_t read_request_head(int fd, uint8_t *out, size_t cap) {
  size_t total = 0;
  int match = 0;                       /* how much of "\r\n\r\n" matched so far */
  static const uint8_t term[4] = { '\r', '\n', '\r', '\n' };
  while (total < cap) {
    ssize_t r = recv(fd, out + total, cap - total, 0);
    if (r < 0) { if (errno == EINTR) continue; return -1; }
    if (r == 0) break;                 /* client closed without a full head */
    for (ssize_t i = 0; i < r; i++) {
      uint8_t b = out[total + (size_t)i];
      match = (b == term[match]) ? match + 1 : (b == term[0] ? 1 : 0);
      if (match == 4) return (ssize_t)(total + (size_t)i + 1);   /* end of head */
    }
    total += (size_t)r;
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

  /* Staging buffers for the verified exchange: the request head buffer, the
     recovered target-length out-param, the 43-byte response head, and the body
     scratch. */
  uint8_t *reqbuf  = malloc(REQ_CAP);
  uint8_t *headbuf = malloc(RESP_HEAD_LEN);
  uint8_t *scratch = malloc(body_len ? body_len : 1);
  if (!reqbuf || !headbuf || !scratch) { free(reqbuf); free(headbuf); free(scratch); free(body); close(lfd); return 1; }

  /* 2. Accept loop. */
  for (;;) {
    int fd = accept(lfd, NULL, NULL);
    if (fd < 0) { if (errno == EINTR) continue; perror("accept"); break; }

    /* Read the client's request head into reqbuf (socket read is glue). */
    ssize_t rl = read_request_head(fd, reqbuf, REQ_CAP);
    if (rl < 0) { close(fd); continue; }
    size_t reqlen = (size_t)rl;

    /* 3. Hand the connected fd + request buffer to the VERIFIED exchange driver:
       it PARSES the request head with http_recv_request_head (recovering the
       target length into ptlen) and writes the 200 head + body, closing the
       channel (and thus the fd). */
    size_t ptlen = 0;
    Common_TCP_channel ch = Common_TCP_channel_of_fd(fd);
    bool okr = http_server_exchange_length_head(ch, reqbuf, reqlen, &ptlen,
                                                (uint16_t)200, body, body_len,
                                                headbuf, scratch);

    if (okr)
      fprintf(stderr, "http_server: parsed request (target %zu bytes), served 200 (%zu-byte body)\n",
              ptlen, body_len);
    else
      fprintf(stderr, "http_server: request head not recognized (served 200 anyway, %zu-byte body)\n",
              body_len);
  }

  free(reqbuf); free(headbuf); free(scratch); free(body);
  close(lfd);
  return 0;
}
