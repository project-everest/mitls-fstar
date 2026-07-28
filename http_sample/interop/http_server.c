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
#define MAX_HEADERS   100      /* header-count cap (431 Request Header Fields Too Large) */
#define MAX_LINE      8192     /* per-header-line byte cap (431) */
#define MAX_BODY      1048576  /* request-body cap (413 Payload Too Large) */
#define READ_TIMEOUT_SECS 5    /* default per-connection read timeout (408) */

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
   Sets *head_end to the number of bytes up to and including the terminating
   CRLF-CRLF (0 if none was seen), and RETURNS the total number of bytes now in
   the buffer -- which for a request WITH a body may exceed *head_end, since the
   same recv() often delivers leading body bytes.  Returns -1 on a hard error, or
   -2 if a read timed out (SO_RCVTIMEO fired: recv gave EAGAIN/EWOULDBLOCK)
   before the head was complete -- the caller answers 408 Request Timeout. */
static ssize_t read_request_head(int fd, uint8_t *out, size_t cap, size_t *head_end) {
  size_t total = 0;
  int match = 0;                       /* how much of "\r\n\r\n" matched so far */
  static const uint8_t term[4] = { '\r', '\n', '\r', '\n' };
  *head_end = 0;
  while (total < cap) {
    ssize_t r = recv(fd, out + total, cap - total, 0);
    if (r < 0) {
      if (errno == EINTR) continue;
      if (errno == EAGAIN || errno == EWOULDBLOCK) return -2;  /* read timeout */
      return -1;
    }
    if (r == 0) break;                 /* client closed without a full head */
    for (ssize_t i = 0; i < r; i++) {
      uint8_t b = out[total + (size_t)i];
      match = (b == term[match]) ? match + 1 : (b == term[0] ? 1 : 0);
      if (match == 4 && *head_end == 0) *head_end = total + (size_t)i + 1;
    }
    total += (size_t)r;
    if (*head_end != 0) break;          /* head complete; body (if any) read separately */
  }
  return (ssize_t)total;
}

/* Read exactly `want` bytes from `fd` into `out` (blocking).  Returns the
   number of bytes read (== want on success, less on early EOF/error). */
static size_t read_exact(int fd, uint8_t *out, size_t want) {
  size_t got = 0;
  while (got < want) {
    ssize_t r = recv(fd, out + got, want - got, 0);
    if (r < 0) { if (errno == EINTR) continue; break; }
    if (r == 0) break;
    got += (size_t)r;
  }
  return got;
}

/* Read from `fd` into `out+off` (capacity `cap`) until EOF (client half-close),
   error, or the buffer fills.  Returns the total number of valid bytes in `out`
   (i.e. off + bytes read).  Used to slurp a chunked request body whose length is
   not known in advance; the client is expected to shutdown its write side. */
static size_t read_to_eof(int fd, uint8_t *out, size_t cap, size_t off) {
  size_t total = off;
  while (total < cap) {
    ssize_t r = recv(fd, out + total, cap - total, 0);
    if (r < 0) { if (errno == EINTR) continue; break; }
    if (r == 0) break;
    total += (size_t)r;
  }
  return total;
}

int main(int argc, char **argv) {
  if (argc < 2 || argc > 3) {
    fprintf(stderr, "usage: %s <bind_port> [body_file]\n", argv[0]);
    return 2;
  }
  signal(SIGPIPE, SIG_IGN);

  uint16_t port = (uint16_t)atoi(argv[1]);

  /* Optional status file (env HTTP_PARSE_STATUS_FILE): after each request we
     write "ok <target_len>" or "unrecognized" so a test harness can DETERMINISTIC-
     ally assert that the VERIFIED parser accepted the client's request head
     (persisting past the server being killed, unlike a racy stderr log). */
  const char *status_path = getenv("HTTP_PARSE_STATUS_FILE");

  /* Per-connection read timeout (env HTTP_READ_TIMEOUT overrides the default),
     in whole seconds.  A client that opens a connection and then stalls without
     completing the request head is dropped with a verified 408 Request Timeout
     instead of holding the single-threaded accept loop open indefinitely (a
     slow-loris style resource-exhaustion defense). */
  long read_timeout = READ_TIMEOUT_SECS;
  { const char *t = getenv("HTTP_READ_TIMEOUT");
    if (t && *t) { long v = atol(t); if (v > 0) read_timeout = v; } }

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
  uint8_t *decbuf  = malloc(REQ_CAP);        /* decoded chunked-body output */
  if (!reqbuf || !headbuf || !scratch || !decbuf) { free(reqbuf); free(headbuf); free(scratch); free(decbuf); free(body); close(lfd); return 1; }

  /* 2. Accept loop. */
  for (;;) {
    int fd = accept(lfd, NULL, NULL);
    if (fd < 0) { if (errno == EINTR) continue; perror("accept"); break; }

    /* Arm a read timeout on this connection so a stalled client cannot hold the
       accept loop open (slow-loris defense).  On expiry recv() returns EAGAIN,
       which read_request_head surfaces as -2 -> a verified 408 below. */
    { struct timeval tv; tv.tv_sec = read_timeout; tv.tv_usec = 0;
      setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv); }

    /* Read the client's request head into reqbuf (socket read is glue). */
    size_t head_end = 0;
    ssize_t rl = read_request_head(fd, reqbuf, REQ_CAP, &head_end);
    if (rl == -2) {
      /* The client stalled before completing the request head -> verified 408. */
      http_emit_response((uint16_t)408, (uint32_t)0, headbuf);
      Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
      Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
      Common_TCP_close(pch);
      fprintf(stderr, "http_server: read timed out on request head, served 408\n");
      if (status_path) {
        FILE *sf = fopen(status_path, "w");
        if (sf) { fprintf(sf, "timeout 408\n"); fclose(sf); }
      }
      continue;
    }
    if (rl < 0) { close(fd); continue; }
    size_t total  = (size_t)rl;
    size_t reqlen = head_end ? head_end : total;

    /* Locate the header block (bytes after the request line's first CRLF),
       which is what the verified header/framing scanners walk. */
    size_t hblock = 0;
    for (size_t i = 0; i + 1 < reqlen; i++)
      if (reqbuf[i] == '\r' && reqbuf[i + 1] == '\n') { hblock = i + 2; break; }

    /* 3y. Request-line + method guard: the VERIFIED validators reject a request
       whose request line does not parse (-> 400 Bad Request) or whose method,
       though syntactically valid, is not one of the eight standard HTTP methods
       (-> 501 Not Implemented).  Either way we answer with a verified error head
       (no body) and drop the connection. */
    if (reqlen == 0 || !http_request_line_ok(reqbuf, reqlen)) {
      http_emit_response((uint16_t)400, (uint32_t)0, headbuf);
      Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
      Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
      Common_TCP_close(pch);
      fprintf(stderr, "http_server: rejected request (malformed request line), served 400\n");
      if (status_path) {
        FILE *sf = fopen(status_path, "w");
        if (sf) { fprintf(sf, "badreq 400\n"); fclose(sf); }
      }
      continue;
    }
    if (!http_method_known(reqbuf, reqlen)) {
      http_emit_response((uint16_t)501, (uint32_t)0, headbuf);
      Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
      Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
      Common_TCP_close(pch);
      fprintf(stderr, "http_server: rejected request (unsupported method), served 501\n");
      if (status_path) {
        FILE *sf = fopen(status_path, "w");
        if (sf) { fprintf(sf, "notimpl 501\n"); fclose(sf); }
      }
      continue;
    }

    /* 3w. Method-not-allowed: the request method is a recognized HTTP method but
       one this origin server does not implement (it serves only GET/HEAD/POST).
       The VERIFIED http_method_allowed reports this; answer a verified 405. */
    if (!http_method_allowed(reqbuf, reqlen)) {
      http_emit_response((uint16_t)405, (uint32_t)0, headbuf);
      Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
      Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
      Common_TCP_close(pch);
      fprintf(stderr, "http_server: rejected request (method not allowed), served 405\n");
      if (status_path) {
        FILE *sf = fopen(status_path, "w");
        if (sf) { fprintf(sf, "notallowed 405\n"); fclose(sf); }
      }
      continue;
    }

    /* 3z. Request-smuggling guard (RFC 7230 3.3.3): the VERIFIED framing check
       rejects a request that carries a Content-Length alongside a
       Transfer-Encoding, or more than one Content-Length line.  On rejection we
       answer a verified 400 (no body) and drop the connection. */
    bool framing_ok = http_request_framing_ok(reqbuf + hblock, reqlen - hblock,
                                              (uint8_t *)"content-length", (size_t)14,
                                              (uint8_t *)"transfer-encoding", (size_t)17);
    if (!framing_ok) {
      http_emit_response((uint16_t)400, (uint32_t)0, headbuf);
      Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
      Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
      Common_TCP_close(pch);
      fprintf(stderr, "http_server: rejected request (smuggling: conflicting/duplicate framing), served 400\n");
      if (status_path) {
        FILE *sf = fopen(status_path, "w");
        if (sf) { fprintf(sf, "smuggling 400\n"); fclose(sf); }
      }
      continue;
    }

    /* 3x. Header-block limits (DoS defense): the VERIFIED limit enforcer rejects
       a request head that carries too many header lines or an over-long single
       line.  On rejection we answer a verified 431 (no body) and drop. */
    if (!http_header_limits_ok(reqbuf + hblock, reqlen - hblock,
                               (size_t)MAX_HEADERS, (size_t)MAX_LINE)) {
      http_emit_response((uint16_t)431, (uint32_t)0, headbuf);
      Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
      Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
      Common_TCP_close(pch);
      fprintf(stderr, "http_server: rejected request (header fields too large), served 431\n");
      if (status_path) {
        FILE *sf = fopen(status_path, "w");
        if (sf) { fprintf(sf, "toolarge 431\n"); fclose(sf); }
      }
      continue;
    }

    /* 3a. POST branch: the VERIFIED method parser detects the method, the
       VERIFIED header decoder recovers Content-Length, and we ECHO the request
       body back in a verified 200 response head + body copy.  This exercises a
       real request body end-to-end (`curl -d ...`). */
    bool is_post = http_method_eq(reqbuf, reqlen, (uint8_t *)"POST", (size_t)4);
    if (is_post) {
      /* Advance past the request line (its terminating CRLF) to the header
         block, which is what the verified header decoder scans. */
      size_t block = 0;
      for (size_t i = 0; i + 1 < reqlen; i++)
        if (reqbuf[i] == '\r' && reqbuf[i + 1] == '\n') { block = i + 2; break; }

      bool     found = false;
      uint32_t clen  = 0;
      http_header_dec(reqbuf + block, reqlen - block,
                      (uint8_t *)"content-length", (size_t)14, &found, &clen);
      size_t clen_sz = (size_t)clen;

      /* 3a-i. Length Required (411): a POST with neither Content-Length nor
         Transfer-Encoding has no defined body length; reject with a verified
         411 (the VERIFIED header counter confirms no Transfer-Encoding).  When a
         Transfer-Encoding IS present we decode the chunked body with the
         VERIFIED chunk decoder (3a-iii). */
      if (!found) {
        size_t tec = http_count_header_named(reqbuf + block, reqlen - block,
                                             (uint8_t *)"transfer-encoding", (size_t)17);
        if (tec == 0) {
          http_emit_response((uint16_t)411, (uint32_t)0, headbuf);
          Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
          Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
          Common_TCP_close(pch);
          fprintf(stderr, "http_server: rejected POST (no Content-Length), served 411\n");
          if (status_path) {
            FILE *sf = fopen(status_path, "w");
            if (sf) { fprintf(sf, "lenreq 411\n"); fclose(sf); }
          }
          continue;
        }

        /* 3a-iii. Chunked upload: slurp the chunked body (the client half-closes
           its write side) and decode it with the VERIFIED variable-width chunk
           decoder.  A well-formed body is echoed back in a verified 200; a
           MALFORMED chunk size (or frame) makes the decoder return ok=false and
           we answer a verified 400 Bad Request. */
        size_t newtotal = read_to_eof(fd, reqbuf, REQ_CAP, total);
        size_t bodylen  = (newtotal > head_end) ? (newtotal - head_end) : 0;
        size_t off      = 0;
        bool dec_ok = http_decode_chunks_var(reqbuf + head_end, bodylen,
                                             decbuf, (size_t)REQ_CAP, &off);
        Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
        if (!dec_ok) {
          http_emit_response((uint16_t)400, (uint32_t)0, headbuf);
          Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
          Common_TCP_close(pch);
          fprintf(stderr, "http_server: rejected chunked POST (malformed chunk), served 400\n");
          if (status_path) {
            FILE *sf = fopen(status_path, "w");
            if (sf) { fprintf(sf, "badchunk 400\n"); fclose(sf); }
          }
          continue;
        }
        http_emit_response((uint16_t)200, (uint32_t)off, headbuf);
        Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
        if (off > 0) Common_TCP_write(pch, decbuf, off);
        Common_TCP_close(pch);
        fprintf(stderr, "http_server: decoded chunked POST, echoed %zu-byte body\n", off);
        if (status_path) {
          FILE *sf = fopen(status_path, "w");
          if (sf) { fprintf(sf, "chunked %zu\n", off); fclose(sf); }
        }
        continue;
      }

      /* 3a-ii. Payload Too Large (413): a Content-Length beyond the server cap
         is rejected up front with a verified 413 (before reading the body). */
      if (found && clen_sz > (size_t)MAX_BODY) {
        http_emit_response((uint16_t)413, (uint32_t)0, headbuf);
        Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
        Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
        Common_TCP_close(pch);
        fprintf(stderr, "http_server: rejected POST (Content-Length %u exceeds cap), served 413\n", clen);
        if (status_path) {
          FILE *sf = fopen(status_path, "w");
          if (sf) { fprintf(sf, "toobig 413\n"); fclose(sf); }
        }
        continue;
      }

      /* Gather the request body: some bytes may already trail the head in
         reqbuf; read the remainder up to Content-Length. */
      size_t have = (total > head_end) ? (total - head_end) : 0;
      if (found && clen_sz < 100000000u && head_end + clen_sz <= REQ_CAP) {
        uint8_t *bodyp = reqbuf + head_end;
        if (have < clen_sz)
          have += read_exact(fd, bodyp + have, clen_sz - have);
        size_t echo_len = (have < clen_sz) ? have : clen_sz;

        /* Verified 200 head (43 bytes, 8-digit Content-Length) + echoed body. */
        http_emit_response((uint16_t)200, (uint32_t)echo_len, headbuf);
        Common_TCP_channel pch = Common_TCP_channel_of_fd(fd);
        Common_TCP_write(pch, headbuf, (size_t)RESP_HEAD_LEN);
        if (echo_len > 0) Common_TCP_write(pch, bodyp, echo_len);
        Common_TCP_close(pch);

        fprintf(stderr, "http_server: parsed POST (Content-Length %u), echoed %zu-byte body\n",
                clen, echo_len);
        if (status_path) {
          FILE *sf = fopen(status_path, "w");
          if (sf) { fprintf(sf, "post %zu\n", echo_len); fclose(sf); }
        }
        continue;
      }
      /* Malformed/oversized POST: fall through to the GET-style handler below. */
    }

    /* 3b. GET (and fallback) path: hand the connected fd + request buffer to the
       VERIFIED exchange driver, which PARSES the request head with
       http_recv_request_head (recovering the target length into ptlen) and
       writes the 200 head + body, closing the channel (and thus the fd). */
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

    /* Deterministic status marker for the test harness. */
    if (status_path) {
      FILE *sf = fopen(status_path, "w");
      if (sf) {
        if (okr) fprintf(sf, "ok %zu\n", ptlen);
        else     fprintf(sf, "unrecognized\n");
        fclose(sf);
      }
    }
  }

  free(reqbuf); free(headbuf); free(scratch); free(decbuf); free(body);
  close(lfd);
  return 0;
}
