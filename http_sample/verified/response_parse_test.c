/*
 * response_parse_test.c -- concrete C validation of the *verified* HTTP/1.1
 * response-head parsers extracted into HTTP_Verified.c.
 *
 * Exercises the extracted, verified F-star/Pulse leaves (HTTP.Impl.Codec.Response)
 *   http_parse_status_line  -- "HTTP/1.1 " ddd " ..."  -> status code
 *   http_parse_framing      -- scan header block for Content-Length /
 *                              Transfer-Encoding: chunked
 *   http_parse_response_head -- both combined
 *
 * These are what the client runs on the reply to GET http://example.com/ to
 * learn the status and how to frame the body.  We feed a spread of real-world
 * response heads (varied header order, casing, whitespace) and check the parser
 * returns the expected (code, framing, content-length), plus that malformed
 * heads are rejected.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

/* framing tags decided from the raw signals (chunked wins over Content-Length) */
enum { FR_EOF = 0, FR_LENGTH = 1, FR_CHUNKED = 2 };

static int framing_of(bool chunked, bool has_cl) {
  if (chunked) return FR_CHUNKED;
  if (has_cl)  return FR_LENGTH;
  return FR_EOF;
}

static void check(const char *head, bool exp_ok, uint16_t exp_code,
                  int exp_framing, uint32_t exp_cl) {
  size_t n = strlen(head);
  uint8_t buf[1024];
  if (n > sizeof buf) { fprintf(stderr, "  test buffer too small\n"); fails++; return; }
  memcpy(buf, head, n);

  uint16_t code = 0;
  bool chunked = false, has_cl = false;
  uint32_t cl = 0;
  size_t headlen = 0;
  bool ok = http_parse_response_head(buf, n, &code, &chunked, &has_cl, &cl, &headlen);
  int fr = framing_of(chunked, has_cl);

  int bad = 0;
  if (ok != exp_ok) bad = 1;
  if (exp_ok) {
    if (code != exp_code) bad = 1;
    if (fr != exp_framing) bad = 1;
    if (exp_framing == FR_LENGTH && cl != exp_cl) bad = 1;
  }
  if (bad) {
    fails++;
    fprintf(stderr, "  MISMATCH ok=%d(exp %d) code=%u(exp %u) fr=%d(exp %d) cl=%u(exp %u)\n",
            (int)ok, (int)exp_ok, code, exp_code, fr, exp_framing,
            (unsigned)cl, (unsigned)exp_cl);
    fprintf(stderr, "    head=<<%s>>\n", head);
    return;
  }
  fprintf(stderr, "  OK  code=%u framing=%d cl=%u\n", code, fr, (unsigned)cl);
}

int main(void) {
  fprintf(stderr, "─────────────────────────────────────────────────────────────────\n");
  fprintf(stderr, " Verified http_parse_response_head  ->  (code, framing, length)\n");
  fprintf(stderr, "─────────────────────────────────────────────────────────────────\n");

  /* Content-Length responses (varied header order / casing / OWS) */
  check("HTTP/1.1 200 OK\r\nContent-Length: 1256\r\nConnection: close\r\n\r\n",
        true, 200, FR_LENGTH, 1256);
  check("HTTP/1.1 404 Not Found\r\nServer: nginx\r\nContent-Length: 0\r\n\r\n",
        true, 404, FR_LENGTH, 0);
  check("HTTP/1.1 200 OK\r\ncontent-length:42\r\n\r\n",
        true, 200, FR_LENGTH, 42);            /* lowercase name, no OWS */
  check("HTTP/1.1 301 Moved Permanently\r\nLocation: http://x/\r\n"
        "CONTENT-LENGTH:   99\r\n\r\n",
        true, 301, FR_LENGTH, 99);            /* uppercase name, extra OWS */

  /* Chunked responses (chunked must win over any Content-Length) */
  check("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n",
        true, 200, FR_CHUNKED, 0);
  check("HTTP/1.1 200 OK\r\ntransfer-encoding: CHUNKED\r\n\r\n",
        true, 200, FR_CHUNKED, 0);            /* value casing ignored */
  check("HTTP/1.1 200 OK\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n",
        true, 200, FR_CHUNKED, 0);            /* chunked wins */

  /* EOF-framed (no length, no chunked) */
  check("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\n",
        true, 200, FR_EOF, 0);

  /* Realistic example.com-style head */
  check("HTTP/1.1 200 OK\r\n"
        "Age: 12345\r\n"
        "Cache-Control: max-age=604800\r\n"
        "Content-Type: text/html; charset=UTF-8\r\n"
        "Date: Mon, 21 Jul 2026 18:30:00 GMT\r\n"
        "Content-Length: 1256\r\n"
        "Connection: close\r\n\r\n",
        true, 200, FR_LENGTH, 1256);

  /* Malformed / rejected heads */
  check("GET / HTTP/1.1\r\n\r\n", false, 0, 0, 0);          /* not a response */
  check("HTTP/1.0 200 OK\r\n\r\n", false, 0, 0, 0);         /* wrong version prefix */
  check("HTTP/1.1 2x0 OK\r\n\r\n", false, 0, 0, 0);         /* non-digit code */
  check("HTTP/1.1 200 OK\r\nContent-Length: 7\r\n", false, 0, 0, 0); /* no terminator */

  if (fails == 0) {
    fprintf(stderr, "ALL PASS\n");
    return 0;
  }
  fprintf(stderr, "%d FAILURE(S)\n", fails);
  return 1;
}
