/*
 * response_emit_var_test.c -- concrete C validation of the *verified*
 * variable-width Content-Length response-head emitter extracted into
 * HTTP_Verified.c.
 *
 * Exercises the extracted, verified F-star/Pulse leaf
 *   http_emit_response_var (code, len, out)
 *       -- writes  "HTTP/1.1 <ddd> \r\nContent-Length: <minimal-width len>\r\n\r\n"
 *          i.e. ser_response_var, into a buffer sized  35 + dec_width(len).
 *
 * Unlike the fixed-width http_emit_response (which pads Content-Length to 8
 * digits: "00000025"), this emits the RFC-canonical minimal width ("25"),
 * which real peers send.  We check:
 *   (1) byte-exactness against an independent snprintf reference, and
 *   (2) that the head round-trips through the verified parser
 *       http_parse_response_head, recovering (code, framing=LENGTH, cl).
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

enum { FR_EOF = 0, FR_LENGTH = 1, FR_CHUNKED = 2 };

/* number of decimal digits in n (>=1, "0" is one digit) */
static size_t dec_width_c(uint32_t n) {
  size_t d = 1;
  while (n >= 10) { n /= 10; d++; }
  return d;
}

static void check(uint16_t code, uint32_t len) {
  size_t D = dec_width_c(len);
  size_t total = 35 + D;

  uint8_t out[64];
  memset(out, 0xAA, sizeof out);          /* poison to catch under-writes */
  http_emit_response_var(code, len, out);

  /* independent reference */
  char ref[64];
  int rn = snprintf(ref, sizeof ref,
                    "HTTP/1.1 %03u \r\nContent-Length: %u\r\n\r\n",
                    (unsigned)code, (unsigned)len);

  int bad = 0;
  if ((size_t)rn != total) {
    bad = 1;
    fprintf(stderr, "  LENGTH MISMATCH ref=%d expected total=%zu\n", rn, total);
  } else if (memcmp(out, ref, total) != 0) {
    bad = 1;
    fprintf(stderr, "  BYTE MISMATCH\n");
    fprintf(stderr, "    got=<<%.*s>>\n", (int)total, (const char *)out);
    fprintf(stderr, "    ref=<<%.*s>>\n", rn, ref);
  }

  /* round-trip through the verified parser */
  /* round-trip through the verified parser.  Note: parse_dec_at clamps the
     recovered Content-Length at max_len8-1 == 99999999, so for len >= 1e8 the
     parser reports the clamp, not len. */
  uint32_t exp_cl = (len < 100000000u) ? len : 99999999u;
  uint16_t pcode = 0;
  bool chunked = false, has_cl = false;
  uint32_t cl = 0;
  size_t headlen = 0;
  bool ok = http_parse_response_head(out, total, &pcode, &chunked, &has_cl,
                                     &cl, &headlen);
  if (!ok || pcode != code || chunked || !has_cl || cl != exp_cl) {
    bad = 1;
    fprintf(stderr,
            "  PARSE MISMATCH ok=%d code=%u(exp %u) chunked=%d has_cl=%d "
            "cl=%u(exp %u)\n",
            (int)ok, pcode, code, (int)chunked, (int)has_cl, (unsigned)cl,
            (unsigned)exp_cl);
  }

  if (bad) {
    fails++;
    return;
  }
  fprintf(stderr, "  OK  code=%u len=%u width=%zu head=<<%.*s>>\n", code,
          (unsigned)len, D, (int)total, (const char *)out);
}

int main(void) {
  fprintf(stderr, "─────────────────────────────────────────────────────────────────\n");
  fprintf(stderr, " Verified http_emit_response_var  ->  ser_response_var (minimal CL)\n");
  fprintf(stderr, "─────────────────────────────────────────────────────────────────\n");

  check(200, 0);            /* 1-digit  */
  check(200, 5);            /* 1-digit  */
  check(200, 9);
  check(200, 10);           /* 2-digit boundary */
  check(404, 42);
  check(301, 99);
  check(200, 100);          /* 3-digit boundary */
  check(200, 255);
  check(500, 1256);         /* 4-digit  */
  check(200, 9999);
  check(200, 10000);        /* 5-digit  */
  check(206, 65535);        /* block-size cap */
  check(200, 65536);
  check(200, 1000000);      /* 7-digit  */
  check(200, 99999999);     /* 8-digit  */
  check(200, 100000000);    /* 9-digit  */
  check(200, 4294967295u);  /* 10-digit UINT32_MAX */

  if (fails) {
    fprintf(stderr, "\n  %d CASE(S) FAILED\n", fails);
    return 1;
  }
  fprintf(stderr, "\n  ALL EMIT-VAR CASES PASS\n");
  return 0;
}
