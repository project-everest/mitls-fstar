/*
 * framing_test.c -- concrete C validation of the *verified* request-framing
 * anti-smuggling guard, extracted into HTTP_Verified.c from F-star/Pulse.
 *
 * Exercises two extracted, verified leaves:
 *
 *   http_count_header_named(inp, n, nm, nm_len)
 *       -- walks the header block inp[0..n) field-by-field and returns how many
 *          well-formed field-lines have field-name == nm[0..nm_len)
 *          (case-insensitive, exact length).
 *
 *   http_request_framing_ok(inp, n, cl, cl_len, te, te_len)
 *       -- returns false (reject) iff the block carries a Content-Length
 *          alongside a Transfer-Encoding, or more than one Content-Length line
 *          (RFC 7230 3.3.3 request-smuggling vectors); true otherwise.
 *
 * The header block is the bytes AFTER the request line, terminated by the empty
 * CRLF -- exactly what http_parse_header_field walks.  Both `cl` and `te` needle
 * names are given lower-case; matching is case-insensitive so mixed-case header
 * names in the block still match.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

static const uint8_t CL[] = "content-length";
static const uint8_t TE[] = "transfer-encoding";
#define CL_LEN (sizeof(CL) - 1)
#define TE_LEN (sizeof(TE) - 1)

static void check_count(const char *label, const char *block,
                        const uint8_t *nm, size_t nm_len, size_t want) {
  const uint8_t *buf = (const uint8_t *)block;
  size_t n = strlen(block);
  size_t got = http_count_header_named((uint8_t *)buf, n, (uint8_t *)nm, nm_len);
  if (got != want) {
    printf("FAIL: [%s] count('%.*s') = %zu, want %zu\n",
           label, (int)nm_len, nm, got, want);
    fails++;
  }
}

static void check_framing(const char *label, const char *block, bool want_ok) {
  const uint8_t *buf = (const uint8_t *)block;
  size_t n = strlen(block);
  bool got = http_request_framing_ok((uint8_t *)buf, n,
                                     (uint8_t *)CL, CL_LEN,
                                     (uint8_t *)TE, TE_LEN);
  if (got != want_ok) {
    printf("FAIL: [%s] framing_ok = %d, want %d\n",
           label, (int)got, (int)want_ok);
    fails++;
  }
}

int main(void) {
  /* 1. Content-Length only -> unambiguous, accept. */
  {
    const char *b = "Host: x\r\nContent-Length: 5\r\n\r\n";
    check_count("cl-only", b, CL, CL_LEN, 1);
    check_count("cl-only", b, TE, TE_LEN, 0);
    check_framing("cl-only", b, true);
  }

  /* 2. Transfer-Encoding only -> unambiguous, accept. */
  {
    const char *b = "Host: x\r\nTransfer-Encoding: chunked\r\n\r\n";
    check_count("te-only", b, CL, CL_LEN, 0);
    check_count("te-only", b, TE, TE_LEN, 1);
    check_framing("te-only", b, true);
  }

  /* 3. Content-Length + Transfer-Encoding -> smuggling vector, reject. */
  {
    const char *b =
        "Host: x\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n";
    check_count("cl+te", b, CL, CL_LEN, 1);
    check_count("cl+te", b, TE, TE_LEN, 1);
    check_framing("cl+te", b, false);
  }

  /* 4. Duplicate Content-Length -> smuggling vector, reject. */
  {
    const char *b =
        "Content-Length: 5\r\nHost: x\r\nContent-Length: 6\r\n\r\n";
    check_count("dup-cl", b, CL, CL_LEN, 2);
    check_framing("dup-cl", b, false);
  }

  /* 5. Neither framing header -> accept. */
  {
    const char *b = "Host: x\r\nAccept: */*\r\n\r\n";
    check_count("neither", b, CL, CL_LEN, 0);
    check_count("neither", b, TE, TE_LEN, 0);
    check_framing("neither", b, true);
  }

  /* 6. Mixed-case names still match (case-insensitive). */
  {
    const char *b =
        "Host: x\r\ncOnTeNt-LeNgTh: 5\r\nTRANSFER-ENCODING: chunked\r\n\r\n";
    check_count("mixed-case", b, CL, CL_LEN, 1);
    check_count("mixed-case", b, TE, TE_LEN, 1);
    check_framing("mixed-case", b, false);
  }

  if (fails == 0) {
    printf("framing_test: ALL PASS\n");
    return 0;
  }
  printf("framing_test: %d FAILURE(S)\n", fails);
  return 1;
}
