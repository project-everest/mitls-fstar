/*
 * request_line_test.c -- concrete C validation of the *verified* method-aware
 * HTTP/1.1 request-line parser extracted into HTTP_Verified.c from F-star/Pulse.
 *
 * Exercises the extracted, verified leaf
 *   http_parse_request_line(inp, n, &ok, &mlen, &toff, &tlen)
 *       -- parses  METHOD SP target SP "HTTP/1.1" CRLF  (ignoring all headers)
 *          out of inp[0..n).  On success ok==1,
 *          method = inp[0    .. mlen),
 *          target = inp[toff .. toff+tlen).
 *          On a malformed line (no method/target space, or wrong version
 *          token) ok==0.
 *
 * The verification proves each success ties to the pure spec
 * HTTP.Wire.Length.parse_request_line_m; here we independently confirm the
 * recovered method/target byte-slices on concrete request heads, including a
 * real curl-style POST head with trailing headers.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

/* Parse the request line at the head of `s`; assert method/target recovered. */
static void expect_line(const char *s, const char *method, const char *target) {
  const uint8_t *buf = (const uint8_t *)s;
  size_t n = strlen(s);
  bool ok = false;
  size_t mlen = 0, toff = 0, tlen = 0;
  http_parse_request_line((uint8_t *)buf, n, &ok, &mlen, &toff, &tlen);
  if (!ok) {
    printf("FAIL: '%.*s...' expected ok, got ok=0\n", 16, s);
    fails++;
    return;
  }
  size_t eml = strlen(method), etl = strlen(target);
  if (mlen != eml || memcmp(buf, method, eml) != 0) {
    printf("FAIL: method mismatch (got mlen=%zu '%.*s', want '%s')\n",
           mlen, (int)mlen, buf, method);
    fails++;
  }
  if (tlen != etl || memcmp(buf + toff, target, etl) != 0) {
    printf("FAIL: target mismatch (got tlen=%zu '%.*s', want '%s')\n",
           tlen, (int)tlen, buf + toff, target);
    fails++;
  }
}

/* Assert the request line at the head of `s` is rejected (ok==0). */
static void expect_bad(const char *s) {
  const uint8_t *buf = (const uint8_t *)s;
  size_t n = strlen(s);
  bool ok = true;
  size_t mlen = 0, toff = 0, tlen = 0;
  http_parse_request_line((uint8_t *)buf, n, &ok, &mlen, &toff, &tlen);
  if (ok) {
    printf("FAIL: '%.*s...' expected reject, got ok=1\n", 16, s);
    fails++;
  }
}

int main(void) {
  /* real curl-style POST head with headers after the version token */
  expect_line("POST /submit HTTP/1.1\r\n"
              "Host: example.com\r\n"
              "Content-Length: 5\r\n"
              "\r\nhello",
              "POST", "/submit");

  /* GET, minimal */
  expect_line("GET / HTTP/1.1\r\n\r\n", "GET", "/");

  /* other methods */
  expect_line("DELETE /a/b/c HTTP/1.1\r\nHost: h\r\n\r\n", "DELETE", "/a/b/c");
  expect_line("PUT /x?y=1 HTTP/1.1\r\n\r\n", "PUT", "/x?y=1");
  expect_line("OPTIONS * HTTP/1.1\r\n\r\n", "OPTIONS", "*");

  /* empty target (two adjacent spaces) still parses, target == "" */
  expect_line("HEAD  HTTP/1.1\r\n\r\n", "HEAD", "");

  /* rejects */
  expect_bad("GET / HTTP/2.0\r\n\r\n");      /* wrong version token   */
  expect_bad("GET /onlyoneword\r\n\r\n");    /* no second space       */
  expect_bad("NOSPACEATALL\r\n\r\n");        /* no first space        */
  expect_bad("GET /x HTTP/1.1");             /* version token truncated */

  if (fails == 0) {
    printf("request_line_test: ALL PASS\n");
    return 0;
  }
  printf("request_line_test: %d FAILURE(S)\n", fails);
  return 1;
}
