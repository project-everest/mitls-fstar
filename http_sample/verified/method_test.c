/*
 * method_test.c -- concrete C validation of the *verified* request-line
 * validation + method classification leaves extracted into HTTP_Verified.c from
 * F-star/Pulse.
 *
 * Exercises two extracted, verified leaves:
 *
 *   http_request_line_ok(inp, n)
 *       -- true iff inp[0..n) begins with a well-formed request line
 *          (METHOD SP target SP "HTTP/1.1" CRLF).  A server answers 400 Bad
 *          Request when this is false.
 *
 *   http_method_known(inp, n)
 *       -- true iff the request line parses AND its method token is one of the
 *          eight standard HTTP methods (GET, HEAD, POST, PUT, DELETE, CONNECT,
 *          OPTIONS, TRACE).  A server answers 501 Not Implemented when the line
 *          parses but this is false.
 *
 * Method matching is exact and case-sensitive (HTTP methods are upper-case
 * tokens), so "get" is NOT recognized.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

static void check(const char *label, const char *s,
                  bool want_line_ok, bool want_known) {
  const uint8_t *buf = (const uint8_t *)s;
  size_t n = strlen(s);
  bool line_ok = http_request_line_ok((uint8_t *)buf, n);
  bool known = http_method_known((uint8_t *)buf, n);
  if (line_ok != want_line_ok) {
    printf("FAIL: [%s] line_ok = %d, want %d\n", label, (int)line_ok, (int)want_line_ok);
    fails++;
  }
  if (known != want_known) {
    printf("FAIL: [%s] method_known = %d, want %d\n", label, (int)known, (int)want_known);
    fails++;
  }
}

static void check_allowed(const char *label, const char *s, bool want_allowed) {
  const uint8_t *buf = (const uint8_t *)s;
  size_t n = strlen(s);
  bool allowed = http_method_allowed((uint8_t *)buf, n);
  if (allowed != want_allowed) {
    printf("FAIL: [%s] method_allowed = %d, want %d\n", label, (int)allowed, (int)want_allowed);
    fails++;
  }
}

int main(void) {
  /* All eight standard methods -> line ok, method known. */
  check("get",     "GET / HTTP/1.1\r\nHost: x\r\n\r\n",            true, true);
  check("head",    "HEAD / HTTP/1.1\r\n\r\n",                      true, true);
  check("post",    "POST /submit HTTP/1.1\r\nHost: x\r\n\r\n",     true, true);
  check("put",     "PUT /r HTTP/1.1\r\n\r\n",                      true, true);
  check("delete",  "DELETE /r HTTP/1.1\r\n\r\n",                   true, true);
  check("options", "OPTIONS * HTTP/1.1\r\n\r\n",                   true, true);
  check("trace",   "TRACE / HTTP/1.1\r\n\r\n",                     true, true);
  check("connect", "CONNECT h:443 HTTP/1.1\r\n\r\n",               true, true);

  /* Syntactically valid line, unknown method -> line ok, NOT known (-> 501). */
  check("frobnicate", "FROBNICATE / HTTP/1.1\r\n\r\n",             true, false);
  check("patch",      "PATCH /r HTTP/1.1\r\n\r\n",                 true, false);

  /* Case-sensitive: lower-case method is not a known token. */
  check("lower-get",  "get / HTTP/1.1\r\n\r\n",                    true, false);

  /* Prefix/substring must not match a known method (length is exact). */
  check("ge",         "GE / HTTP/1.1\r\n\r\n",                     true, false);
  check("gett",       "GETT / HTTP/1.1\r\n\r\n",                   true, false);

  /* Malformed request lines -> line NOT ok (-> 400), and hence not known. */
  check("garbage",    "garbage\r\n\r\n",                           false, false);
  check("no-spaces",  "GET/HTTP/1.1\r\n\r\n",                      false, false);
  check("bad-ver",    "GET / HTTP/9.9\r\n\r\n",                    false, false);
  check("empty-meth", " / HTTP/1.1\r\n\r\n",                       false, false);

  /* http_method_allowed: this server implements only GET / HEAD / POST. */
  check_allowed("allow-get",     "GET / HTTP/1.1\r\n\r\n",         true);
  check_allowed("allow-head",    "HEAD / HTTP/1.1\r\n\r\n",        true);
  check_allowed("allow-post",    "POST /s HTTP/1.1\r\n\r\n",       true);
  check_allowed("deny-put",      "PUT /r HTTP/1.1\r\n\r\n",        false);
  check_allowed("deny-delete",   "DELETE /r HTTP/1.1\r\n\r\n",     false);
  check_allowed("deny-options",  "OPTIONS * HTTP/1.1\r\n\r\n",     false);
  check_allowed("deny-connect",  "CONNECT h:1 HTTP/1.1\r\n\r\n",   false);
  check_allowed("deny-unknown",  "FROBNICATE / HTTP/1.1\r\n\r\n",  false);
  check_allowed("deny-badline",  "garbage\r\n\r\n",                false);

  if (fails == 0) {
    printf("method_test: ALL PASS\n");
    return 0;
  }
  printf("method_test: %d FAILURE(S)\n", fails);
  return 1;
}
