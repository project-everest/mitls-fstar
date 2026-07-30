/*
 * connclose_test.c -- concrete C validation of the *verified* Connection: close
 * detector extracted into HTTP_Verified.c from F-star/Pulse.
 *
 * Exercises the extracted, verified leaf
 *
 *   http_connection_close(inp, n, cn, cn_len, cl, cl_len)
 *       -- finds the first `Connection` header (name cn, case-insensitive) in the
 *          header block inp[0..n) and returns true iff its field-value contains
 *          the `close` connection-option token cl (case-insensitive substring).
 *          Returns false when no Connection header is present, so an HTTP/1.1
 *          request defaults to a PERSISTENT (keep-alive) connection.  A server
 *          uses this to decide whether to close the connection after the
 *          response (RFC 7230 6.1).
 *
 * The header block is the bytes AFTER the request line, terminated by the empty
 * CRLF -- exactly what http_parse_header_field walks.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

static void check(const char *label, const char *block, bool want_close) {
  const uint8_t *buf = (const uint8_t *)block;
  size_t n = strlen(block);
  bool got = http_connection_close((uint8_t *)buf, n,
                                   (uint8_t *)"connection", (size_t)10,
                                   (uint8_t *)"close", (size_t)5);
  if (got != want_close) {
    printf("FAIL: [%s] connection_close = %d, want %d\n",
           label, (int)got, (int)want_close);
    fails++;
  }
}

int main(void) {
  /* No Connection header at all -> persistent (false). */
  check("absent", "Host: x\r\nAccept: */*\r\n\r\n", false);

  /* Explicit close token -> true. */
  check("close", "Host: x\r\nConnection: close\r\n\r\n", true);

  /* keep-alive token, not close -> false. */
  check("keep-alive", "Host: x\r\nConnection: keep-alive\r\n\r\n", false);

  /* Case-insensitive header name and value -> true. */
  check("mixed-case", "Host: x\r\nCONNECTION: Close\r\n\r\n", true);

  /* close appearing in a comma-separated option list -> true. */
  check("list", "Host: x\r\nConnection: keep-alive, close\r\n\r\n", true);

  /* Empty header block -> no Connection header -> false. */
  check("empty", "\r\n", false);

  /* A different header whose value merely mentions close should NOT be read as a
     Connection: close (the name must match). */
  check("wrong-name", "Host: x\r\nX-Note: please close soon\r\n\r\n", false);

  if (fails == 0) {
    printf("connclose_test: ALL PASS\n");
    return 0;
  }
  printf("connclose_test: %d FAILURE(S)\n", fails);
  return 1;
}
