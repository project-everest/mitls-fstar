/*
 * limits_test.c -- concrete C validation of the *verified* header-block limit
 * enforcer extracted into HTTP_Verified.c from F-star/Pulse.
 *
 * Exercises the extracted, verified leaf
 *
 *   http_header_limits_ok(inp, n, max_headers, max_line)
 *       -- walks the header block inp[0..n) field-line by field-line and returns
 *          false as soon as either the number of field-lines exceeds
 *          max_headers, or any single field-line (including its terminating
 *          CRLF) is longer than max_line bytes; true otherwise.  A server
 *          answers 431 Request Header Fields Too Large when this is false.
 *
 * The header block is the bytes AFTER the request line, terminated by the empty
 * CRLF -- exactly what http_parse_header_field walks.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

static void check(const char *label, const char *block,
                  size_t max_headers, size_t max_line, bool want_ok) {
  const uint8_t *buf = (const uint8_t *)block;
  size_t n = strlen(block);
  bool got = http_header_limits_ok((uint8_t *)buf, n, max_headers, max_line);
  if (got != want_ok) {
    printf("FAIL: [%s] limits_ok(max_headers=%zu, max_line=%zu) = %d, want %d\n",
           label, max_headers, max_line, (int)got, (int)want_ok);
    fails++;
  }
}

int main(void) {
  /* Three short header lines, generous limits -> ok. */
  {
    const char *b = "Host: x\r\nAccept: */*\r\nConnection: close\r\n\r\n";
    check("within", b, 16, 1024, true);
  }

  /* Same block, header-count cap of 2 (there are 3) -> reject. */
  {
    const char *b = "Host: x\r\nAccept: */*\r\nConnection: close\r\n\r\n";
    check("too-many", b, 2, 1024, false);
  }

  /* Header-count cap exactly at the number of lines -> ok (boundary). */
  {
    const char *b = "Host: x\r\nAccept: */*\r\nConnection: close\r\n\r\n";
    check("count-boundary", b, 3, 1024, true);
  }

  /* One oversized line -> reject even with a high count cap.
     "X: " + 40 'a' + CRLF = 45 bytes; cap the line at 20. */
  {
    const char *b =
        "Host: x\r\n"
        "X: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\r\n"
        "\r\n";
    check("long-line", b, 16, 20, false);
  }

  /* The same oversized line with a line cap that admits it -> ok. */
  {
    const char *b =
        "Host: x\r\n"
        "X: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\r\n"
        "\r\n";
    check("long-line-ok", b, 16, 64, true);
  }

  /* Empty header block (immediate CRLF) -> zero lines, ok. */
  {
    const char *b = "\r\n";
    check("empty", b, 0, 8, true);
  }

  if (fails == 0) {
    printf("limits_test: ALL PASS\n");
    return 0;
  }
  printf("limits_test: %d FAILURE(S)\n", fails);
  return 1;
}
