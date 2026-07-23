/*
 * header_parse_test.c -- concrete C validation of the *verified* single-line
 * HTTP/1.1 header-field parser and its iterator driver, both extracted into
 * HTTP_Verified.c from F-star/Pulse.
 *
 * Exercises two extracted, verified leaves:
 *
 *   http_parse_header_field(inp, n, start,
 *                           &is_end, &ok, &nlen, &voff, &vlen, &next)
 *       -- parses ONE  field-line = field-name ":" OWS field-value OWS CRLF
 *          out of inp[start..n).  On a well-formed line: ok==1, is_end==0,
 *          name  = inp[start .. start+nlen),
 *          value = inp[voff  .. voff+vlen),   (value runs up to the CR;
 *                                              leading OWS after ':' skipped)
 *          next  = offset just past this line's CRLF.
 *          On the terminating empty line (CRLF): is_end==1.
 *          On a malformed line: ok==0, is_end==0.
 *
 *   http_count_headers(inp, n)
 *       -- walks the block field-by-field from offset 0 and returns the number
 *          of well-formed field-lines before the terminating empty CRLF.
 *
 * The verification proves each success ties to the pure spec
 * HTTP.Wire.Header.parse_field; here we independently confirm the recovered
 * (name, value) byte-slices and cursor advance on concrete inputs.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

/* Parse one field at `start`; assert it is a well-formed line whose recovered
 * name/value slices equal the given C strings, and return `next`. */
static size_t expect_field(const uint8_t *buf, size_t n, size_t start,
                           const char *name, const char *val) {
  bool is_end = true, ok = false;
  size_t nlen = 0, voff = 0, vlen = 0, next = 0;
  http_parse_header_field((uint8_t *)buf, n, start,
                          &is_end, &ok, &nlen, &voff, &vlen, &next);
  if (is_end || !ok) {
    printf("FAIL: field@%zu expected ok, got is_end=%d ok=%d\n",
           start, (int)is_end, (int)ok);
    fails++;
    return next;
  }
  size_t enlen = strlen(name), evlen = strlen(val);
  if (nlen != enlen || memcmp(buf + start, name, enlen) != 0) {
    printf("FAIL: field@%zu name mismatch (got nlen=%zu, want '%s')\n",
           start, nlen, name);
    fails++;
  }
  if (vlen != evlen || memcmp(buf + voff, val, evlen) != 0) {
    printf("FAIL: field@%zu value mismatch (got vlen=%zu '%.*s', want '%s')\n",
           start, vlen, (int)vlen, buf + voff, val);
    fails++;
  }
  return next;
}

/* Assert the field at `start` is the terminating empty CRLF. */
static void expect_end(const uint8_t *buf, size_t n, size_t start) {
  bool is_end = false, ok = false;
  size_t nlen = 0, voff = 0, vlen = 0, next = 0;
  http_parse_header_field((uint8_t *)buf, n, start,
                          &is_end, &ok, &nlen, &voff, &vlen, &next);
  if (!is_end) {
    printf("FAIL: field@%zu expected end-of-headers, got is_end=0 ok=%d\n",
           start, (int)ok);
    fails++;
  }
}

/* Assert the field at `start` is malformed (no colon / not a header line). */
static void expect_bad(const uint8_t *buf, size_t n, size_t start) {
  bool is_end = false, ok = true;
  size_t nlen = 0, voff = 0, vlen = 0, next = 0;
  http_parse_header_field((uint8_t *)buf, n, start,
                          &is_end, &ok, &nlen, &voff, &vlen, &next);
  if (is_end || ok) {
    printf("FAIL: field@%zu expected malformed, got is_end=%d ok=%d\n",
           start, (int)is_end, (int)ok);
    fails++;
  }
}

static void check_count(const uint8_t *buf, size_t n, size_t want) {
  size_t got = http_count_headers((uint8_t *)buf, n);
  if (got != want) {
    printf("FAIL: count_headers got %zu, want %zu\n", got, want);
    fails++;
  }
}

int main(void) {
  /* ---- 1. A normal header block, iterated field-by-field ---------------- */
  {
    const char *s =
        "Host: example.com\r\n"            /* single SP after ':'            */
        "Content-Length:   42\r\n"         /* multiple OWS after ':'         */
        "X-Trailing: value  \r\n"          /* trailing OWS kept in value     */
        "A:B\r\n"                          /* minimal, no OWS                */
        "X-Empty:\r\n"                     /* empty value                    */
        "\r\n";                            /* terminator                     */
    const uint8_t *buf = (const uint8_t *)s;
    size_t n = strlen(s);

    size_t p = 0;
    p = expect_field(buf, n, p, "Host", "example.com");
    p = expect_field(buf, n, p, "Content-Length", "42");
    p = expect_field(buf, n, p, "X-Trailing", "value  ");
    p = expect_field(buf, n, p, "A", "B");
    p = expect_field(buf, n, p, "X-Empty", "");
    expect_end(buf, n, p);

    check_count(buf, n, 5);
  }

  /* ---- 2. Empty block: first line is the terminator --------------------- */
  {
    const char *s = "\r\n";
    const uint8_t *buf = (const uint8_t *)s;
    size_t n = strlen(s);
    expect_end(buf, n, 0);
    check_count(buf, n, 0);
  }

  /* ---- 3. Malformed line (no colon) stops the walk --------------------- */
  {
    const char *s =
        "Good: yes\r\n"
        "NoColonHere\r\n"
        "\r\n";
    const uint8_t *buf = (const uint8_t *)s;
    size_t n = strlen(s);
    size_t p = expect_field(buf, n, 0, "Good", "yes");
    expect_bad(buf, n, p);
    /* count stops at the malformed line: only the first field counts */
    check_count(buf, n, 1);
  }

  /* ---- 4. A single field with a long value ----------------------------- */
  {
    const char *s = "User-Agent: curl/8.5.0 (verified-parse)\r\n\r\n";
    const uint8_t *buf = (const uint8_t *)s;
    size_t n = strlen(s);
    size_t p = expect_field(buf, n, 0, "User-Agent", "curl/8.5.0 (verified-parse)");
    expect_end(buf, n, p);
    check_count(buf, n, 1);
  }

  if (fails == 0) {
    printf("header_parse_test: ALL PASS\n");
    return 0;
  }
  printf("header_parse_test: %d FAILURE(S)\n", fails);
  return 1;
}
