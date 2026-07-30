/*
 * request_post_test.c -- concrete C validation of the *verified* HTTP/1.1 POST
 * request-head emitter extracted into HTTP_Verified.c from F-star/Pulse.
 *
 * Exercises the extracted, verified leaf
 *   http_emit_request_post(target, target_len, len, out)
 *       -- writes a byte-exact POST request head into out[0 .. 36+target_len+d)
 *          (d = decimal width of len):
 *            "POST " target " HTTP/1.1\r\nContent-Length: " <len> "\r\n\r\n"
 *
 * The verification proves the emitted bytes equal the pure spec
 * HTTP.Wire.Length.ser_request_post; here we independently confirm the exact
 * wire bytes for several (target, Content-Length) pairs, including the
 * variable-width digit run (len = 0, 5, 255, 1000000).
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

/* decimal width of n (minimal, "0" -> 1). */
static size_t dec_width(uint32_t n) {
  size_t d = 1;
  while (n >= 10) { n /= 10; d++; }
  return d;
}

/* Emit a POST head for (target, len); assert it equals the expected wire string. */
static void expect_post(const char *target, uint32_t len, const char *expected) {
  size_t tl = strlen(target);
  size_t d = dec_width(len);
  size_t olen = 36 + tl + d;
  uint8_t out[512];
  if (olen > sizeof out) { printf("FAIL: buffer too small\n"); fails++; return; }
  memset(out, 0xAB, sizeof out);
  http_emit_request_post((uint8_t *)target, tl, len, out);

  size_t elen = strlen(expected);
  if (olen != elen) {
    printf("FAIL: target='%s' len=%u -- olen=%zu != expected len=%zu\n",
           target, len, olen, elen);
    fails++;
    return;
  }
  if (memcmp(out, expected, olen) != 0) {
    printf("FAIL: target='%s' len=%u -- bytes differ\n  got:      ", target, len);
    for (size_t i = 0; i < olen; i++) putchar(out[i] < 32 ? '.' : out[i]);
    printf("\n  expected: ");
    for (size_t i = 0; i < olen; i++) putchar(expected[i] < 32 ? '.' : expected[i]);
    putchar('\n');
    fails++;
    return;
  }
  printf("  ok: target='%s' len=%u -> %zu-byte head byte-exact\n", target, len, olen);
}

int main(void) {
  printf("─────────────────────────────────────────────────────────────────\n");
  printf(" Verified http_emit_request_post  ->  ser_request_post\n");
  printf("─────────────────────────────────────────────────────────────────\n");

  expect_post("/submit", 5,
              "POST /submit HTTP/1.1\r\nContent-Length: 5\r\n\r\n");
  expect_post("/", 0,
              "POST / HTTP/1.1\r\nContent-Length: 0\r\n\r\n");
  expect_post("/api/v1/things", 255,
              "POST /api/v1/things HTTP/1.1\r\nContent-Length: 255\r\n\r\n");
  expect_post("/upload", 1000000,
              "POST /upload HTTP/1.1\r\nContent-Length: 1000000\r\n\r\n");

  if (fails == 0) { printf("request_post_test: ALL PASS\n"); return 0; }
  printf("request_post_test: %d FAILURE(S)\n", fails);
  return 1;
}
