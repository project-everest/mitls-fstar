/*
 * request_emit_test.c -- concrete C validation of the *verified* HTTP/1.1
 * origin-server GET request emitter extracted into HTTP_Verified.c.
 *
 * Exercises the extracted, verified F-star/Pulse leaf
 *   http_emit_request_host (HTTP.Impl.Codec.Request) -- builds
 *       "GET " <target> " HTTP/1.1" CRLF "Host: " <host> CRLF
 *       "Connection: close" CRLF CRLF
 *
 * Unlike http_emit_request, this carries the mandatory HTTP/1.1 Host header (and
 * Connection: close), so it is what a client actually sends to a real web server
 * (e.g. GET http://example.com/).  This pins the emitter against an independent
 * snprintf reference for a spread of target/host inputs; a mismatch would catch
 * an extraction-level regression the F-star proof (about the spec
 * ser_request_host, not the C) cannot.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

static void check(const char *target, const char *host) {
  size_t tlen = strlen(target);
  size_t hlen = strlen(host);
  size_t total = 4 + tlen + 17 + hlen + 23;

  uint8_t out[512];
  if (total > sizeof out) {
    fprintf(stderr, "  test buffer too small\n");
    fails++;
    return;
  }
  memset(out, 0xAA, sizeof out);
  http_emit_request_host((uint8_t *)target, tlen, (uint8_t *)host, hlen, out);

  char ref[512];
  int n = snprintf(ref, sizeof ref,
                   "GET %s HTTP/1.1\r\nHost: %s\r\nConnection: close\r\n\r\n",
                   target, host);

  if ((size_t)n != total || memcmp(out, ref, total) != 0) {
    fails++;
    fprintf(stderr, "  MISMATCH target='%s' host='%s'\n", target, host);
    fprintf(stderr, "    got: "); for (size_t i = 0; i < total; i++) fprintf(stderr, "%02x", out[i]);
    fprintf(stderr, "\n    ref: "); for (size_t i = 0; i < total; i++) fprintf(stderr, "%02x", (uint8_t)ref[i]);
    fprintf(stderr, "\n");
    return;
  }
  fprintf(stderr, "  OK  (%zu bytes) GET %s ... Host: %s\n", total, target, host);
}

int main(void) {
  fprintf(stderr, "─────────────────────────────────────────────────────────────────\n");
  fprintf(stderr, " Verified http_emit_request_host  ->  byte-exact snprintf reference\n");
  fprintf(stderr, "─────────────────────────────────────────────────────────────────\n");

  check("/", "example.com");
  check("/index.html", "www.example.com");
  check("/a/b/c/deep/path", "host.local");
  check("/", "a");
  check("/very/long/path/that/exercises/the/copy/loop/repeatedly", "some.longer.hostname.example.org");

  if (fails == 0) {
    fprintf(stderr, "ALL PASS\n");
    return 0;
  }
  fprintf(stderr, "%d FAILURE(S)\n", fails);
  return 1;
}
