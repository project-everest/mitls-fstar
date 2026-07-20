/*
 * head_emit_test.c -- concrete C validation of the *verified* HTTP/1.1 head
 * emitters extracted into HTTP_Verified.c.
 *
 * Exercises the extracted, verified F-star/Pulse leaves
 *   http_emit_response (HTTP.Impl.Codec.Length) -- builds the 43-byte head
 *       "HTTP/1.1 " ddd " CRLF Content-Length: " dddddddd CRLF CRLF
 *   http_emit_request  (HTTP.Impl.Codec.Length) -- builds
 *       "GET " <target> " HTTP/1.1" CRLF CRLF
 *
 * This pins the emitters against an independent reference built with
 * snprintf/memcpy for a spread of inputs.  A mismatch here would catch an
 * extraction-level regression that the F-star proof (which is about the spec
 * ser_response/ser_request, not the C) cannot.
 *
 * It also round-trips through the verified recv-head parser
 *   http_recv_response (HTTP.Impl.Codec.Length) -- parses the 43-byte head back
 *       to (code,len), returning false on anything that is not a valid head,
 * checking that emit-then-recv recovers the original (code,len) and that a
 * corrupted head is rejected.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int fails = 0;

static void check_response(uint16_t code, uint32_t len) {
  uint8_t out[43];
  memset(out, 0xAA, sizeof out);
  http_emit_response(code, len, out);

  uint8_t ref[43];
  char big[64];
  snprintf(big, sizeof big,
           "HTTP/1.1 %03u \r\nContent-Length: %08u\r\n\r\n",
           (unsigned)code, (unsigned)len);
  memcpy(ref, big, 43);

  if (memcmp(out, ref, 43) != 0) {
    fails++;
    fprintf(stderr, "  MISMATCH response code=%u len=%u\n", (unsigned)code, (unsigned)len);
    fprintf(stderr, "    got: "); for (int i = 0; i < 43; i++) fprintf(stderr, "%02x", out[i]);
    fprintf(stderr, "\n    ref: "); for (int i = 0; i < 43; i++) fprintf(stderr, "%02x", ref[i]);
    fprintf(stderr, "\n");
    return;
  }

  /* Round-trip: the verified parser must recover the original (code,len). */
  uint16_t rcode = 0;
  uint32_t rlen = 0;
  if (!http_recv_response(out, &rcode, &rlen)) {
    fails++;
    fprintf(stderr, "  RECV rejected a valid head code=%u len=%u\n",
            (unsigned)code, (unsigned)len);
    return;
  }
  if (rcode != code || rlen != len) {
    fails++;
    fprintf(stderr, "  RECV mismatch: emitted (%u,%u) but parsed (%u,%u)\n",
            (unsigned)code, (unsigned)len, (unsigned)rcode, (unsigned)rlen);
    return;
  }
  printf("  ok  response code=%u len=%u -> recv (%u,%u)\n", (unsigned)code,
         (unsigned)len, (unsigned)rcode, (unsigned)rlen);
}

/* A head with one byte corrupted must be rejected by the verified parser. */
static void check_reject(uint16_t code, uint32_t len, int pos, uint8_t val) {
  uint8_t buf[43];
  http_emit_response(code, len, buf);
  buf[pos] = val;
  uint16_t rcode = 0;
  uint32_t rlen = 0;
  if (http_recv_response(buf, &rcode, &rlen)) {
    fails++;
    fprintf(stderr, "  RECV accepted a corrupted head (pos=%d val=%02x)\n", pos, val);
  } else {
    printf("  ok  reject corrupted head pos=%d val=%02x\n", pos, val);
  }
}

static void check_request(const char *target) {
  size_t tlen = strlen(target);
  size_t olen = 4 + tlen + 13;
  uint8_t out[512];
  if (olen > sizeof out) { fprintf(stderr, "target too long for test\n"); fails++; return; }
  memset(out, 0xAA, sizeof out);
  http_emit_request((uint8_t *)target, tlen, out);

  uint8_t ref[512];
  size_t p = 0;
  memcpy(ref + p, "GET ", 4); p += 4;
  memcpy(ref + p, target, tlen); p += tlen;
  memcpy(ref + p, " HTTP/1.1\r\n\r\n", 13); p += 13;

  if (memcmp(out, ref, olen) != 0) {
    fails++;
    fprintf(stderr, "  MISMATCH request target=\"%s\"\n", target);
  } else {
    printf("  ok  request  target=\"%s\" -> \"GET %s HTTP/1.1\\r\\n\\r\\n\"\n", target, target);
  }
}

int main(void) {
  printf("── verified HTTP head-emitter self-test ──\n");

  /* Content-Length body head: boundary + spread inputs. */
  check_response(100u, 0u);
  check_response(200u, 1u);
  check_response(404u, 1300u);
  check_response(599u, 65535u);
  check_response(301u, 99999999u);   /* max Content-Length (< 10^8) */
  check_response(500u, 12345678u);

  /* Corrupted response heads must be rejected (not parsed as valid). */
  check_reject(200u, 1u, 0, 'X');       /* wrong literal prefix byte     */
  check_reject(200u, 1u, 9, 'a');       /* non-digit in the status code  */
  check_reject(200u, 1u, 31, ':');      /* non-digit in Content-Length   */
  check_reject(200u, 1u, 41, 'Z');      /* wrong trailing CRLF byte      */
  check_reject(200u, 1u, 9, '0');       /* code 000 (< 100) rejected     */

  /* Request line: various targets. */
  check_request("/");
  check_request("/index.html");
  check_request("/a/b/c?q=1");

  if (fails == 0) {
    printf("head-emitter self-test: ALL PASS\n");
    return 0;
  }
  fprintf(stderr, "head-emitter self-test: %d FAILURE(S)\n", fails);
  return 1;
}
