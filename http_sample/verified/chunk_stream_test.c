/*
 * chunk_stream_test.c -- concrete C validation of the *verified* HTTP/1.1
 * multi-chunk streaming reassembly decoder extracted into HTTP_Verified.c.
 *
 * Builds a chunked transfer-encoding stream out of the verified emitters
 *   http_emit_chunk       (HTTP.Impl.Codec.Chunked) -- one "hhhh CRLF data CRLF"
 *   http_emit_empty_chunk (HTTP.Impl.Codec.Chunked) -- the "0000 CRLF CRLF"
 *                                                      last-chunk terminator
 * then decodes the whole stream in one shot with the verified reassembler
 *   http_decode_chunks    (HTTP.Impl.Codec.Chunked.Stream) -- walks the frames,
 *       concatenates their payloads into `out`, stops at the empty chunk, and
 *       (per its F-star proof) yields exactly parse_chunks(stream).
 *
 * The test asserts the reassembled body byte-for-byte equals the original
 * concatenation of the chunk payloads, across a spread of chunk counts / sizes,
 * and that malformed / truncated streams are rejected.
 */

#include "HTTP_Verified.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

static int fails = 0;

/* Append one chunk frame (8 + n bytes) for payload data[0..n) to buf at *pos. */
static void emit_one(uint8_t *buf, size_t *pos, const uint8_t *data, size_t n) {
  http_emit_chunk((uint8_t *)data, n, buf + *pos);
  *pos += 8 + n;
}

/* Build a stream from `k` payloads (sizes[i], contents = filler byte b+i),
 * decode it, and check the reassembled body matches the concatenation. */
static void run_case(const char *name, const size_t *sizes, size_t k) {
  size_t total_enc = 0, total_body = 0;
  for (size_t i = 0; i < k; i++) { total_enc += 8 + sizes[i]; total_body += sizes[i]; }
  total_enc += 8; /* terminator */

  uint8_t *stream = malloc(total_enc ? total_enc : 1);
  uint8_t *body   = malloc(total_body ? total_body : 1);
  uint8_t *out    = malloc(total_body ? total_body : 1);
  size_t spos = 0, bpos = 0;

  for (size_t i = 0; i < k; i++) {
    uint8_t *payload = malloc(sizes[i] ? sizes[i] : 1);
    for (size_t j = 0; j < sizes[i]; j++) payload[j] = (uint8_t)(0x30 + ((i + j) & 0x3f));
    memcpy(body + bpos, payload, sizes[i]);
    bpos += sizes[i];
    emit_one(stream, &spos, payload, sizes[i]);
    free(payload);
  }
  http_emit_empty_chunk(stream + spos);
  spos += 8;

  size_t off = 0xdead;
  bool ok = http_decode_chunks(stream, spos, out, total_body, &off);

  if (!ok) {
    fails++;
    fprintf(stderr, "  [%s] decode REJECTED a well-formed stream\n", name);
  } else if (off != total_body) {
    fails++;
    fprintf(stderr, "  [%s] reassembled length %zu != expected %zu\n", name, off, total_body);
  } else if (total_body && memcmp(out, body, total_body) != 0) {
    fails++;
    fprintf(stderr, "  [%s] reassembled body MISMATCH\n", name);
  } else {
    printf("  [%s] OK  (%zu chunks, %zu body bytes, %zu encoded)\n",
           name, k, total_body, spos);
  }

  free(stream); free(body); free(out);
}

/* A stream missing its terminator must be rejected (runs off the end). */
static void run_reject_no_terminator(void) {
  uint8_t data[4] = { 'a', 'b', 'c', 'd' };
  uint8_t stream[8 + 4];
  size_t spos = 0;
  emit_one(stream, &spos, data, 4);   /* one chunk, NO empty terminator */
  uint8_t out[4];
  size_t off = 0;
  bool ok = http_decode_chunks(stream, spos, out, sizeof out, &off);
  if (ok) { fails++; fprintf(stderr, "  [no-terminator] wrongly ACCEPTED\n"); }
  else    { printf("  [no-terminator] correctly rejected\n"); }
}

/* A corrupted size header (non-hex digit) must be rejected. */
static void run_reject_bad_header(void) {
  uint8_t data[4] = { 'a', 'b', 'c', 'd' };
  uint8_t stream[8 + 4 + 8];
  size_t spos = 0;
  emit_one(stream, &spos, data, 4);
  http_emit_empty_chunk(stream + spos);
  spos += 8;
  stream[1] = 'Z';                    /* clobber a hex digit of the size */
  uint8_t out[4];
  size_t off = 0;
  bool ok = http_decode_chunks(stream, spos, out, sizeof out, &off);
  if (ok) { fails++; fprintf(stderr, "  [bad-header] wrongly ACCEPTED\n"); }
  else    { printf("  [bad-header] correctly rejected\n"); }
}

int main(void) {
  printf("=== verified multi-chunk reassembly (http_decode_chunks) ===\n");

  size_t empty_stream[1] = { 0 };
  run_case("terminator-only", empty_stream, 0);

  size_t one[1]  = { 5 };
  run_case("single-chunk", one, 1);

  size_t few[3]  = { 1, 300, 7 };
  run_case("three-chunks", few, 3);

  size_t many[5] = { 65535, 1, 65535, 100, 4096 };
  run_case("max-and-mixed", many, 5);

  size_t small[8] = { 1, 2, 3, 4, 5, 6, 7, 8 };
  run_case("eight-small", small, 8);

  run_reject_no_terminator();
  run_reject_bad_header();

  if (fails == 0) { printf("ALL PASS\n"); return 0; }
  fprintf(stderr, "%d FAILURE(S)\n", fails);
  return 1;
}
