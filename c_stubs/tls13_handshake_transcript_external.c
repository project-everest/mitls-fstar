#include "tls13_handshake_transcript_external.h"

#include "tls13_hacl_stubs.h"

#include <string.h>

bool TLS13_Handshake_Transcript_External_sha256_three(
    uint8_t *a,
    size_t a_len,
    uint8_t *b,
    size_t b_len,
    uint8_t *c,
    size_t c_len,
    uint8_t *out,
    void *a_bytes,
    void *b_bytes,
    void *c_bytes,
    void *old_out) {
  (void)a_bytes;
  (void)b_bytes;
  (void)c_bytes;
  (void)old_out;
  uint8_t transcript[32768];
  if (a_len > sizeof transcript ||
      b_len > sizeof transcript - a_len ||
      c_len > sizeof transcript - a_len - b_len) {
    return false;
  }
  size_t pos = 0;
  if (a_len != 0) {
    memcpy(transcript + pos, a, a_len);
  }
  pos += a_len;
  if (b_len != 0) {
    memcpy(transcript + pos, b, b_len);
  }
  pos += b_len;
  if (c_len != 0) {
    memcpy(transcript + pos, c, c_len);
  }
  pos += c_len;
  return tls13_hacl_sha256(out, transcript, pos);
}
