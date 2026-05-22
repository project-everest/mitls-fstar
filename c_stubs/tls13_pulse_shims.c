#include "tls13_crypto_external.h"

#include <string.h>

void Pulse_Lib_Array_memcpy(
    size_t len,
    uint8_t *src,
    uint8_t *dst,
    void *src_bytes,
    void *dst_bytes,
    void *squash) {
  (void)src_bytes;
  (void)dst_bytes;
  (void)squash;
  if (len != 0) {
    memcpy(dst, src, len);
  }
}
