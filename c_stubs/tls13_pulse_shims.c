#define TLS13_PULSE_SHIMS_IMPLEMENTATION
#include "tls13_crypto_external.h"
#include "krmllib.h"

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

void Pulse_Lib_Array_memcpy_l(
    size_t len,
    uint8_t *src,
    uint8_t *dst,
    void *src_bytes,
    void *dst_bytes,
    void *squash) {
  Pulse_Lib_Array_memcpy(len, src, dst, src_bytes, dst_bytes, squash);
}
