/*
 * pulse_array_shim.c — trusted C realization of the Pulse.Lib.Array primitives
 * that the verified YMODEM loops depend on but that the F-star/Pulse toolchain does
 * not ship a C definition for.
 *
 * `Pulse_Lib_Array_memcpy_l(n, src, dst, _, _, _)` is the C realization of the
 * Pulse library's verified `memcpy_l`: it copies `n` bytes from `src` into
 * `dst`.  The three trailing arguments are erased ghost witnesses (passed as
 * NULL by the extracted code).  The verified client loop was checked against
 * this primitive's separation-logic spec (copy `n` bytes); this file supplies
 * its trusted lowering, exactly as the Common.TCP C stub supplies the trusted
 * lowering of the verified read/write interface.
 */

#include <stddef.h>
#include <stdint.h>
#include <string.h>

void Pulse_Lib_Array_memcpy_l(size_t n, uint8_t *src, uint8_t *dst,
                              void *g0, void *g1, void *g2) {
  (void)g0; (void)g1; (void)g2;
  if (n != 0U) {
    memcpy(dst, src, n);
  }
}
