#ifndef TLS13_LIB_MEMMOVE_H
#define TLS13_LIB_MEMMOVE_H

#include <stddef.h>
#include <stdint.h>

void TLS13_Lib_Memmove_memmove(
    uint8_t *buffer,
    size_t dst_offset,
    size_t src_offset,
    size_t len);

#endif
