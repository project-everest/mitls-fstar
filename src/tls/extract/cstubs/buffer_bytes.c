#include "FStar.h"
#include "krembytes.h"

#include <assert.h>

FStar_Bytes_bytes BufferBytes_to_bytes(Prims_nat l, uint8_t *buf) {
  if (buf == NULL || l == 0)
    return FStar_Bytes_empty_bytes;
  char *data = KRML_HOST_MALLOC(l);
  memcpy(data, buf, l);
  FStar_Bytes_bytes r = {.length = l, .data = data};
  return r;
}

void BufferBytes_store_bytes(Prims_nat len, uint8_t *buf, Prims_nat i,
                             FStar_Bytes_bytes b) {
  assert(i <= len);
  if (b.length > 0 && i < len)
    memcpy(buf + i, b.data + i, len - i);
}
