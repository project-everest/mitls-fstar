#include "Mitls_Kremlib.h"

FStar_Bytes_bytes BufferBytes_to_bytes(Prims_nat l, uint8_t *buf) {
  if (buf == NULL || l == 0)
    return FStar_Bytes_empty_bytes;
  char *data = KRML_HOST_MALLOC(l);
  if (data == NULL)
    KRML_HOST_EXIT(255);
  memcpy(data, buf, l);
  FStar_Bytes_bytes r = {.length = l, .data = data};
  return r;
}

void BufferBytes_store_bytes(Prims_nat len, uint8_t *buf, Prims_nat i,
                             FStar_Bytes_bytes b) {
  if (i > len) {
      KRML_HOST_PRINTF("BufferBytes_store_bytes i must be <= len (i=%d len=%d)\n", i, len);
      KRML_HOST_EXIT(252);
  }
  if (b.length > 0 && i < len)
    memcpy(buf + i, b.data + i, len - i);
}

uint8_t *BufferBytes_from_bytes(FStar_Bytes_bytes b) {
  uint8_t *buf = KRML_HOST_MALLOC(b.length);
  if (buf == NULL)
    KRML_HOST_EXIT(255);
  BufferBytes_store_bytes(b.length, buf, 0, b);
  return buf;
}
