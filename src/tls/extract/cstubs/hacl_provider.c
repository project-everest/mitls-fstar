#include "kremlib.h"
#include "Curve25519.h"

FStar_Bytes_bytes HaclProvider_crypto_scalarmult(FStar_Bytes_bytes secret, FStar_Bytes_bytes base) {
  FStar_Bytes_bytes out = {
    .length = 32,
    .data = calloc(32, 1)
  };
  Curve25519_crypto_scalarmult((char *) out.data, (char *) secret.data,  (char *) base.data);
  return out;
}
