#include "kremlib.h"
#include "Crypto_HKDF_Crypto_HMAC.h"
#include "Hacl_Curve25519.h"
#include "HaclProvider.h"

// FIXME KRML_HOST_CALLOC() == NULL

FStar_Bytes_bytes HaclProvider_crypto_scalarmult(FStar_Bytes_bytes secret, FStar_Bytes_bytes base) {
  FStar_Bytes_bytes out = {
    .length = 32,
    .data = KRML_HOST_CALLOC(32, 1)
  };
  Hacl_Curve25519_crypto_scalarmult((uint8_t *) out.data, (uint8_t *) secret.data,  (uint8_t *) base.data);
  return out;
}

static inline Crypto_HMAC_alg hash_alg(HaclProvider_hash_alg i) {
  switch (i) {
    case HaclProvider_HACL_SHA256:
      return Crypto_HMAC_SHA256;
    case HaclProvider_HACL_SHA384:
      return Crypto_HMAC_SHA384;
    case HaclProvider_HACL_SHA512:
      return Crypto_HMAC_SHA512;
  }
  return Crypto_HMAC_SHA256;
}

static inline size_t hash_size(Crypto_HMAC_alg h) {
  switch (h) {
    case Crypto_HMAC_SHA256:
      return 32;
    case Crypto_HMAC_SHA384:
      return 48;
    case Crypto_HMAC_SHA512:
      return 64;
  }
  return 32;
}

FStar_Bytes_bytes HaclProvider_crypto_hash(HaclProvider_hash_alg alg, FStar_Bytes_bytes msg) {
  Crypto_HMAC_alg h = hash_alg(alg);
  size_t len = hash_size(h);

  FStar_Bytes_bytes out = {
    .length = len,
    .data = KRML_HOST_CALLOC(len, 1)
  };
  
  Crypto_HMAC_agile_hash(h, (uint8_t *) out.data, (uint8_t *)msg.data, msg.length);
  return out;
}

FStar_Bytes_bytes HaclProvider_crypto_hmac(HaclProvider_hash_alg alg,
  FStar_Bytes_bytes key, FStar_Bytes_bytes msg) {
  Crypto_HMAC_alg h = hash_alg(alg);
  size_t len = hash_size(h);

  FStar_Bytes_bytes out = {
    .length = len,
    .data = KRML_HOST_CALLOC(len, 1)
  };

  Crypto_HMAC_hmac(h, (uint8_t *) out.data, (uint8_t *)key.data, key.length, (uint8_t *)msg.data, msg.length);
  return out;
}
