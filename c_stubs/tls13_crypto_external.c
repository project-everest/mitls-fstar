#include "tls13_crypto_external.h"

#include "Hacl_Random.h"

static uint8_t empty_output;

bool TLS13_Crypto_Random_random_bytes(uint8_t *out, size_t out_len) {
  if (out_len != 0 && out == NULL) {
    return false;
  }
  return Hacl_Random_bytes(out_len == 0 ? &empty_output : out, out_len);
}
