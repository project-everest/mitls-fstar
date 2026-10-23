#ifndef TLS13_CRYPTO_EXTERNAL_H
#define TLS13_CRYPTO_EXTERNAL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* The one cryptographic extern left in C: platform entropy, realizing
   src/impl/extern/TLS13.Crypto.Random.fsti.  Every other primitive is the
   verified Pulse code of TLS13.Crypto calling hacl-pulse directly. */
bool TLS13_Crypto_Random_random_bytes(uint8_t *out, size_t out_len);

#endif
