// We need these two fully defined
#ifdef __Crypto_Indexing_H_DEFINED

#ifndef __HACL_GLUE
#define __HACL_GLUE

#include "Crypto_AEAD_Main.h"

typedef Crypto_AEAD_Invariant_aead_state Crypto_AEAD_Main_aead_state;
typedef Crypto_AEAD_Invariant_aead_state Crypto_AEAD_Main_aead_state_______;

typedef struct {
  Crypto_AEAD_Invariant_aead_state *st;
  Crypto_Indexing_id id;
} LowCProvider_aead_state;

#endif
#endif
