// We can only include these files when we're in AEADProvider, or later.
#ifdef __AEADProvider_H
// But only at the last minute!
#ifdef __AEADOpenssl_H
#ifndef __HACL_GLUE
#define __HACL_GLUE

#include "Crypto_Indexing.h"
#include "Crypto_AEAD_Main.h"

typedef Crypto_AEAD_Invariant_aead_state_______ Crypto_AEAD_Main_aead_state_______;

#endif
#endif
#endif
