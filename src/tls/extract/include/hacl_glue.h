// Use the new header mark that says "AEADOpenSSL has been fully defined".
#ifdef __Crypto_Indexing_H_DEFINED
// That way, we can insert ourselves right after AEADOpenSSL in the include
// sequence.
#ifndef __HACL_GLUE
#define __HACL_GLUE

#include "Crypto_AEAD_Main.h"

typedef Crypto_AEAD_Invariant_aead_state Crypto_AEAD_Main_aead_state;
typedef Crypto_AEAD_Invariant_aead_state Crypto_AEAD_Main_aead_state_______;

#endif
#endif
