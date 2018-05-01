#ifndef __HACKS_H
#define __HACKS_H
#include "kremlib.h"

typedef void *CoreCrypto_hash_ctx, *CoreCrypto_cipher_stream,
  *Platform_Date_dateTime, *Platform_Date_timeSpan;

typedef uint32_t FStar_Char_char_, FStar_Char;

typedef void *Hashing_OpenSSL_hash_ctx_______;

typedef void *FStar_Pointer_Base_loc;

typedef void *FStar_Tcp_networkStream, *FStar_Tcp_tcpListener;

// Why is there no prefix?
typedef const char *string;

#define Prims_uu___is_Cons(X) ((X)->tag == Prims_Cons)

#endif // __HACKS_H
