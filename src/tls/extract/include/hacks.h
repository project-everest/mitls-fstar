#ifndef __HACKS_H
#define __HACKS_H
#include "kremlib.h"

typedef void *CoreCrypto_hash_ctx, *CoreCrypto_cipher_stream,
  *Platform_Date_dateTime, *Platform_Date_timeSpan;

typedef uint32_t FStar_Char_char_, FStar_Char;

/* #define FStar_Seq_Base_length(x) 0 */
/* #define FStar_Seq_Base_init(x, y) 0 */
/* #define FStar_Seq_Properties_split(x, y) ((K___FStar_Seq_Base_seq_FStar_Char_char__FStar_Seq_Base_seq_FStar_Char_char_){ .fst = 0, .snd = 0 }) */

/* FStar_UInt16_t FStar_UInt16_uint_to_t(Prims_nat x); */
/* FStar_UInt32_t FStar_UInt32_uint_to_t(Prims_nat x); */

#define FStar_HyperStack_ST_new_colored_region(X, Y) 0

typedef void *Hashing_OpenSSL_hash_ctx_______;

typedef void *FStar_Pointer_Base_loc;

typedef void *FStar_Tcp_networkStream, *FStar_Tcp_tcpListener;

// Why is there no prefix?
typedef const char *string;

#define Prims_uu___is_Cons(X) ((X)->tag == Prims_Cons)

#endif // __HACKS_H
