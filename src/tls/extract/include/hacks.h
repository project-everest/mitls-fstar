#ifndef __HACKS_H
#define __HACKS_H
#include "kremlib.h"

typedef void *FStar_Char_char_, *CoreCrypto_hash_ctx, *CoreCrypto_cipher_stream,
  *Platform_Date_dateTime, *Platform_Date_timeSpan;

typedef int FStar_Char;

/* #define FStar_Seq_Base_length(x) 0 */
/* #define FStar_Seq_Base_init(x, y) 0 */
/* #define FStar_Seq_Properties_split(x, y) ((K___FStar_Seq_Base_seq_FStar_Char_char__FStar_Seq_Base_seq_FStar_Char_char_){ .fst = 0, .snd = 0 }) */

/* FStar_UInt16_t FStar_UInt16_uint_to_t(Prims_nat x); */
/* FStar_UInt32_t FStar_UInt32_uint_to_t(Prims_nat x); */
FStar_Char FStar_Char_char_of_int(krml_checked_int_t);

#define FStar_HyperStack_ST_new_colored_region(X, Y) 0
#define MonotoneMapNonDep_alloc__Nonce_random_Nonce_ex_rid_Nonce_injective___(X, Y) \
  ((void*)0)
#define MonotoneMapNonDep_alloc__FStar_Bytes_bytes______(X, Y) ((void*)0)
#define FStar_Monotonic_DependentMap_alloc__FStar_Bytes_bytes______(X) 0
#define FStar_Monotonic_DependentMap_alloc__FStar_Bytes_bytes_FStar_Bytes_bytes___PSK_pskInfo___bool___(X) ((void*)0)

typedef void *Hashing_OpenSSL_hash_ctx_______;

#endif // __HACKS_H
