#ifndef __HACKS_H
#define __HACKS_H
#include "kremlib.h"

typedef uint32_t FStar_Char_char_, FStar_Char;

typedef void *FStar_Pointer_Base_loc;

typedef void *FStar_Tcp_networkStream, *FStar_Tcp_tcpListener;

// Why is there no prefix?
typedef const char *string;

static inline bool __log_to_choice(const char *str)
{
  KRML_HOST_PRINTF("%s", str);
  return 1;
}

#define Prims_uu___is_Cons(X) ((X)->tag == Prims_Cons)
#define FStar_IO_debug_print_string __log_to_choice

#endif // __HACKS_H
