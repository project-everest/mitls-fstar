// Implementation of various functions that are assume val and therefore
// declared via kremlin as extern

#include "kremlib.h"
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

extern bool FStar_IO_debug_print_string(Prims_string msg) {
  printf("%s\n", msg);
  return true;
}
