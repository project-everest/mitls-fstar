// Implementation of various functions that are assume val and therefore
// declared via kremlin as extern

#include "kremlib.h"
#include "kremstr.h"
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

extern bool FStar_IO_debug_print_string(const char *msg) {
  printf("%s\n", msg);
  return true;
}

extern Prims_string Platform_Error_perror(Prims_string x0, Prims_int x1, Prims_string x2) {
  char *buf = malloc(512);
  snprintf(buf, 512, "perror: %s %d %s", x0, x1, x2);
  return buf;
}
