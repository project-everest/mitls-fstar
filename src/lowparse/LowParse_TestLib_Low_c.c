#include "kremlib.h"

#include "Prims.h"
#include "FStar.h"

#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include "LowParse.h"
#include "LowParse_TestLib_Aux.h"

K___uint8_t__int32_t LowParse_TestLib_Low_load_file_buffer(Prims_string x0)
{
    K___uint8_t__int32_t ret;
    LowParse_TestLib_Aux_load_file(x0, (uint8_t**)&ret.fst, &ret.snd);
    return ret;
}

bool LowParse_TestLib_Low_beqb (uint8_t * b1, uint8_t * b2, uint32_t len) {
  return memcmp(b1, b2, len) == 0;
}
