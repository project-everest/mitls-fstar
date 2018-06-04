#include "kremlib.h"

#include "Prims.h"
#include "FStar.h"

#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include "LowParse.h"
#include "LowParse_TestLib_Aux.h"

FStar_Bytes_bytes LowParse_TestLib_SLow_load_file(Prims_string x0)
{
    FStar_Bytes_bytes ret;
    int32_t len;
    LowParse_TestLib_Aux_load_file(x0, (uint8_t**)&ret.data, &len);
    ret.length = (uint32_t) len;
    return ret;
}
