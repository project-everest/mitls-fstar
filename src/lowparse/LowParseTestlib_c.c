#include "kremlib.h"

#include "Prims.h"
#include "FStar.h"

#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include "LowParseTestlib.h"

K___uint8_t__uint32_t LowParseTestlib_load_file_buffer(Prims_string x0)
{
    FILE *fp = fopen(x0, "rb");
    if (!fp) {
        KRML_HOST_EPRINTF("Failed to open input data file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    if (fseek(fp, 0L, SEEK_END) != 0) {
        KRML_HOST_EPRINTF("Failed to seek to end of file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    long filesize = ftell(fp);
    if (filesize < 0) {
        KRML_HOST_EPRINTF("Failed get length of file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    if (fseek(fp, 0L, SEEK_SET) != 0) {
        KRML_HOST_EPRINTF("Failed to seek to start of file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    char *buffer = (char*)KRML_HOST_MALLOC(filesize);
    if (!buffer) {
        KRML_HOST_EPRINTF("Out of memory reading file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    if (fread(buffer, sizeof(char), filesize, fp) == 0) {
        KRML_HOST_EPRINTF("Error reading file '%s'.  errno=%d\n", x0, errno);
        KRML_HOST_EXIT(1);
    }
    fclose(fp);

    K___uint8_t__uint32_t ret = {.fst = (uint8_t*)buffer, .snd = (uint32_t)filesize };
    return ret;
}

FStar_Bytes_bytes LowParseTestlib_load_file(Prims_string x0)
{
    K___uint8_t__uint32_t f = LowParseTestlib_load_file_buffer(x0);

    FStar_Bytes_bytes ret = {.length = f.snd, .data = (char*)f.fst};
    return ret;
}
