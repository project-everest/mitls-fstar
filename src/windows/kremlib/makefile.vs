CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I../include /FICommonInclude.h

all: libkremlib.lib

# ls kremlin/kremlib/*.c | xargs basename -a
# remove fstar_uint128.c
SOURCES = \
  RegionAllocator.c \
  c.c \
  c_string.c \
  fstar_bytes.c \
  fstar_char.c \
  fstar_date.c \
  fstar_dyn.c \
  fstar_hyperstack_io.c \
  fstar_int16.c \
  fstar_int32.c \
  fstar_int64.c \
  fstar_int8.c \
  fstar_io.c \
  fstar_string.c \
#  fstar_uint128.c \
  fstar_uint128_msvc.c \
  fstar_uint16.c \
  fstar_uint32.c \
  fstar_uint64.c \
  fstar_uint8.c \
  prims.c \
  testlib.c \
  FStar_UInt_8_16_32_64.c


libkremlib.lib: $(SOURCES:.c=.obj)
  lib /nologo /out:libkremlib.lib $**

.c.obj::
    cl $(CCOPTS) -c $<

clean:
    -del *.lib
    -del *.obj
