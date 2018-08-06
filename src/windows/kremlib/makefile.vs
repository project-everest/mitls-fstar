CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I../include /FI..\CommonInclude.h

all: libkremlib.dll libkremlib.lib

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
  testlib.c


libkremlib_code.lib: $(SOURCES:.c=.obj)
  lib /nologo /out:libkremlib_code.lib $**

# Note: libkremlib.def generated via nm libkremlib.a -g | grep ' T ' | awk '{ print $3; }'
# Then: remove FStar_UInt128_mul + TestLib_cpucycles*
libkremlib.dll: libkremlib_code.lib libkremlib.def dllmain.obj
  link /nologo /dll /debug:full /out:libkremlib.dll libkremlib_code.lib dllmain.obj /def:libkremlib.def /OPT:ICF /OPT:REF ntdll.lib

.c.obj::
    cl $(CCOPTS) -c $<

clean:
    -del *.lib
    -del *.obj
