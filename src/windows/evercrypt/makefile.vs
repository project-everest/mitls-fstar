CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I.. -I../mitls /FI..\CommonInclude.h

all: libevercrypt.dll libevercrypt.lib

#  ls hacl-star/providers/evercrypt/c/*.c hacl-star/providers/generated/*.c | xargs basename -a
#  remove evercrypt_openssl
SOURCES = \
  evercrypt_autoconfig.c \
  evercrypt_bcrypt.c \
  evercrypt_bytes.c \
#  evercrypt_openssl.c \
  evercrypt_vale_stubs.c \
  AEAD_Poly1305_64.c \
  C.c \
  C_Endianness.c \
  C_Failure.c \
  C_Loops.c \
  C_Nullity.c \
  C_String.c \
  EverCrypt.c \
  EverCrypt_AutoConfig.c \
  EverCrypt_BCrypt.c \
  EverCrypt_Bytes.c \
  EverCrypt_Hacl.c \
  EverCrypt_Helpers.c \
#  EverCrypt_OpenSSL.c \
  EverCrypt_Specs.c \
  EverCrypt_StaticConfig.c \
  EverCrypt_Vale.c \
  EverCrypt_ValeGlue.c \
  FStar.c \
  Hacl_Chacha20.c \
  Hacl_Chacha20Poly1305.c \
  Hacl_Curve25519.c \
  Hacl_Policies.c \
  Hacl_SHA2_256.c \
  Hacl_SHA2_384.c \
  Hacl_SHA2_512.c \
  LowStar.c \
  Prims.c \
  Vale_Hash_SHA2_256.c

libevercrypt_code.lib: $(SOURCES:.c=.obj)
  lib /nologo /out:libevercrypt_code.lib $**

# Note: libevercrypt.def generated via nm libevercrypt.a -g | grep ' T ' | awk '{ print $3; }'
libevercrypt.dll: libevercrypt_code.lib libevercrypt.def dllmain.obj
  link /nologo /dll /debug:full /out:libevercrypt.dll libevercrypt_code.lib dllmain.obj /def:libevercrypt.def /OPT:ICF /OPT:REF ntdll.lib

.c.obj::
    cl $(CCOPTS) -c $<

clean:
    -del *.lib
    -del *.obj
