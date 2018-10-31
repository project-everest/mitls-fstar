CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I../include /FICommonInclude.h

all: libevercrypt.dll libevercrypt.lib

#  ls hacl-star/providers/evercrypt/c/*.c hacl-star/providers/generated/*.c | xargs basename -a
#  remove evercrypt_openssl
#  add a couple missing ones... looks like make-source-drop is more
#  authoritative
SOURCES = \
  AEAD_Poly1305_64.c \
  C_C.c \
  Crypto_Symmetric_AES.c \
  Crypto_Symmetric_AES128.c \
  EverCrypt.c \
  EverCrypt_AutoConfig.c \
  EverCrypt_BCrypt.c \
  EverCrypt_Bytes.c \
  EverCrypt_Hacl.c \
  EverCrypt_Hash.c \
  EverCrypt_Helpers.c \
  EverCrypt_HKDF.c \
  EverCrypt_HMAC.c \
  EverCrypt_StaticConfig.c \
  EverCrypt_Vale.c \
  evercrypt_vale_stubs.c \
  EverCrypt_ValeGlue.c \
  Flag.c \
  FStar.c \
  Hacl.c \
  Hacl_Chacha20.c \
  Hacl_Chacha20Poly1305.c \
  Hacl_Curve25519.c \
  Hacl_Ed25519.c \
  Hacl_HMAC_SHA2_256.c \
  Hacl_Policies.c \
  Hacl_Poly1305_64.c \
  Hacl_Salsa20.c \
  Hacl_SHA2_256.c \
  Hacl_SHA2_384.c \
  Hacl_SHA2_512.c \
  LowStar.c \
  Prims.c \
  vale_aes_glue.c \
  Vale_Hash_SHA2_256.c \
  sha256_main_i.c

{amd64\}.asm.obj:
    ml64 /nologo /c $< /Fo$@

{i386\}.asm.obj:
    ml /nologo /c $< /Fo$@
  
!if "$(PLATFORM)"=="x86"
PLATFORM_OBJS = aes-i686.obj
!else if "$(PLATFORM)"=="X64" || "$(VSCMD_ARG_TGT_ARCH)"=="x64"
PLATFORM_OBJS = aes-x86_64.obj sha256-x86_64.obj aesgcm-x86_64.obj
!else
PLATFORM_OBJS = 
!endif

libevercrypt_code.lib: $(SOURCES:.c=.obj) $(PLATFORM_OBJS)
  lib /nologo /out:libevercrypt_code.lib $**

# Note: libevercrypt.def generated via nm libevercrypt.a -g | grep ' T ' | awk '{ print $3; }'
# Then: remove symbols that mention OpenSSL
libevercrypt.dll: libevercrypt_code.lib libevercrypt.def dllmain.obj ../kremlib/libkremlib.lib
  link /nologo /dll /debug:full /out:libevercrypt.dll ../kremlib/libkremlib.lib libevercrypt_code.lib dllmain.obj /def:libevercrypt.def /OPT:ICF /OPT:REF ntdll.lib bcrypt.lib

.c.obj::
    cl $(CCOPTS) -c $<

clean:
    -del *.lib
    -del *.obj
