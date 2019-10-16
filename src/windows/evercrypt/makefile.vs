CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I../include /FICommonInclude.h

all: libevercrypt.dll libevercrypt.lib

#  ls hacl-star/providers/evercrypt/c/*.c hacl-star/providers/generated/*.c | xargs basename -a
#  remove evercrypt_openssl
#  add a couple missing ones... looks like make-source-drop is more
#  authoritative
SOURCES = \
  EverCrypt.c \
  EverCrypt_AEAD.c \
  EverCrypt_AutoConfig2.c \
  EverCrypt_BCrypt.c \
  EverCrypt_Chacha20Poly1305.c \
  EverCrypt_Cipher.c \
  EverCrypt_Curve25519.c \
  EverCrypt_Hash.c \
  EverCrypt_HKDF.c \
  EverCrypt_HMAC.c \
  EverCrypt_Poly1305.c \
  EverCrypt_StaticConfig.c \
  EverCrypt_Vale.c \
  evercrypt_vale_stubs.c \
  Hacl_Chacha20.c \
  Hacl_Chacha20_Vec32.c \
  Hacl_Chacha20_Vec128.c \
  Hacl_Chacha20_Vec256.c \
  Hacl_Chacha20Poly1305_32.c \
  Hacl_Chacha20Poly1305_128.c \
  Hacl_Chacha20Poly1305_256.c \
  Hacl_Curve25519_51.c \
  Hacl_Curve25519_64.c \
  Hacl_Ed25519.c \
  Hacl_Hash.c \
  Hacl_AES.c \
  Hacl_Kremlib.c \
  Hacl_SHA3.c \
  Hacl_Poly1305_32.c \
  Hacl_Poly1305_128.c \
  Hacl_Poly1305_256.c \
  evercrypt_vale_stubs.c

{amd64\}.asm.obj:
    ml64 /nologo /c $< /Fo$@

{i386\}.asm.obj:
    ml /nologo /c $< /Fo$@
  
!if "$(PLATFORM)"=="x86"
PLATFORM_OBJS = aes-i686.obj
!else if "$(PLATFORM)"=="X64" || "$(VSCMD_ARG_TGT_ARCH)"=="x64"
PLATFORM_OBJS = aes-x86_64-msvc.obj sha256-x86_64-msvc.obj \
  oldaesgcm-x86_64-msvc.obj aesgcm-x86_64-msvc.obj cpuid-x86_64-msvc.obj curve25519-x86_64-msvc.obj \
  poly1305-x86_64-msvc.obj
!else
PLATFORM_OBJS = 
!endif

libevercrypt_code.lib: $(SOURCES:.c=.obj) $(PLATFORM_OBJS)
  lib /nologo /out:libevercrypt_code.lib $**

# Note: libevercrypt.def generated via:
# nm libevercrypt.a -g | grep ' T ' | awk '{ print $3; }'
# Then: remove symbols that mention OpenSSL
libevercrypt.dll: libevercrypt_code.lib libevercrypt.def dllmain.obj ../kremlib/libkremlib.lib
  link /nologo /dll /debug:full /out:libevercrypt.dll ../kremlib/libkremlib.lib libevercrypt_code.lib dllmain.obj /def:libevercrypt.def /OPT:ICF /OPT:REF ntdll.lib bcrypt.lib

.c.obj::
    cl $(CCOPTS) -c $<

clean:
    -del *.lib
    -del *.obj
