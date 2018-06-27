CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I.. -Iinclude -Ikremlin -FI.\CommonInclude.h /DNO_OPENSSL

all: libquiccrypto.dll test

# 'dir /b *.c' then replace "^(.*)" by "  \1 \\"
SOURCES = \
  Crypto_AEAD_Main_Crypto_Symmetric_Cipher_Crypto_Indexing.c \
  Crypto_HKDF_Crypto_HMAC.c \
  Crypto_Symmetric_Bytes.c \
  Hacl_Curve25519.c \
# Hacl_Test_X25519.c \
  quic_provider.c \
  sha256_main_i.c \
# test.c \
  vale_aes_glue.c \
  Vale_Hash_SHA2_256.c

!if "$(PLATFORM)"=="x86"
PLATFORM_OBJS = aes-i686.obj
!else if "$(PLATFORM)"=="X64" || "$(VSCMD_ARG_TGT_ARCH)"=="x64"
PLATFORM_OBJS = aes-x86_64.obj sha256-x86_64.obj aesgcm-x86_64.obj
!else
PLATFORM_OBJS = 
!endif
  
libquiccrypto_code.lib: $(SOURCES:.c=.obj) $(PLATFORM_OBJS)
  lib /nologo /out:libquiccrypto_code.lib $**
  
libquiccrypto.dll: libquiccrypto_code.lib libquiccrypto.def dllmain.obj ../kremlib/libkremlib.lib
  link /nologo /dll /debug:full /out:libquiccrypto.dll libquiccrypto_code.lib dllmain.obj /def:libquiccrypto.def /OPT:ICF /OPT:REF ntdll.lib ../kremlib/libkremlib.lib

test.exe: test.obj libquiccrypto.dll
  link /nologo /ltcg /debug:full /out:test.exe test.obj libquiccrypto.lib ../kremlib/libkremlib.lib

test: test.exe libquiccrypto.dll
  set PATH=..\kremlib;%PATH% ; .\test.exe
  
.c.obj::
    cl $(CCOPTS) -c $<

{amd64\}.asm.obj:
    ml64 /nologo /c $< /Fo$@

{i386\}.asm.obj:
    ml /nologo /c $< /Fo$@

clean:
    -del *.lib
    -del *.obj
