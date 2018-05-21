CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I.. -Iinclude -FI.\CommonInclude.h /DNO_OPENSSL

all: libquiccrypto.dll test

# 'dir /b *.c' then replace "^(.*)" by "  \1 \\"
SOURCES = \
  Crypto_AEAD_Main_Crypto_Indexing.c \
  Crypto_HKDF_Crypto_HMAC.c \
  Crypto_Symmetric_Bytes.c \
  Hacl_Curve25519.c \
  FStar_UInt128.c \
# Hacl_Test_X25519.c \
  kremstr.c \
  quic_provider.c \
  sha256_main_i.c \
# test.c \
  vale_aes_glue.c \
  Vale_Hash_SHA2_256.c

!if "$(PLATFORM)"=="x86"
PLATFORM_OBJS = aes-i686.obj
!else
PLATFORM_OBJS = aes-x86_64.obj aesgcm-x86_64.obj
!endif
  
libquiccrypto_code.lib: $(SOURCES:.c=.obj) $(PLATFORM_OBJS)
  lib /nologo /out:libquiccrypto_code.lib $**
  
libquiccrypto.dll: libquiccrypto_code.lib libquiccrypto.def dllmain.obj
  link /nologo /dll /debug:full /out:libquiccrypto.dll libquiccrypto_code.lib dllmain.obj /def:libquiccrypto.def /OPT:ICF /OPT:REF ntdll.lib

test.exe: test.obj libquiccrypto.dll
  link /nologo /ltcg /debug:full /out:test.exe test.obj libquiccrypto.lib

test: test.exe libquiccrypto.dll
  test.exe
  
.c.obj::
    cl $(CCOPTS) -c $<

{amd64\}.asm.obj:
    ml64 /nologo /c $< /Fo$@

{i386\}.asm.obj:
    ml /nologo /c $< /Fo$@

clean:
    -del *.lib
    -del *.obj
