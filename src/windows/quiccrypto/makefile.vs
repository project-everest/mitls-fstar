CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I../include -FICommonInclude.h /DNO_OPENSSL

all: libquiccrypto.dll test

# 'dir /b *.c' then replace "^(.*)" by "  \1 \\"
SOURCES = \
  quic_provider.c

PLATFORM_OBJS = 
  
libquiccrypto_code.lib: $(SOURCES:.c=.obj) $(PLATFORM_OBJS)
  lib /nologo /out:libquiccrypto_code.lib $**
  
libquiccrypto.dll: libquiccrypto_code.lib libquiccrypto.def dllmain.obj ../kremlib/libkremlib.lib ../evercrypt/libevercrypt.lib
  link /nologo /dll /debug:full /out:libquiccrypto.dll libquiccrypto_code.lib dllmain.obj /def:libquiccrypto.def /OPT:ICF /OPT:REF ntdll.lib ../kremlib/libkremlib.lib ../evercrypt/libevercrypt.lib

test.exe: test.obj libquiccrypto.dll
  link /nologo /debug:full /out:test.exe test.obj libquiccrypto.lib ../kremlib/libkremlib.lib ../evercrypt/libevercrypt.lib

test: test.exe libquiccrypto.dll
  set PATH=..\kremlib;..\evercrypt;%PATH% & .\test.exe
  
.c.obj::
    cl $(CCOPTS) -c $<

clean:
    -del *.lib
    -del *.obj
