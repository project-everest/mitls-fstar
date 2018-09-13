CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I../include -Iinclude -FICommonInclude.h /DNO_OPENSSL

all: libmitls.dll

# 'dir /b *.c' then replace "^(.*)" by "  \1 \\"
SOURCES = \
  AEADProvider.c \
  Alert.c \
  buffer_bytes.c \
  BufferBytes.c \
  C.c \
  Cert.c \
  CommonDH.c \
  Connection.c \
  Content.c \
  Crypto_Plain.c \
  Extensions.c \
  FFI.c \
  FFICallbacks.c \
  Flags.c \
  Format.c \
  FStar.c \
  HandshakeLog.c \
  HandshakeMessages.c \
  Hashing.c \
  kremlinit.c \
  LowParse.c \
  LowParseWrappers.c \
  LowStar.c \
  Mem.c \
  mitlsffi.c \
  Negotiation.c \
  Nonce.c \
  Old_Handshake.c \
  Parse.c \
  PMS.c \
  Prims.c \
  PSK.c \
  QUIC.c \
  Random.c \
  Range.c \
  Record.c \
  StatefulLHAE.c \
  StreamAE.c \
  Ticket.c \
  TLS.c \
  TLSConstants.c \
  TLSError.c \
  TLSInfo.c

libmitls_code.lib: $(SOURCES:.c=.obj) $(PLATFORM_OBJS)
  lib /nologo /out:libmitls_code.lib $**
  
libmitls.dll: libmitls_code.lib libmitls.def dllmain.obj ../kremlib/libkremlib.lib ../evercrypt/libevercrypt.lib
  link /nologo /dll /debug:full /out:libmitls.dll libmitls_code.lib dllmain.obj /def:libmitls.def ntdll.lib advapi32.lib bcrypt.lib ../kremlib/libkremlib.lib ../evercrypt/libevercrypt.lib /OPT:ICF /OPT:REF

.c.obj::
    cl $(CCOPTS) -c $<

clean:
    -del *.lib
    -del *.obj
