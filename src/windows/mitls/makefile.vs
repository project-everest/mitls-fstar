CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I../include -Iinclude -FICommonInclude.h /DNO_OPENSSL

all: libmitls.dll

# 'dir /b *.c' then replace "^(.*)" by "  \1 \\"
SOURCES = \
  AEADProvider.c \
  Alert.c \
  buffer_bytes.c \
  Cert.c \
  CipherSuite.c \
  CommonDH.c \
  Connection.c \
  Content.c \
  Crypto_AE.c \
  Crypto_AEAD.c \
  Crypto_CRF.c \
  EverCrypt.c \
  Extensions.c \
  FFI.c \
  Format.c \
  Handshake.c \
  HandshakeLog.c \
  HandshakeMessages.c \
  Hashing.c \
  HSL_Receive.c \
  HSL_Transcript.c \
  IdNonce.c \
  Idx.c \
  IV.c \
  KDF.c \
  KDF_Rekey.c \
  KDF_Salt_ODH.c \
  krmlinit.c \
  LowParse.c \
  Mem.c \
  mipki_wrapper.c \
  MITLS_Init.c \
  MiTls_Krmllib.c \
  MITLS_Repr.c \
  mitlsffi.c \
  Negotiation.c \
  Negotiation_Version.c \
  Nonce.c \
  Parse.c \
  Parsers.c \
  PMS.c \
  PSK.c \
  QUIC.c \
  Random.c \
  Range.c \
  Record.c \
  Spec.c \
  StatefulLHAE.c \
  StreamAE.c \
  TC.c \
  Ticket.c \
  TLS.c \
  TLS_Callbacks.c \
  TLS_Cookie.c \
  TLSConstants.c \
  TLSError.c \
  TLSInfo.c \
  Unused.c

libmitls_code.lib: $(SOURCES:.c=.obj) $(PLATFORM_OBJS)
  lib /nologo /out:libmitls_code.lib $**

libmitls.dll: libmitls_code.lib libmitls.def dllmain.obj ../krmllib/libkrmllib.lib ../evercrypt/libevercrypt.lib
  link /nologo /dll /debug:full /out:libmitls.dll libmitls_code.lib dllmain.obj /def:libmitls.def ntdll.lib advapi32.lib bcrypt.lib ../krmllib/libkrmllib.lib ../evercrypt/libevercrypt.lib /OPT:ICF /OPT:REF

.c.obj::
    cl $(CCOPTS) -c $<

clean:
    -del *.lib
    -del *.obj
