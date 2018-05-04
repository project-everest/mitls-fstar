CCOPTS = /nologo /O2 /Gy /GF /Gw /GA /MD /Zi -I. -I.. -Iinclude -FI..\CommonInclude.h /DNO_OPENSSL

all: libmitls.dll

# 'dir /b *.c' then replace "^(.*)" by "  \1 \\"
# then comment out Crypto_AEAD_Main.c
SOURCES = \
  AEADOpenssl.c \
  AEADProvider.c \
  AEAD_GCM.c \
  Alert.c \
  buffer_bytes.c \
  Buffer_Utils.c \
  BufferBytes.c \
  Cert.c \
  CommonDH.c \
  Connection.c \
  Content.c \
  CoreCrypto.c \
  core_crypto.c \
  CryptoTypes.c \
#  Crypto_AEAD_Main.c \
  Crypto_Plain.c \
  Crypto_HKDF_Crypto_HMAC.c \
  Crypto_Indexing.c \
  Crypto_Symmetric_Bytes.c \
  Curve25519.c \
  C_Loops_Spec_Loops.c \
  DataStream.c \
  DHGroup.c \
  ECGroup.c \
  Epochs.c \
  Extensions.c \
  FFI.c \
  FFICallbacks.c \
  Flag.c \
  Flags.c \
  Format.c \
  FStar.c \
  HaclProvider.c \
  hacl_aead.c \
  hacl_provider.c \
  Handshake.c \
  HandshakeLog.c \
  HandshakeMessages.c \
  Hashing.c \
  Hashing_CRF.c \
  Hashing_Flags.c \
  Hashing_OpenSSL.c \
  Hashing_Spec.c \
  HKDF.c \
  HMAC.c \
  HMAC_UFCMA.c \
  KeySchedule.c \
  kremdate.c \
  kremlinit.c \
  kremstr.c \
  LHAEPlain.c \
  LowCProvider.c \
  LowParse.c \
  LowParseWrappers.c \
  mitlsffi.c \
  Negotiation.c \
  Nonce.c \
  Parse.c \
  PMS.c \
  Prims.c \
  PSK.c \
  QUIC.c \
  regionallocator.c \
  Range.c \
  Record.c \
  RSAKey.c \
  sha256_main_i.c \
  Specializations_Providers_AEAD.c \
  StAE.c \
  StatefulLHAE.c \
  StatefulPlain.c \
  StreamAE.c \
  StreamDeltas.c \
  StreamPlain.c \
  Ticket.c \
  TLS.c \
  TLSConstants.c \
  TLSError.c \
  TLSInfo.c \
  TLSInfoFlags.c \
  TLSPRF.c \
  TLS_Curve25519.c \
  Transport.c \
  uint128_wrapper.c \
  vale_aes_glue.c \
  Vale_Hash_SHA2_256.c
  
aes-x86_64.obj: amd64\aes-x86_64.asm
  ml64 /nologo /Zi /c amd64\aes-x86_64.asm
  
aes-i686.obj: i386\aes-i686.asm
  ml /nologo /Zi /c i386\aes-i686.asm
  
!if "$(PLATFORM)"=="x86"
PLATFORM_OBJS = aes-i686.obj
!else
PLATFORM_OBJS = aes-x86_64.obj
!endif

libmitls_code.lib: $(SOURCES:.c=.obj) $(PLATFORM_OBJS)
  lib /nologo /out:libmitls_code.lib $**
  
libmitls.dll: libmitls_code.lib libmitls.def dllmain.obj
  link /nologo /dll /debug:full /out:libmitls.dll libmitls_code.lib dllmain.obj /def:libmitls.def ntdll.lib advapi32.lib bcrypt.lib /OPT:ICF /OPT:REF

.c.obj::
    cl $(CCOPTS) -c $<

clean:
    -del *.lib
    -del *.obj
