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
  Hacl_Curve25519.c \
  C_Loops_Spec_Loops.c \
  DataStream.c \
  DHGroup.c \
  ECGroup.c \
  Old_Epochs.c \
  Extensions.c \
  FFI.c \
  FFICallbacks.c \
  Flag.c \
  Flags.c \
  Format.c \
  FStar.c \
  FStar_UInt128.c \
  HaclProvider.c \
  hacl_aead.c \
  hacl_provider.c \
  Old_Handshake.c \
  HandshakeLog.c \
  HandshakeMessages.c \
  Hashing.c \
  Hashing_CRF.c \
  Hashing_OpenSSL.c \
  Hashing_Spec.c \
  Old_HKDF.c \
  HMAC.c \
  Old_HMAC_UFCMA.c \
  Old_KeySchedule.c \
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
  vale_aes_glue.c \
  Vale_Hash_SHA2_256.c \
# Taken from the list of HACL sources in hacl-star/providers/Makefiles
  Hacl_Chacha20.c \
  Hacl_Salsa20.c \
  Hacl_SHA2_256.c \
  Hacl_SHA2_384.c \
  Hacl_SHA2_512.c \
  Hacl_Curve25519.c \
  Hacl_Ed25519.c \
  Hacl_Poly1305_64.c \
  Hacl_HMAC_SHA2_256.c \
  AEAD_Poly1305_64.c \
  Hacl_Chacha20_Vec128.c \
# Taken from ls hacl-star/providers/multiplexer/c/*.c | xargs basename
  evercrypt_bytes.c \
  evercrypt_native.c \
  evercrypt_openssl.c \
  evercrypt_vale.c \
# Taken from ls hacl-star/providers/generated/EverCrypt_*.c | xargs basename
  EverCrypt_Bytes.c \
  EverCrypt_Hacl.c \
  EverCrypt_Helpers.c \
  EverCrypt_Native.c \
  EverCrypt_OpenSSL.c \
  EverCrypt_Specs.c \
  EverCrypt_Vale.c \
# Remember to add these
  EverCrypt.c \
  C_Failure.c

  
aes-x86_64.obj: amd64\aes-x86_64.asm
  ml64 /nologo /Zi /c amd64\aes-x86_64.asm
  
aes-i686.obj: i386\aes-i686.asm
  ml /nologo /Zi /c i386\aes-i686.asm

# JP: didn't manage to make a pattern rule work here
sha256-x86_64.obj: amd64\sha256-x86_64.asm
  ml64 /nologo /Zi /c amd64\sha256-x86_64.asm
  
sha256-i686.obj: i386\sha256-i686.asm
  ml /nologo /Zi /c i386\sha256-i686.asm
  
!if "$(PLATFORM)"=="x86"
PLATFORM_OBJS = aes-i686.obj sha256-i686.obj
!else
PLATFORM_OBJS = aes-x86_64.obj sha256-x86_64.obj
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
