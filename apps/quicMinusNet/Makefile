FSTAR_HOME ?= ../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
HACL_HOME ?= ../../../hacl-star
MARCH?=x86_64

ifeq ($(OS),Windows_NT)
LIBMITLS=libmitls.dll
LIBQC=libquiccrypto.dll
LIBPKI=libmipki.dll
CC=$(MARCH)-w64-mingw32-gcc
else
LIBMITLS=libmitls.so
LIBQC=libquiccrypto.so
LIBPKI=libmipki.so
endif

all: quic.exe

clean:
	rm -rf *.o *.exe *.dll *~

../../src/pki/$(LIBPKI):
	make -C ../../src/pki

../../src/tls/extract/Kremlin-Library/$(LIBMITLS):
	make -j8 -C ../../src/tls -f Makefile.Kremlin build-library

$(HACL_HOME)/secure_api/QuicProvider/$(LIBQC):
	make -C $(HACL_HOME)/secure_api/QuicProvider

$(LIBMITLS): ../../src/tls/extract/Kremlin-Library/$(LIBMITLS)
	cp ../../../MLCrypto/openssl/libcrypto-*.dll .
	cp ../../src/tls/extract/Kremlin-Library/$(LIBMITLS) .

$(LIBQC): $(HACL_HOME)/secure_api/QuicProvider/$(LIBQC)
	cp $(HACL_HOME)/secure_api/QuicProvider/$(LIBQC) .

$(LIBPKI): ../../src/pki/$(LIBPKI)
	cp ../../src/pki/$(LIBPKI) .

quic.exe: quic.c $(LIBMITLS) $(LIBQC) $(LIBPKI)
	$(CC) -fPIC -I ../../src/pki -I ../../libs/ffi -I $(HACL_HOME)/secure_api/QuicProvider -L. quic.c -lmitls -lquiccrypto -lmipki -o quic.exe

