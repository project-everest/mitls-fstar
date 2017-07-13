FSTAR_HOME ?= ../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
HACL_HOME ?= ../../../hacl-star


ifeq ($(OS),Windows_NT)
LIBMITLS=libmitls.dll
LIBQC=libquiccrypto.dll
else
LIBMITLS=libmitls.so
LIBQC=libquiccrypto.so
endif

all: quic.exe

clean:
	rm -rf *.o *.exe *.dll *~

../../src/tls/$(LIBMITLS):
	make -C ../../src/tls tls-ffi

$(HACL_HOME)/secure_api/QuicProvider/$(LIBQC):
	make -C $(HACL_HOME)/secure_api/QuicProvider

$(LIBMITLS): ../../src/tls/$(LIBMITLS)
	cp ../../src/tls/$(LIBMITLS) .

$(LIBQC): $(HACL_HOME)/secure_api/QuicProvider/$(LIBQC)
	cp $(HACL_HOME)/secure_api/QuicProvider/$(LIBQC) .

quic.exe: quic.c $(LIBMITLS) $(LIBQC)
	$(CC) -fPIC -I ../../libs/ffi -I $(HACL_HOME)/secure_api/QuicProvider -L. quic.c -lmitls -lquiccrypto -o quic.exe

