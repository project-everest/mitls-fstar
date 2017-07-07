FSTAR_HOME ?= ../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include





ifeq ($(OS),Windows_NT)
LIBMITLS=libmitls.dll
else
LIBMITLS=libmitls.so
endif


all: quic.exe

clean:
	rm -rf *.o *.exe *.dll *~

../../src/tls/libmitls.dll:
	make -C ../../src/tls tls-ffi

libmitls.dll: ../../src/tls/libmitls.dll
	cp ../../src/tls/libmitls.dll .

libmitls.so: ../../src/tls/libmitls.so
	cp ../../src/tls/libmitls.so .

quic.exe: quic.c $(LIBMITLS)
	gcc -fPIC -I ../../libs/ffi -L. quic.c -lmitls -o quic.exe
