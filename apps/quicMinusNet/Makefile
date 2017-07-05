FSTAR_HOME ?= ../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: quic.exe

clean:
	rm -rf *.o *.exe *.dll *~

../../src/tls/libmitls.dll:
	make -C ../../src/tls tls-ffi

libmitls.dll: ../../src/tls/libmitls.dll
	cp ../../src/tls/libmitls.dll .

quic.exe: quic.c libmitls.dll
	gcc -fPIC -I ../../libs/ffi -L. -lmitls quic.c -o quic.exe
