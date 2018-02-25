MARCH?=x86_64

CCOPTS = -std=c11 -D__USE_MINGW_ANSI_STDIO -I..

ifeq ($(OS),Windows_NT)
    EXTRA_OPTS = -DUNICODE=1
    EXTRA_LIBS = -L.
    CC = $(MARCH)-w64-mingw32-gcc
else
    #error This code is Windows-only (certificate store)
endif

.PHONY: test clean

all: libmipki.dll

mipkiwin.o: mipkiwin.c
	$(CC) $(CCOPTS) $(EXTRA_OPTS) -c mipkiwin.c


libmipki.dll: mipkiwin.o
	$(CC) $(COPTS) -shared mipkiwin.o -lcrypt32 -o $@

test.exe: libmipki.dll test.c
	$(CC) $(COPTS) -I.. -L. -lmipki test.c -o $@

test: test.exe
	@./test.exe

clean:
	$(MAKE) -C $(PLATFORM) clean
	rm -f *.[oa] *.exe *.dll *.lib *.annot *~

