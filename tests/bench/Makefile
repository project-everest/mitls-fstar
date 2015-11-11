#! -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean jsse-server jsse-client

arch      = $(shell uname)
buildtype =

ifneq ($(findstring CYGWIN,$(arch)),)
buildtype = cygwin
else
buildtype = unix
endif

ifeq ($(buildtype), unix)
ifeq ($(TARGET), mingw)
EXE   = .exe
CROSS = x86_64-w64-mingw32-
else
EXE   =
CROSS =
endif

PKGC   = $(CROSS)pkg-config
LOG4C  = $(CROSS)log4c-config

CC      := $(CROSS)gcc
CFLAGS  := -I ../c-stub -Wall -W -Wno-unused-function
CFLAGS  += $(shell $(PKGC) --cflags libevent) 
CFLAGS  += $(shell $(PKGC) --cflags libssl) 
CFLAGS  += $(shell $(LOG4C) --cflags)
LDFLAGS :=
LIBS    := -lpthread \
  $(shell $(PKGC) --libs libevent) \
  $(shell $(PKGC) --libs libssl) \
  $(shell $(LOG4C) --libs)

ifeq ($(TARGET), mingw)
LIBS += -lws2_32 -lexpat
endif

ESRC := echo-memory.c echo-ssl.c echo-log.c
ESRC := $(patsubst %,../c-stub/%,$(ESRC))
endif

JAVACP := $(wildcard 3rdparty/*.jar)
JAVACP := $(patsubst 3rdparty/%.jar,-cp 3rdparty/%.jar,$(JAVACP))

# --------------------------------------------------------------------
all:: jsse-server jsse-client

ifeq ($(buildtype), unix)
all:: openssl-server$(EXE) openssl-client$(EXE)

openssl-server$(EXE): openssl-server.c $(ESRC)
	$(CC) -o $@ $(CFLAGS) $(LDFLAGS) $^ $(LIBS)

openssl-client$(EXE): openssl-client.c $(ESRC)
	$(CC) -o $@ $(CFLAGS) $(LDFLAGS) $^ $(LIBS)
endif

jsse-server:
	rm -rf jsse-server && mkdir jsse-server
	javac $(JAVACP) -d jsse-server JSSEServer.java

jsse-client:
	rm -rf jsse-client && mkdir jsse-client
	javac $(JAVACP) -d jsse-client JSSEClient.java

clean:
	rm -rf jsse jsse-server jsse-client
	rm -rf openssl openssl-server openssl-client
