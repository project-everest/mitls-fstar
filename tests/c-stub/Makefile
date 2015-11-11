# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean

# --------------------------------------------------------------------
TARGET ?= unix					# allowed: <empty>, mingw

# --------------------------------------------------------------------
ifeq ($(TARGET), mingw)
EXE   = .exe
CROSS = i686-pc-mingw32-
else
EXE   =
CROSS =
endif

CC     = $(CROSS)gcc
LD     = $(CROSS)ld
AR     = $(CROSS)ar
PKGC   = $(CROSS)pkg-config
LOG4C  = $(CROSS)log4c-config

CFLAGS  += -O2 -ggdb -Wall -W -Wno-unused-function \
             $(shell $(PKGC)  --cflags libevent) \
             $(shell $(PKGC)  --cflags libevent_openssl) \
             $(shell $(PKGC)  --cflags libssl) \
             $(shell $(LOG4C) --cflags)
LDFLAGS +=
LIBS    += -lpthread \
	$(shell $(PKGC)  --libs libevent) \
	$(shell $(PKGC)  --libs libevent_openssl) \
	$(shell $(PKGC)  --libs libssl) \
	$(shell $(LOG4C) --libs)

ifeq ($(TARGET), mingw)
LIBS += -lws2_32 -lexpat
endif

SOURCES = \
	echo-log.c     \
	echo-memory.c  \
	echo-dlist.c   \
	echo-options.c \
	echo-ssl.c     \
	echo-net.c     \
	echo-client.c  \
	echo-server.c  \
	echo.c

HEADERS = \
	echo-log.h     \
	echo-memory.h  \
	echo-dlist.h   \
	echo-options.h \
	echo-ssl.h     \
	echo-net.h     \
	echo-client.h  \
	echo-server.h

# --------------------------------------------------------------------
all: $(CROSS)echo$(EXE)

$(CROSS)echo$(EXE): $(SOURCES:.c=.o)
	$(CC) -o $@ $(CFLAGS) $(LDFLAGS) $^ $(LIBS)

$(SOURCES:.c=.o): $(HEADER)

clean:
	rm -f $(SOURCES:.c=.o)
	rm -f $(CROSS)echo$(EXE)
