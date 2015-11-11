# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: all clean cstub

# --------------------------------------------------------------------
uname_S := $(shell sh -c 'uname -s 2>/dev/null || echo not')
uname_M := $(shell sh -c 'uname -m 2>/dev/null || echo not')
uname_O := $(shell sh -c 'uname -o 2>/dev/null || echo not')
uname_R := $(shell sh -c 'uname -r 2>/dev/null || echo not')
uname_P := $(shell sh -c 'uname -p 2>/dev/null || echo not')
uname_V := $(shell sh -c 'uname -v 2>/dev/null || echo not')


# --------------------------------------------------------------------
define pki
  $(MAKE) -C pki MODE=$(1) clean
  $(MAKE) -C pki MODE=$(1) dh dsap ca
  $(MAKE) -C pki MODE=$(1) 'import!ca'
  $(MAKE) -C pki MODE=$(1) 'import!$(1).cert-01.mitls.org'
  $(MAKE) -C pki MODE=$(1) 'import!$(1).cert-02.mitls.org'
  $(MAKE) -C pki MODE=$(1) hash
endef

# --------------------------------------------------------------------
all: cstub pki.built
	CYGWIN="$$CYGWIN pipe_byte pipe_nooverlap" ./test-suite.py

ifneq (, $(findstring CYGWIN, $(UNAME_S)))
cstub:
	@true
else
cstub:
	$(MAKE) -C c-stub
endif

pki.built:
	$(call pki,rsa)
	$(call pki,dsa)
	touch $@

# --------------------------------------------------------------------
clean:
	$(MAKE) -C pki MODE=rsa clean
	$(MAKE) -C pki MODE=dsa clean
	if [ "$(uname_O)" != "Cygwin" ]; then \
	  $(MAKE) -C c-stub clean; \
	fi
	rm -f pki.built
