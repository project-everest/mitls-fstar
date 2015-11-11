# -*- Makefile -*-

# --------------------------------------------------------------------
# Available modes: rsa, dsa
MODE ?= rsa

# --------------------------------------------------------------------
C  = CC
ST = State
L  = Location
O  = Organization
OU = 
CN = mitls.org
EA = root@mitls.org

# --------------------------------------------------------------------
export PKI := $(CURDIR)/$(MODE)

CASUBJECT=/C=$(C)/ST=$(ST)/L=$(L)/O=$(O)/OU=$(OU)/CN=$(MODE).$(CN)/emailAddress=$(EA)

# --------------------------------------------------------------------
uname_S := $(shell sh -c 'uname -s 2>/dev/null || echo not')
uname_M := $(shell sh -c 'uname -m 2>/dev/null || echo not')
uname_O := $(shell sh -c 'uname -o 2>/dev/null || echo not')
uname_R := $(shell sh -c 'uname -r 2>/dev/null || echo not')
uname_P := $(shell sh -c 'uname -p 2>/dev/null || echo not')
uname_V := $(shell sh -c 'uname -v 2>/dev/null || echo not')

JSKPW = 123456

# --------------------------------------------------------------------
define layout
	if [ ! -d $(PKI) ]; then \
	    mkdir -p $(PKI);     \
	fi

	if [ ! -d $(PKI)/db ]; then             \
		mkdir $(PKI)/db;                    \
		mkdir $(PKI)/db/ca.db.certs;        \
		touch $(PKI)/db/ca.db.serial;       \
		touch $(PKI)/db/ca.db.index;        \
		echo '01' > $(PKI)/db/ca.db.serial; \
	fi

	if [ ! -d $(PKI)/certificates ]; then \
		mkdir $(PKI)/certificates;        \
	fi

	if [ ! -d $(PKI)/imported ]; then \
		mkdir $(PKI)/imported;        \
	fi
endef

# --------------------------------------------------------------------
.PHONY: ca dh dsap layout clean hash
.PHONY: cert!% import!%

.PRECIOUS: $(MODE)/certificates/%.p12
.PRECIOUS: $(MODE)/certificates/%.key
.PRECIOUS: $(MODE)/certificates/%.crt
.PRECIOUS: $(MODE)/certificates/%.csr
.PRECIOUS: $(MODE)/certificates/ca.key
.PRECIOUS: $(MODE)/certificates/ca.crt
.PRECIOUS: $(MODE)/imported/%.imported

# --------------------	------------------------------------------------
all:
	@echo "No default rule" >&2

# --------------------------------------------------------------------
cert!%: $(MODE)/certificates/%.p12
	@true

import!%: $(MODE)/imported/%.imported
	@true

# --------------------------------------------------------------------
ca: layout $(MODE)/certificates/ca.crt

$(MODE)/certificates/ca.crt: $(MODE)/certificates/ca.key
	openssl req -new -x509 -batch          \
	    -subj   "$(CASUBJECT)"             \
	    -config $(CURDIR)/config/ca.config \
	    -key    $<                         \
	    -out    $@
	openssl x509 -in $@ -noout -text

# --------------------------------------------------------------------
dh: layout $(MODE)/certificates/dh.pem

$(MODE)/certificates/dh.pem:
	openssl dhparam -out $@ 1024

# --------------------------------------------------------------------
dsap: layout $(MODE)/certificates/dsap.pem

$(MODE)/certificates/dsap.pem:
	openssl dsaparam -out $@ 1024

# --------------------------------------------------------------------
ifeq ($(MODE),rsa)
$(MODE)/certificates/%.key:
	openssl genrsa -out $@ 1024
endif

ifeq ($(MODE),dsa)
$(MODE)/certificates/%.key: $(MODE)/certificates/dsap.pem
	openssl gendsa -out $@ $(MODE)/certificates/dsap.pem
endif

$(MODE)/certificates/%.p12: $(MODE)/certificates/%.crt $(MODE)/certificates/ca.crt
	echo | openssl pkcs12 -export -password stdin \
	    -in       $(PKI)/certificates/$*.crt   \
	    -inkey    $(PKI)/certificates/$*.key   \
	    -name     "uTLS PKI ($*)" \
	    -out      $(PKI)/certificates/$*.p12

$(MODE)/certificates/%.csr: $(MODE)/certificates/%.key
	openssl req -new -batch \
	    -subj   "/C=$(C)/ST=$(ST)/L=$(L)/O=$(O)/OU=$(OU)/CN=$*/emailAddress=$(EA)" \
	    -config config/ca.config \
	    -key    $< \
	    -out    $@

$(MODE)/certificates/%.crt: $(MODE)/certificates/%.csr $(MODE)/certificates/ca.crt
	openssl ca -batch -config config/ca.config -in $< -out $@
	openssl x509 -in $@ -noout -text

# --------------------------------------------------------------------
IMPORTED := $(wildcard $(MODE)/imported/*.imported)
IMPORTED := $(patsubst $(MODE)/imported/%.imported,%,$(IMPORTED))
IMPORTED := $(filter-out ca,$(IMPORTED))

ifeq ($(uname_O),Cygwin)
$(MODE)/imported/ca.imported:
	certutil -f -user -addstore Root $(MODE)/certificates/ca.crt
	touch $@

$(MODE)/imported/%.imported: $(MODE)/certificates/%.p12
	certutil -f -user -p '' -v -importpfx $(MODE)/certificates/$*.p12
	touch $@

clean-store:
	certutil -user -delstore Root $(MODE).$(CN)
	for i in $(IMPORTED); do                   \
	  certutil -user -delstore My $$i || true; \
	done
	sleep 2						# Yes, I know...
else
$(MODE)/imported/ca.imported:
	umask 077; certmgr -add -c Trust $(MODE)/certificates/ca.crt
	touch $@

$(MODE)/imported/%.imported: $(MODE)/certificates/%.p12
	umask 077; ( set -e; \
	  certmgr -add       -c My $(MODE)/certificates/$*.crt;      \
	  certmgr -importKey -c -p '' My $(MODE)/certificates/$*.p12 \
	)
	touch $@

clean-store:
	for i in $$(support/mono-crt-cleanup.py $(MODE).$(CN) $(IMPORTED)); do \
	  certmgr -del -c My    $$i || true; \
	  certmgr -del -c Trust $$i || true; \
	done
endif

$(MODE)/imported/ca.imported.jsk:
	(echo $(JSKPW); echo $(JSKPW); echo yes) | \
	  keytool -keystore $(MODE)/JSK.db \
	    -importcert -file $(MODE)/certificates/ca.crt
	touch $@

$(MODE)/imported/%.imported.jsk: $(MODE)/certificates/%.p12
	(echo $(JSKPW); echo yes) | \
	  keytool -keystore $(MODE)/JSK.db \
	    -importkeystore \
	    -srckeystore $(MODE)/certificates/$*.p12 \
	    -srcstorepass '' \
	    -srcstoretype pkcs12 \
	    -destkeystore $(MODE)/JSK.db
	touch $@

# --------------------------------------------------------------------
hash:
	cd $(MODE)/db/ca.db.certs && c_rehash .

# --------------------------------------------------------------------
layout:
	@$(call layout)

# --------------------------------------------------------------------
clean: clean-store
	rm -rf $(PKI)/certificates
	rm -rf $(PKI)/db
	rm -rf $(PKI)/imported
	rm  -f $(PKI)/JSK.db
	if [ -d $(PKI) ]; then rmdir $(PKI); fi
