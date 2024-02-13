EVERPARSE_HOME ?= ../../../everparse
QD_BIN = $(EVERPARSE_HOME)/bin/qd.exe

# The verify dependency is not strictly necessary here.
# For miTLS, we don't need to verify everything, the
# miTLS dependency system would take care of collecting which generated
# modules are actually needed.

all: gen verify

gen: $(addsuffix .gen,$(wildcard *.rfc))

genmakefile: generated/Makefile

verify: gen genmakefile
	+$(MAKE) -C generated verify

generated/Makefile: Makefile.qd
	mkdir -p generated
	cp Makefile.qd $@

%.gen: % $(QD_BIN)
	mkdir -p generated
#	-rm generated/$(patsubst %.rfc, %, $(basename $<)).*.{fst,fsti}
	$(QD_BIN) -prefix $(basename $<). -odir generated $<
	touch $@

clean:
	rm -rf *.gen generated

.PHONY: all gen genmakefile clean verify
