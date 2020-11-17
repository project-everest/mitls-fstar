QD_HOME ?= ../../../quackyducky

# all: DO NOT enable `verify` for now, not everything currently
# verifies. Anyway, for miTLS, we don't need to verify everything, the
# miTLS dependency system will take care of collecting which generated
# modules are actually needed.

all: verify

gen: parsers.gen

parsers.gen: $(wildcard *.rfc) $(QD_HOME)/qd
	mkdir -p generated
	rm -rf generated/*.fst generated/*.fsti
	for f in $(wildcard *.rfc) ; do	$(QD_HOME)/qd -prefix $$(basename $$f .rfc). -odir generated $$f ; done
	touch $@

genmakefile: generated/Makefile

verify: gen genmakefile
	+$(MAKE) -C generated verify

generated/Makefile: Makefile.qd
	mkdir -p generated
	cp Makefile.qd $@

clean:
	rm -rf *.gen generated

.PHONY: all gen genmakefile clean verify
