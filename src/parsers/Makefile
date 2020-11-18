QD_HOME ?= ../../../quackyducky

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

test: verify
	+$(MAKE) -C test

generated/Makefile: Makefile.qd
	mkdir -p generated
	cp Makefile.qd $@

clean:
	rm -rf *.gen generated

.PHONY: all gen genmakefile clean verify test
