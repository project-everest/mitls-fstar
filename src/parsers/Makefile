QD_HOME ?= ../../../quackyducky

# all: DO NOT enable `verify` for now, not everything currently
# verifies. Anyway, for miTLS, we don't need to verify everything, the
# miTLS dependency system will take care of collecting which generated
# modules are actually needed.

all: gen # verify

gen: $(addsuffix .gen,$(wildcard *.rfc))

genmakefile: generated/Makefile

verify: gen genmakefile
	+$(MAKE) -C generated verify

generated/Makefile: Makefile.qd
	mkdir -p generated
	cp Makefile.qd $@

%.gen: %
	# FIXME: remove the spurious Parse_ prefix later, once the
	# issue of capitalization of module names in QuackyDucky is
	# solved
	mkdir -p generated
	$(QD_HOME)/qd -prefix $(basename $<). -odir generated $<
	touch $@

clean:
	rm -rf *.gen generated

.PHONY: all gen genmakefile clean verify
