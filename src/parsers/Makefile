QD_HOME ?= ../../quackyducky

all: gen

gen: $(addsuffix .gen,$(wildcard *.rfc))

%.gen: %
	# FIXME: remove the spurious Parse_ prefix later, once the
	# issue of capitalization of module names in QuackyDucky is
	# solved
	mkdir -p generated
	$(QD_HOME)/qd -prefix $(basename $<).Parse_ -odir generated $<
	touch $@

clean:
	rm -rf *.gen generated

.PHONY: all gen clean
