# This is a standalone Makefile. It can be used to verify LowParse
# independently of the rest of miTLS. It might be used by the rest of
# the miTLS build system, but the options passing has not been
# harmonized yet.

include Makefile.include

INCLUDE_PATHS:=

ifeq ($(KREMLIN_HOME),)
  INCLUDE_KREMLIN=
else
  INCLUDE_KREMLIN=--include $(KREMLIN_HOME)/kremlib
endif

FSTAR_OPTIONS ?=
#--use_two_phase_tc true

MY_FSTAR=$(FSTAR_HOME)/bin/fstar.exe --use_hints --cache_checked_modules $(addprefix --include , $(INCLUDE_PATHS)) $(INCLUDE_KREMLIN)  $(FSTAR_OPTIONS)

all: verify-spec verify-slow

# a.fst.checked is the binary, checked version of a.fst
%.checked: %
	$(MY_FSTAR) $*
	touch $@

$(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa:
	make -C $(FSTAR_HOME)/ulib/ml

clean:
	rm -rf _build $(OUTPUT_DIRECTORY) *~ *.checked* .depend

.depend: $(LOWPARSE_FILES)
	$(MY_FSTAR) --dep full $(LOWPARSE_FILES) > .depend

depend: .depend

include .depend

# The default target is to verify all files, without extracting anything
# It needs to be here, because it reads the variable ALL_FST_FILES in .depend
verify-all: $(addsuffix .checked, $(LOWPARSE_FILES))

verify-spec: $(addsuffix .checked, $(LOWPARSE_SPEC_FILES))

verify-slow: $(addsuffix .checked, $(LOWPARSE_SLOW_FILES))

extract-c: example/LowParseExample.c example2/LowParseExample2.c

example/LowParseExample.c: LowParseExample.fst.checked
	$(KREMLIN_HOME)/krml -skip-linking -tmpdir example -bundle 'LowParse.*' -bundle LowParseExample.Aux -drop 'FStar.Tactics.*' -drop 'FStar.Reflection.*' LowParseExample.fst

example2/LowParseExample2.c: LowParseExample2.fst.checked
	$(KREMLIN_HOME)/krml -skip-linking -tmpdir example2 -bundle 'LowParse.*' -drop 'FStar.Tactics.*' -drop 'FStar.Reflection.*' LowParseExample2.fst
