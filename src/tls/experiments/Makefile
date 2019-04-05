# ------------------ Dependencies on F* & its libraries --------------
# Default F* location. 
FSTAR_HOME=../../../../FStar
# This location can easily be overridden by doing:
#   FSTAR_HOME=../../../fstar make mitls.exe
# BUT NOT AS FOLLOWS
#   make FSTAR_HOME=../../../fstar mitls.exe
# the latter form won't work because FSTAR_HOME will incorrectly override
# values in recursive invocations of $(MAKE)...

LOWPARSE_HOME=../../../../quackyducky/src/lowparse

#OPTIONS=--fstar_home $(FSTAR_HOME)

FSTARFLAGS=$(OPTIONS) $(OTHERFLAGS)
FSTAR=$(FSTAR_HOME)/bin/fstar.exe \
      $(FSTARFLAGS)

CONTRIB=ucontrib

CDIR=$(FSTAR_HOME)/$(CONTRIB)/CoreCrypto/fst/
PDIR=$(FSTAR_HOME)/$(CONTRIB)/Platform/fst/

HINTS_ENABLED?=--use_hints
VERFLAGS=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
  --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection \
  $(HINTS_ENABLED)

FSTAR_INCLUDE_PATHS=--include .. --include $(LOWPARSE_HOME) --include $(FSTAR_HOME)/../kremlin/kremlib

# Lax-checking one file at a time
%.fst-lax: $(LIBFILES)
	$(FSTAR) $(VERFLAGS) --lax \
	$(FSTAR_INCLUDE_PATHS) \
	--include ../concrete-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Verifying one file at a time
%.fst-ver: $(LIBFILES)
	$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ../ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

%.fsti-ver: $(LIBFILES)
	$(FSTAR) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ../ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fsti

# Targets to get F* arguments in interactive mode
%.fst-in: 
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS)

%.fsti-in: 
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include ../ideal-flags \
	--verify_module $(basename $(notdir $@)) \
	$(addsuffix .fst,$(VERIFY))
