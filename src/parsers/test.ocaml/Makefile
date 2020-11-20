# From https://fstarlang.github.io/lowstar/html/Setup.html#build

all: test

include Makefile.include

test: $(ALL_CHECKED_FILES)

clean:
	rm -rf obj dist

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: all test %.fsti-in %.fst-in clean

FSTAR_NO_FLAGS = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_OPTIONS) \
  --odir obj --cache_checked_modules --cmi --warn_error '+241@247+285' \
  --cache_dir obj

FSTAR_ROOTS = $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIRS))) \

# This is the only bulletproof way that I know of forcing a regeneration of the
# .depend file every single time. Why, you may ask? Well, it's frequent enough
# to add a new file that you don't want to decipher a cryptic error only to
# remember you should run `make depend`. Also, if you move files around, it's
# good to force regeneration even though .depend may be more recent than the
# mtime of the moved files.
ifndef MAKE_RESTARTS
obj/.depend: .FORCE
	mkdir -p obj
	$(FSTAR_NO_FLAGS) --dep full $(notdir $(FSTAR_ROOTS)) $(FSTAR_EXTRACT) > $@

.PHONY: .FORCE
.FORCE:
endif

include obj/.depend

# Verification
# ------------

# Everest-specific idiom: all makefiles accept OTHERFLAGS, for instance, if one
# wants to rebuild with OTHERFLAGS="--admit_smt_queries true". We just don't
# pass such flags to the dependency analysis.
FSTAR = $(FSTAR_NO_FLAGS) $(OTHERFLAGS)

obj:
	mkdir -p $@

%.checked: | obj
	time $(FSTAR) $< && touch -c $@

# Extraction
# ----------

.PRECIOUS: %.ml
%.ml:
	time $(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

# Compiling the generated OCaml code
# ----------------------------------
