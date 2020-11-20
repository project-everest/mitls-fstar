# From https://fstarlang.github.io/lowstar/html/Setup.html#build

all: test

include Makefile.include

test: dist/test.exe

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

.PRECIOUS: %.krml
%.krml:
	time $(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

# F* --> C
# --------

obj/kremlin.rsp: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	for f in $(filter %.krml,$^) ; do echo $$f ; done > $@

dist/Makefile.basic: obj/kremlin.rsp
	mkdir -p $(dir $@)
	$(KRML) -tmpdir $(dir $@) -skip-compilation \
	  @$< \
	  -warn-error @4@5@18 \
	  -fparentheses \
	  -fnoreturn-else \
	  -header header.txt \
	  -bundle 'Test=TestSpecs,Test.*,Parsers.*,LowParse.*,LowStar.*,FStar.*,C,C.\*,Prims' \
	  -o test.exe \
	  -no-prefix Test \
	  -ccopt -Wno-type-limits

# Compiling the generated C code
# ------------------------------

dist/test.exe: dist/Makefile.basic
	$(MAKE) -C $(dir $@) -f $(notdir $<)
	$@
