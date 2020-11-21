# From https://fstarlang.github.io/lowstar/html/Setup.html#build

all: test.exe

include Makefile.include

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

FSTAR_EXTRACT=--extract '* -Prims -FStar'

# This is the only bulletproof way that I know of forcing a regeneration of the
# .depend file every single time. Why, you may ask? Well, it's frequent enough
# to add a new file that you don't want to decipher a cryptic error only to
# remember you should run `make depend`. Also, if you move files around, it's
# good to force regeneration even though .depend may be more recent than the
# mtime of the moved files.
ifndef MAKE_RESTARTS
obj/.depend: .FORCE
	mkdir -p obj
	+$(MAKE) -f Makefile.qd
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

obj/Parsers.%.checked: FSTAR_FLAGS=--admit_smt_queries true

%.checked: FSTAR_FLAGS=
%.checked: | obj
	time $(FSTAR) $(FSTAR_FLAGS) $< && touch -c $@

# Extraction
# ----------

.PRECIOUS: %.ml
%.ml:
	time $(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--warn_error -342 \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

# Compiling the generated OCaml code
# ----------------------------------

# This is much more difficult, and you're probably better off calling OCamlbuild
# or Dune at this stage. Nonetheless, I still show how to compile the generate
# OCaml code with only GNU make and without relying on an external tool or an
# extra dependency analysis.

# First complication... no comment.
ifeq ($(OS),Windows_NT)
  export OCAMLPATH := $(FSTAR_HOME)/bin;$(OCAMLPATH)
else
  export OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif

# Second complication: F* generates a list of ML files in the reverse linking
# order. No POSIX-portable way of reversing the order of a list.
TAC = $(shell which tac >/dev/null 2>&1 && echo "tac" || echo "tail -r")

ALL_CMX_FILES = $(patsubst %.ml,%.cmx,$(shell echo $(ALL_ML_FILES) | $(TAC)))

# Finally, how to compile things...

OCAMLOPT = ocamlfind opt -package fstarlib -linkpkg -g -I $(TARGET_DIR) -w -8-20-26

.PRECIOUS: obj/%.cmx
obj/%.cmx: obj/%.ml
	$(OCAMLOPT) -c $< -o $@

test.exe: $(ALL_CMX_FILES)
	$(OCAMLOPT) $^ -o $@
	./$@
