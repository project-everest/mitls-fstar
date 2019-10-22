HACL_HOME    ?= ../../../../../hacl-star
FSTAR_HOME   ?= ../../../../../FStar
KREMLIN_HOME ?= ../../../../../kremlin
QD_HOME      ?= ../../../../../quackyducky

CACHE_DIR     ?= .
HINT_DIR      ?= .
OUTPUT_DIR    = test-krml
GENERATED_DIR = test-c
OUT_DIR	      = test-c

.PHONY: all test stage1 stage2 clean clean-c distclean

all: test

test:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2

stage1: $(GENERATED_DIR)/Makefile.include

stage2: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

#include $(HACL_HOME)/Makefile.common

FSTAR_INCLUDE_DIRS = \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/providers/evercrypt \
  ../.. \
  ../../../parsers/generated \
  $(QD_HOME)/src/lowparse \
  $(KREMLIN_HOME)/kremlib

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --already_cached 'Prims FStar LowStar C' \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Test.fst

.PRECIOUS: %.krml

$(HINT_DIR):
	mkdir -p $@

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -LowStar -FStar' > $@

include .depend

%.checked: | .depend $(HINT_DIR) $(CACHE_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

LowParse.%.checked Parsers.%.checked: | .depend $(HINT_DIR) $(CACHE_DIR)
	$(FSTAR) --admit_smt_queries true $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@


$(OUTPUT_DIR)/%.krml: | .depend $(OUTPUT_DIR)
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Generation of .c files

KREMLIN=$(KREMLIN_HOME)/krml

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
$(GENERATED_DIR)/Makefile.include: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) -skip-compilation \
	-no-prefix 'ConnectionTable' \
	-no-prefix 'ConnectionTable_Aux' \
	-no-prefix 'Test' \
	-library 'C' \
	-drop 'LowStar,C' \
	-tmpdir $(GENERATED_DIR) \
	$^

ifeq ($(STAGE),2)

include $(GENERATED_DIR)/Makefile.include

# 3. Collect all source files and generate corresponding object files

ALL_GENERATED_FILES = $(addprefix $(GENERATED_DIR)/,$(ALL_C_FILES))
ALL_SOURCES = $(ALL_GENERATED_FILES)

ALL_OBJS = $(patsubst %.c,%.o,$(ALL_SOURCES))

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(KREMLIN_HOME)/kremlib/dist/generic

CFLAGS += -O3 -march=native -mtune=native -funroll-loops
CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable

# GNU Make manual section 4.14
%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(patsubst %.c,%.d,$(ALL_SOURCES))

$(OUT_DIR):
	mkdir -p $@

$(OUT_DIR)/test.exe: $(ALL_OBJS) | $(OUT_DIR)
	$(info ALL_SOURCES is $(ALL_SOURCES))
	cp driver.c $(GENERATED_DIR)
	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/dist/generic -lkremlib $(GENERATED_DIR)/driver.c

.PRECIOUS: %.o

endif # STAGE=2

# 5. Targets for interactive mode

%.fst-in:
	@echo $(addprefix --include ,$(FSTAR_INCLUDE_DIRS)) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(addprefix --include ,$(FSTAR_INCLUDE_DIRS)) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# 6. Clean targets

SHELL=/bin/bash

clean:
	rm -rf $(GENERATED_DIR) $(OUT_DIR)/*.exe $(OUT_DIR)/*.a .depend

clean-c:
	rm -rf $(GENERATED_DIR)/{*.{c,h},Makefile.include,Makefile.basic}

distclean: clean
	rm -rf $(OUT_DIR) $(OUTPUT_DIR) *.checked *.hints
