FSTAR_HOME=../../../../FStar
KRML_HOME=../../../../karamel
HACL_HOME=../../../../hacl-star
MITLS_HOME=../../..
include ../Makefile

# Targets to get F* arguments in interactive mode
%.fst-in: 
	@echo $(OPTIONS) $(VERFLAGS) \
	$(FSTAR_INCLUDE_PATHS) \
	--include $(MITLS_HOME)/src/tls \
	--include $(MITLS_HOME)/src/tls/ideal-flags \
	--verify_module $(basename $(notdir $@))
