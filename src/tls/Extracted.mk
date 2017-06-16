include Makefile
include $(FSTAR_HOME)/ulib/ml/Makefile.include

mlclean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean MEM=HST
	$(MAKE) -C $(FSTAR_HOME)/ucontrib/CoreCrypto/ml clean
	$(MAKE) -C $(FSTAR_HOME)/ucontrib/Platform/ml clean
	$(MAKE) -C $(HACL_HOME)/secure_api/LowCProvider clean
	$(MAKE) -C $(FFI_HOME) clean
	-rm -rf test/*.cm* test/*.o
	-rm -fr $(ODIR)/*.cm* $(ODIR)/*.o $(ODIR)/.tmp $(ODIR)/.deporder *.exe *.cm* *.o *.so *.dll *.out

.PHONY: mlclean

# Makefile voodoo to substitute _ for . in module names
# Note that this is not sound if the F* module name contains an underscore (e.g. AEAD_GCM.fst)
# The dependencies are handled by the .depend files above to allow semi-incremental extraction
# (it is only incremental on connected components of the dependency graph rather than on a per-module basis)
.SECONDEXPANSION:
$(ODIR)/%.ml: $$(subst _,.,%.fst)
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax --codegen OCaml \
	--odir $(ODIR) $(NOEXTRACT) \
	$(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	--include concrete-flags $<

$(ODIR)/Test%.ml: test/Test%.fst
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax --codegen OCaml \
	--odir $(ODIR) $(NOEXTRACT) \
	$(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	--include concrete-flags --extract_module Test$(*F) $<

# Special case for Crypto.AEAD.*: must look in hacl-star/secure_api/aead
# Note that dependencies have absolute paths in the .depend so there is no need 
# to specialize for other internal Hacl paths
$(ODIR)/Crypto_AEAD_%.ml: $(LLDIR)/aead/Crypto.AEAD.%.fst
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax --codegen OCaml \
	--odir $(ODIR) $(NOEXTRACT) \
	$(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	--include concrete-flags $<

# Hacl flags: extract with concrete
$(ODIR)/Flag.ml: $(LLDIR)/test/Flag.fst
	$(FSTAR) $(FSTAR_INCLUDE_PATHS) --lax --codegen OCaml \
	  --odir $(ODIR) $(NOEXTRACT) \
	  $(addprefix --codegen-lib , $(CODEGEN_LIBS)) \
	  --include concrete-flags $<

FSTARLIB=$(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa

.PHONY: $(FSTARLIB)

$(FSTARLIB):
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml

# Try to only rebuild CoreCrypto when necessary
$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmi $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmx $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa: \
		$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.ml $(FSTARLIB)
	$(MAKE) -C $(FSTAR_HOME)/ucontrib/CoreCrypto/ml

# Try to only rebuild LowCProvider when necessary
# Missing: not dependency on hacl-star/code/*
$(LCDIR)/LowCProvider.cmxa: $(FSTARLIB) $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa $(wildcard $(LLDIR)/*/*.fst)
	$(MAKE) -C $(LCDIR)

$(FFI_HOME)/FFICallbacks.cmxa: $(FSTARLIB) $(wildcard $(FFI_HOME)/*.ml) $(wildcard $(FFI_HOME)/*.c)
	$(MAKE) -C $(FFI_HOME)

$(ODIR)/FFIRegister.cmi $(ODIR)/FFIRegister.cmx: $(FFI_HOME)/FFIRegister.ml $(ODIR)/FFI.cmx
	$(OCAMLOPT) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -c $(FFI_HOME)/FFIRegister.ml -o $(ODIR)/FFIRegister.cmx

%.cmi %.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -c $<
	@[ -f $(ODIR)/.deporder ] || echo "$(subst .ml,.cmx,$<) " >> $(ODIR)/.tmp

.depend-ML: \
	$(ODIR)/Flag.ml \
	$(ODIR)/CommonDH.ml \
	$(ODIR)/Crypto_AEAD_Main.ml \
	$(ODIR)/HandshakeLog.ml \
	$(ODIR)/Handshake.ml \
	$(ODIR)/FFI.ml \
	$(ODIR)/TestAPI.ml \
	$(ODIR)/TestFFI.ml
	OCAMLPATH=$(FSTAR_HOME)/bin ocamlfind dep -native -slash -all $(OCAMLPKG) $(OCAML_INCLUDE_PATHS) $(addsuffix /*.ml,$(OCAML_PATHS)) > .depend-ML

-include .depend-ML

$(ODIR)/.deporder: $(FSTARLIB) $(ODIR)/FFI.cmx $(ODIR)/TestAPI.cmx $(ODIR)/TestFFI.cmx
	@echo "=== Note: ML dependencies may be outdated. If you have a link-time error, run 'make mlclean' ==="
	@cp $(ODIR)/.tmp $(ODIR)/.deporder

# We don't pass -I $(ODIR) because it causes trouble on Windows about duplicate modules
mitls.cmxa: \
  $(FSTARLIB) \
  $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa \
  $(LCDIR)/LowCProvider.cmxa \
  $(FFI_HOME)/FFICallbacks.cmxa \
  $(ODIR)/.deporder $(ODIR)/FFI.cmx \
  $(ODIR)/FFIRegister.cmx
	$(OCAMLOPT_BARE) $(addprefix -I ,$(filter-out $(ODIR),$(OCAML_PATHS))) -a `cat $(ODIR)/.deporder` $(ODIR)/FFIRegister.cmx -o mitls.cmxa

mitls.exe: mitls.cmxa test/mitls.cmx $(FSTARLIB)
	$(OCAMLOPT) -linkpkg $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) -I test/ -g \
	  $(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa \
	  $(FFI_HOME)/FFICallbacks.cmxa $(LCDIR)/LowCProvider.cmxa \
	  mitls.cmxa $(LCDIR)/libllcrypto.a test/mitls.cmx -o mitls.exe

test.out: mitls.cmxa $(ODIR)/TestKS.ml $(ODIR)/TestDH.ml $(ODIR)/TestGCM.ml test/parsing_test.ml test/test_hkdf.ml test/test_main.ml $(FSTARLIB)
	$(OCAMLOPT) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) \
	$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa \
	$(LCDIR)/libllcrypto.a $(LCDIR)/LowCProvider.cmx \
	mitls.cmxa \
	$(ODIR)/TestKS.ml $(ODIR)/TestDH.ml $(ODIR)/TestGCM.ml test/parsing_test.ml test/test_hkdf.ml test/test_main.ml -o test.out

test: test.out mitls.exe cmitls.exe
	# Unit tests from test/test_main.ml
	$(EXTRA_PATH) ./test.out
	# Run mitls.exe 
	./mitls.exe  -v 1.2 -ffi www.google.com
	./mitls.exe  -v 1.2 www.microsoft.com
	#./mitls.exe -v 1.3. www.google.com failing due to different draft versions
	./cmitls.exe -v 1.2 www.google.com

# FFI support - calling from C into miTLS. TODO: remove duplication somehow
ifeq ($(OS),Windows_NT)
LIBMITLS=libmitls.dll

$(LIBMITLS): mitls.cmxa $(FSTARLIB)
	$(OCAMLOPT) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) \
	$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa \
	$(LCDIR)/libllcrypto.a $(LCDIR)/LowCProvider.cmx \
	$(FFI_HOME)/FFICallbacks.cmxa \
	-linkall -output-obj -g mitls.cmxa -o $(LIBMITLS)
else
UNAME_S = $(shell uname -s)
LIBMITLS=libmitls.so
ifeq ($(UNAME_S),Darwin)
$(LIBMITLS): mitls.cmxa $(FSTARLIB)
	$(OCAMLOPT) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) \
	$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa \
	$(LCDIR)/libllcrypto.a $(LCDIR)/LowCProvider.cmx \
	$(FFI_HOME)/FFICallbacks.cmxa \
	-linkall -runtime-variant _pic -ccopt -dynamiclib -ccopt -lasmrun -g mitls.cmxa -o libmitls.dylib
	$(OCAMLOPT) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) \
	$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa \
	$(LCDIR)/libllcrypto.a $(LCDIR)/LowCProvider.cmx \
	$(FFI_HOME)/FFICallbacks.cmxa \
	-linkall -runtime-variant _pic -ccopt -dynamiclib -g mitls.cmxa -o $(LIBMITLS)
else
$(LIBMITLS): mitls.cmxa $(FSTARLIB)
    # pass "-z noexecstack" to better support Bash on Windows
    # Use a version script to ensure that CoreCrypto calls to OpenSSL crypto are resolved by 
    #   libcrypt.a at link time, not against libcrypto*.so at run-time, as version mismatches
    #   can result in heap corruptions and crashes.
	$(OCAMLOPT) $(OCAMLOPTS) $(OCAML_INCLUDE_PATHS) \
	$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/CoreCrypto.cmxa \
	$(LCDIR)/libllcrypto.a $(LCDIR)/LowCProvider.cmx \
	$(FFI_HOME)/FFICallbacks.cmxa \
	-linkall -runtime-variant _pic -output-obj -g mitls.cmxa -o $(LIBMITLS) \
	-ccopt "-Xlinker -z -Xlinker noexecstack -Xlinker --version-script -Xlinker libmitls_version_script"
endif
endif

tls-ffi: $(LIBMITLS)

# ask OCaml about the name of the native C compiler.  This will be mingw on Windows.
NATIVE_C_COMPILER=$(shell ocamlfind opt -config | grep native_c_compiler | sed -e "s/native_c_compiler: //")
NATIVE_C_LIBRARIES=$(shell ocamlfind opt -config | grep native_c_libraries | sed -e "s/native_c_libraries: //")

# C test of the FFI
cmitls.o: cmitls.c $(FFI_HOME)/mitlsffi.h
	$(NATIVE_C_COMPILER) -g -c -I$(FFI_HOME) -g -Wall -O0 cmitls.c
cmitls.exe: cmitls.o $(LIBMITLS)
	$(NATIVE_C_COMPILER) -g -o cmitls.exe cmitls.o $(LIBMITLS) $(NATIVE_C_LIBRARIES)

# our interactive tests; the baseline is make client{|12|13} vs make server 

server::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.2 -v 1.3 -s -cert ../../data/server-ecdsa.crt -key ../../data/server-ecdsa.key 0.0.0.0 4443 -sigalgs ECDSA+SHA384
server12::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.2 -v 1.2 -s -cert ../../data/server.crt -key ../../data/server.key 0.0.0.0 4443 -sigalgs RSA+SHA256
server13::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.3 -v 1.3 -s -cert ../../data/server-ecdsa.crt -key ../../data/server-ecdsa.key 0.0.0.0 4443 -sigalgs ECDSA+SHA256
server-psk::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.3 -v 1.3 -s -psk TestPSK:00 -cert ../../data/server-ecdsa.crt -key ../../data/server-ecdsa.key 0.0.0.0 4443 -sigalgs ECDSA+SHA384
server-0rtt::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.3 -v 1.3 -s -cert ../../data/server-ecdsa.crt -key ../../data/server-ecdsa.key 0.0.0.0 4443 -sigalgs ECDSA+SHA384 -0rtt
cserver::
	OCAMLRUNPARAM=b ./cmitls.exe -mv 1.2 -v 1.3 -s -cert ../../data/server-ecdsa.crt -key ../../data/server-ecdsa.key 0.0.0.0 4443 -sigalgs ECDSA+SHA384
cserver12::
	OCAMLRUNPARAM=b ./cmitls.exe -mv 1.2 -v 1.2 -s -cert ../../data/server.crt -key ../../data/server.key 0.0.0.0 4443 -sigalgs RSA+SHA256
cserver13::
	OCAMLRUNPARAM=b ./cmitls.exe -mv 1.3 -v 1.3 -s -cert ../../data/server-ecdsa.crt -key ../../data/server-ecdsa.key 0.0.0.0 4443 -sigalgs ECDSA+SHA384
cserver-psk::
	OCAMLRUNPARAM=b ./cmitls.exe -mv 1.3 -v 1.3 -s -psk TestPSK:00 -cert ../../data/server-ecdsa.crt -key ../../data/server-ecdsa.key 0.0.0.0 4443 -sigalgs ECDSA+SHA384

client13::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.3 -v 1.3 127.0.0.1 4443 
client-psk::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.3 -v 1.3 -psk TestPSK:00 -offerpsk TestPSK 127.0.0.1 4443
client-0rtt::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.3 127.0.0.1 4443 -reconnect -0rtt
client12::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.2 -v 1.2 127.0.0.1 4443 
client::
	OCAMLRUNPARAM=b ./mitls.exe -mv 1.2 -v 1.3 127.0.0.1 4443
cclient13::
	OCAMLRUNPARAM=b ./cmitls.exe -mv 1.3 -v 1.3 127.0.0.1 4443
cclient-psk::
	OCAMLRUNPARAM=b ./cmitls.exe -mv 1.3 -v 1.3 -psk TestPSK:00 -offerpsk TestPSK 127.0.0.1 4443
cclient12::
	OCAMLRUNPARAM=b ./cmitls.exe -mv 1.2 -v 1.2 127.0.0.1 4443
cclient::
	OCAMLRUNPARAM=b ./cmitls.exe -mv 1.2 -v 1.3 127.0.0.1 4443

.PHONY: test tls-ffi server server12 server13 client client12 client13 cserver cserver12 cserver13 cclient cclient12 cclient3

.DEFAULT:

/mitls.exe -mv 1.3 -s -psk TestPSK:00 -cert ../../data/server-ecdsa.crt -key ../../data/server-ecdsa.key 127.0.0.1 4443 -sigalgs ECDSA+SHA256 -0rtt
