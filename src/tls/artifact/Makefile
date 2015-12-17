all: TLSError.fst-ver TLSConstants.fst-ver Nonce.fst-ver TLSInfo.fst-ver Range.p.fst-ver LHAEPlain.fst-ver AEAD_GCM.fst-ver StatefulLHAE.fst-ver

.PHONY: check-env

check-env:
ifndef FSTAR_HOME
	@echo ----------------------------------------------------------------------
	@echo Please set the FSTAR_HOME environment variable.
	@echo You may use the setenv.sh script in the root of the F* release.
	@echo ----------------------------------------------------------------------
	@exit 1
endif

clean:
	rm -rf *.ml *.p.* *.cm* *.o *~

# ------------------ dependencies on Fstar & its libraries --------------------

STDLIB_ADMITS=Char

STDLIB=ext.fst classical.fst FStar.Set.fsi FStar.Set.fst FStar.Heap.fst map.fst listTot.fst hyperHeap.fst \
stHyperHeap.fst allHyperHeap.fst char.fsi string.fst list.fst listproperties.fst seq.fsi seq.fst\
seqproperties.fst
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(STDLIB)

PDIR=$(FSTAR_HOME)/contrib/Platform/fst/
PLATFORM=$(addprefix $(PDIR),Bytes.fst Date.fst Error.fst Tcp.fst)

CDIR=$(FSTAR_HOME)/contrib/CoreCrypto/fst/
CRYPTO=$(CDIR)CoreCrypto.fst $(CDIR)DHDB.fst

VERFLAGS=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 100

LIBFILES = $(PLATFORM) $(CRYPTO) $(DHDB)

# ------------------------- miTLS* -------------------------------------------

# these files are the stable inputs for verification
TLSVER=TLSError.fst TLSConstants.fst Nonce.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fsti Cert.fsti TLSInfo.fst Range.p.fst StatefulPlain.fsti LHAEPlain.fst AEAD_GCM.fst StatefulLHAE.fst 

# these files are verified here
VERIFY=TLSError TLSConstants Nonce TLSInfo Range LHAEPlain AEAD_GCM StatefulLHAE

# admitting things verified elsewhere
ADMITTED=$(addprefix --admit_fsi ,$(addprefix FStar., $(STDLIB_ADMITS)) UntrustedCert CoreCrypto Cert StatefulPlain)

# truncates $(TLSVER) just before $(basename $@).fst
define prefix_cfg
	$(shell str="$(TLSVER)"; echo "$${str%%$(1).$(2)*}")
endef

# truncates $(TLSVER) just after $(basename $@).fst
define prefix_ver
	$(shell str="$(TLSVER)"; echo "$${str%%$(1).$(2)*}$(1).$(2)")
endef

# verifying one file within $(TLSVER)
%.fst-ver: check-env
	$(FSTAR) $(VERFLAGS) $(LIBFILES) $(ADMITTED) $(call prefix_ver,$(basename $@),fst) \
--verify_module $(subst .p,,$(basename $@))

%.fsti-ver: check-env
	$(FSTAR) $(VERFLAGS) $(LIBFILES) $(ADMITTED) $(call prefix_ver,$(basename $@),fsti) \
--verify_module $(subst .p,,$(basename $@))

# prints build-config block for interactive verification
%.fst-cfg:
	@echo '(*--build-config'
	@echo '    options:--trace_error '$(VERFLAGS) $(ADMITTED)' --verify_module '$(subst .p,,$(basename $@))';'
	@echo '    other-files:'$(STDLIB) $(LIBFILES) $(call prefix_cfg,$(basename $@),fst)
	@echo '--*)'

%.fsti-cfg:
	@echo '(*--build-config'
	@echo '    options:--trace_error '$(VERFLAGS) $(ADMITTED)' --verify_module '$(subst .p,,$(basename $@))';'
	@echo '    other-files:'$(STDLIB) $(LIBFILES) $(call prefix_cfg,$(basename $@),fsti)
	@echo '--*)'
