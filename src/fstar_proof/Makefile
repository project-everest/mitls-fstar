ifeq ($(OS),Windows_NT)
	BIN=FStar.exe
else 
	BIN=fstar.exe
endif

#FSTAR_HOME=~/tmp/FStar
FSTAR=$(FSTAR_HOME)/bin/$(BIN)

ARGS=--z3timeout 3600 --admit_fsi FStar.Set --admit_fsi FStar.Seq

LIB=FStar.FunctionalExtensionality.fst classical.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst list.fst listproperties.fst seq.fsi seqproperties.fst predicates.fst

all:
	@echo Verifying initial state
	$(FSTAR) $(ARGS) $(LIB) initial_state_lemma.fst --verify_module InitialStateLemma

	@echo Verifying client hello state
	$(FSTAR) $(ARGS) $(LIB) initial_state_lemma.fsti --admit_fsi InitialStateLemma client_hello_lemma.fst --verify_module ClientHelloLemma

	@echo Verifying server hello state
	$(FSTAR) $(ARGS) $(LIB) client_hello_lemma.fsti --admit_fsi ClientHelloLemma server_hello_lemma.fst --verify_module ServerHelloLemma

	@echo Verifying server certificate state
	$(FSTAR) $(ARGS) $(LIB) server_hello_lemma.fsti --admit_fsi ServerHelloLemma server_certificate_lemma.fst --verify_module ServerCertificateLemma

	@echo Verifying server key exchange state
	$(FSTAR) $(ARGS) $(LIB) server_hello_lemma.fsti --admit_fsi ServerHelloLemma server_certificate_lemma.fsti --admit_fsi ServerCertificateLemma server_key_exchange_lemma.fst --verify_module ServerKeyExchangeLemma

	@echo Verifying server certificate request state
	$(FSTAR) $(ARGS) $(LIB) server_certificate_lemma.fsti --admit_fsi ServerCertificateLemma server_key_exchange_lemma.fsti --admit_fsi ServerKeyExchangeLemma server_certificate_request_lemma.fst --verify_module ServerCertificateRequestLemma

	@echo Verifying server hello done state
	$(FSTAR) $(ARGS) $(LIB) server_certificate_lemma.fsti --admit_fsi ServerCertificateLemma server_key_exchange_lemma.fsti --admit_fsi ServerKeyExchangeLemma server_certificate_request_lemma.fsti --admit_fsi ServerCertificateRequestLemma server_hello_done_lemma.fst --verify_module ServerHelloDoneLemma

	@echo Verifying client certificate
	$(FSTAR) $(ARGS) $(LIB) server_hello_done_lemma.fsti --admit_fsi ServerHelloDoneLemma client_certificate_lemma.fst --verify_module ClientCertificateLemma

	@echo Verifying client key exchange
	$(FSTAR) $(ARGS) $(LIB) server_hello_done_lemma.fsti --admit_fsi ServerHelloDoneLemma client_certificate_lemma.fsti --admit_fsi ClientCertificateLemma client_key_exchange_lemma.fst --verify_module ClientKeyExchangeLemma

	@echo Verifying client certificate verify
	$(FSTAR) $(ARGS) $(LIB) client_key_exchange_lemma.fsti --admit_fsi ClientKeyExchangeLemma client_certificate_verify_lemma.fst --verify_module ClientCertificateVerifyLemma

	@echo Verifying client cipher spec change
	$(FSTAR) $(ARGS) $(LIB) client_certificate_lemma.fsti --admit_fsi ClientCertificateLemma client_key_exchange_lemma.fsti --admit_fsi ClientKeyExchangeLemma client_certificate_verify_lemma.fsti --admit_fsi ClientCertificateVerifyLemma client_ccs_lemma.fst --verify_module ClientCCSLemma

	@echo Verifying client finished
	$(FSTAR) $(ARGS) $(LIB) client_ccs_lemma.fsti --admit_fsi ClientCCSLemma client_fin_lemma.fst --verify_module ClientFinLemma

	@echo Verifying server new session ticket
	$(FSTAR) $(ARGS) $(LIB) server_hello_lemma.fsti --admit_fsi ServerHelloLemma client_fin_lemma.fsti --admit_fsi ClientFinLemma server_new_session_ticket_lemma.fst --verify_module ServerNewSessionTicketLemma

	@echo Verifying server cipher spec change
	$(FSTAR) $(ARGS) $(LIB) server_hello_lemma.fsti --admit_fsi ServerHelloLemma client_fin_lemma.fsti --admit_fsi ClientFinLemma server_new_session_ticket_lemma.fsti --admit_fsi ServerNewSessionTicketLemma server_ccs_lemma.fst --verify_module ServerCCSLemma

	@echo Verifying server finished
	$(FSTAR) $(ARGS) $(LIB)  server_ccs_lemma.fsti --admit_fsi ServerCCSLemma server_fin_lemma.fst --verify_module ServerFinLemma

	@echo Verifying client ccs last message
	$(FSTAR) $(ARGS) $(LIB) server_fin_lemma.fsti --admit_fsi ServerFinLemma client_ccs_last_msg_lemma.fst --verify_module ClientCCSLastMsgLemma

	@echo Verifying client finished last message
	$(FSTAR) $(ARGS) $(LIB) client_ccs_last_msg_lemma.fsti --admit_fsi ClientCCSLastMsgLemma client_fin_last_msg_lemma.fst --verify_module ClientFinLastMsgLemma

	@echo Helper lemmas
	$(FSTAR) $(ARGS) $(LIB) helper_lemmas.fst --verify_module HelperLemmas

	@echo Injectivity lemma
	$(FSTAR) $(ARGS) FStar.FunctionalExtensionality.fst classical.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst list.fst listproperties.fst seq.fsi seqproperties.fst predicates.fsti --admit_fsi Predicates initial_state_lemma.fsti --admit_fsi InitialStateLemma client_hello_lemma.fsti --admit_fsi ClientHelloLemma server_hello_lemma.fsti --admit_fsi ServerHelloLemma server_certificate_lemma.fsti --admit_fsi ServerCertificateLemma server_key_exchange_lemma.fsti --admit_fsi ServerKeyExchangeLemma server_certificate_request_lemma.fsti --admit_fsi ServerCertificateRequestLemma server_hello_done_lemma.fsti --admit_fsi ServerHelloDoneLemma client_certificate_lemma.fsti --admit_fsi ClientCertificateLemma client_key_exchange_lemma.fsti --admit_fsi ClientKeyExchangeLemma client_certificate_verify_lemma.fsti --admit_fsi ClientCertificateVerifyLemma client_ccs_lemma.fsti --admit_fsi ClientCCSLemma client_fin_lemma.fsti --admit_fsi ClientFinLemma server_new_session_ticket_lemma.fsti --admit_fsi ServerNewSessionTicketLemma server_ccs_lemma.fsti --admit_fsi ServerCCSLemma server_fin_lemma.fsti --admit_fsi ServerFinLemma client_ccs_last_msg_lemma.fsti --admit_fsi ClientCCSLastMsgLemma client_fin_last_msg_lemma.fsti --admit_fsi ClientFinLastMsgLemma helper_lemmas.fsti --admit_fsi HelperLemmas injectivity_lemma.fst --verify_module InjectivityLemma
