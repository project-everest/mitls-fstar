module HelperLemmas

open FStar.List
open FStar.Seq
open Predicates
open InitialStateLemma
open ClientHelloLemma
open ServerHelloLemma
open ServerCertificateLemma
open ServerKeyExchangeLemma
open ServerCertificateRequestLemma
open ServerHelloDoneLemma
open ClientCertificateLemma
open ClientKeyExchangeLemma
open ClientCertificateVerifyLemma
open ClientCCSLemma
open ClientFinLemma
open ServerNewSessionTicketLemma
open ServerCCSLemma
open ServerFinLemma
open ClientCCSLastMsgLemma
open ClientFinLastMsgLemma

val initial_state_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = UndefinedMessageType))
    (ensures (StateAfterInitialState state))

#reset-options

val client_hello_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ClientHello ))
    (ensures (StateAfterClientHello state))

#reset-options

val server_hello_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerHello ))
    (ensures (StateAfterServerHello state))

#reset-options

val server_certificate_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerCertificate ))
    (ensures (StateAfterServerCertificate state))

#reset-options

val ske_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerKeyExchange ))
    (ensures (StateAfterServerKeyExchange state))

#reset-options

val scr_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerCertificateRequest ))
    (ensures (StateAfterServerCertificateRequest state))

#reset-options

val shd_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerHelloDone ))
    (ensures (StateAfterServerHelloDone state))

#reset-options

val cc_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ClientCertificate ))
    (ensures (StateAfterClientCertificate state))

#reset-options

val cke_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ClientKeyExchange ))
    (ensures (StateAfterClientKeyExchange state))

#reset-options

val ccv_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ClientCertificateVerify ))
    (ensures (StateAfterClientCertificateVerify state))
 

#reset-options

val get_discriminating_message_from_client_ccs:
  state:state_mon{ isValidState state /\ state.last_message = ClientCCS } ->
  Tot messageType

#reset-options  

val cccs_helper:
  state:state_mon{ isValidState state /\ state.last_message = ClientCCS } ->
  Lemma
    (requires ( True ))
    (ensures (
	 ( ( get_discriminating_message_from_client_ccs state = Finished) ==>  StateAfterClientCCSLastMsg state)
	 /\ ( ( get_discriminating_message_from_client_ccs state <> Finished) ==>  StateAfterClientCCS state) ))

#reset-options

val get_discriminating_message_from_client_fin:
  state:state_mon{ isValidState state /\ state.last_message = ClientFinished } ->
  Tot messageType

#reset-options

val cfin_helper:
  state:state_mon{ isValidState state /\ state.last_message = ClientFinished } ->
  Lemma
    (requires ( True ))
    (ensures (
	 ( ( get_discriminating_message_from_client_fin state = Finished) ==>  StateAfterClientFinLastMsg state)
	 /\ ( ( get_discriminating_message_from_client_fin state <> Finished) ==>  StateAfterClientFin state) ))

#reset-options

val snst_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerNewSessionTicket ))
    (ensures (StateAfterServerNewSessionTicket state))

#reset-options

val sccs_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerCCS ))
    (ensures (StateAfterServerCCS state))

#reset-options

val sfin_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerFinished ))
    (ensures (StateAfterServerFin state))
		       
