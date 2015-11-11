module HelperLemmas

open FStar.List
open FStar.Seq
open Predicates

val initial_state_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = UndefinedMessageType))
    (ensures (StateAfterInitialState state))
let initial_state_helper state = ()

#reset-options

val client_hello_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ClientHello ))
    (ensures (StateAfterClientHello state))
let client_hello_helper state = ()

#reset-options

val server_hello_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerHello ))
    (ensures (StateAfterServerHello state))
let server_hello_helper state = ()

#reset-options

val server_certificate_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerCertificate ))
    (ensures (StateAfterServerCertificate state))
let server_certificate_helper state = ()

#reset-options

val ske_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerKeyExchange ))
    (ensures (StateAfterServerKeyExchange state))
let ske_helper state = ()

#reset-options

val scr_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerCertificateRequest ))
    (ensures (StateAfterServerCertificateRequest state))
let scr_helper state = ()

#reset-options

val shd_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerHelloDone ))
    (ensures (StateAfterServerHelloDone state))
let shd_helper state = ()

#reset-options

val cc_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ClientCertificate ))
    (ensures (StateAfterClientCertificate state))
let cc_helper state = ()

#reset-options

val cke_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ClientKeyExchange ))
    (ensures (StateAfterClientKeyExchange state))
let cke_helper state = ()

#reset-options

val ccv_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ClientCertificateVerify ))
    (ensures (StateAfterClientCertificateVerify state))
let ccv_helper state = ()
 

#reset-options

val get_discriminating_message_from_client_ccs:
  state:state_mon{ isValidState state /\ state.last_message = ClientCCS } ->
  Tot messageType
let get_discriminating_message_from_client_ccs state =
  cut( (List.length (state.msg_list) >= 1) /\ True );
  let msg::_ = state.msg_list in
  readMessageType (index msg 0)

#reset-options  

val cccs_helper:
  state:state_mon{ isValidState state /\ state.last_message = ClientCCS } ->
  Lemma
    (requires ( True ))
    (ensures (
	 ( ( get_discriminating_message_from_client_ccs state = Finished) ==>  StateAfterClientCCSLastMsg state)
	 /\ ( ( get_discriminating_message_from_client_ccs state <> Finished) ==>  StateAfterClientCCS state) ))
let cccs_helper state = ()

#reset-options

val get_discriminating_message_from_client_fin:
  state:state_mon{ isValidState state /\ state.last_message = ClientFinished } ->
  Tot messageType
let get_discriminating_message_from_client_fin state =
  cut( ( List.length (state.msg_list) >= 2) /\ True );
  let _::msg::_ = state.msg_list in
  readMessageType (index msg 0)

#reset-options

val cfin_helper:
  state:state_mon{ isValidState state /\ state.last_message = ClientFinished } ->
  Lemma
    (requires ( True ))
    (ensures (
	 ( ( get_discriminating_message_from_client_fin state = Finished) ==>  StateAfterClientFinLastMsg state)
	 /\ ( ( get_discriminating_message_from_client_fin state <> Finished) ==>  StateAfterClientFin state) ))
let cfin_helper state = ()

#reset-options

val snst_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerNewSessionTicket ))
    (ensures (StateAfterServerNewSessionTicket state))
let snst_helper state = ()

#reset-options

val sccs_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerCCS ))
    (ensures (StateAfterServerCCS state))
let sccs_helper state = ()

#reset-options

val sfin_helper:
  state:state_mon ->
  Lemma
    (requires (isValidState state /\ state.last_message = ServerFinished ))
    (ensures (StateAfterServerFin state))
let sfin_helper state = ()
		      
