module ClientCertificateVerifyLemma

open FStar.Seq
open FStar.List
open Predicates
open ClientKeyExchangeLemma

#reset-options

val getPreviousStateFromClientCertificateVerify:
  state:state_mon{ StateAfterClientCertificateVerify state } ->
  Tot (state':state_mon{ NextStateAfterClientCertificateVerify state state'} )
let getPreviousStateFromClientCertificateVerify state =
  let last_msg::prev_log = state.msg_list in
  let last_last_msg::_ = prev_log in
  let msg_type = readMessageType (index last_last_msg 0) in
  cut ( (msg_type = ClientKeyExchange) /\ True );
  { 
    pv = state.pv; 
    role = state.role; 
    kem = state.kem; 
    last_message = ClientKeyExchange;
    client_auth = Auth_provided;
    resumption = state.resumption;
    renegotiation = state.renegotiation;
    ntick = state.ntick;
    msg_list = prev_log;
    log = build_log prev_log;
    log_length = Seq.length (build_log prev_log);
  }

#reset-options

val client_certificate_verify_log_lemma:
  state:state_mon{ StateAfterClientCertificateVerify state } ->
  Lemma
    (requires (True))
    (ensures ( ( is_Some (parse state.log) )
		/\ (Some.v (parse state.log) = (state.msg_list))
		/\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let client_certificate_verify_log_lemma state =
  let prev_state = getPreviousStateFromClientCertificateVerify state in
  client_key_exchange_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut ( old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

#reset-options

val client_certificate_verify_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientCertificateVerify s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterClientCertificateVerify s2))
let client_certificate_verify_aux_lemma s1 s2 = ()

#reset-options

val client_certificate_verify_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientCertificateVerify s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let client_certificate_verify_lemma s1 s2 =
  client_certificate_verify_aux_lemma s2 s1;
  let s1' = getPreviousStateFromClientCertificateVerify s1 in
  let s2' = getPreviousStateFromClientCertificateVerify s2 in
  client_key_exchange_lemma s1' s2';
  ()
