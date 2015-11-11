module ClientCCSLemma

open FStar.Seq
open FStar.List
open Predicates
open ClientCertificateVerifyLemma
open ClientKeyExchangeLemma
open ClientCertificateLemma

#reset-options

val getPreviousStateFromClientCCS:
  state:state_mon{ StateAfterClientCCS state } ->
  Tot (state':state_mon{ NextStateAfterClientCCS state state'} )
let getPreviousStateFromClientCCS state =
  let last_msg::prev_log = state.msg_list in
  let msg_type = readMessageType (index last_msg 0) in
  cut ( msg_type = ClientCertificateVerify
        \/ msg_type = ClientKeyExchange
        \/ msg_type = ClientCertificate );
  match msg_type with
  | ClientCertificateVerify ->
     { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ClientCertificateVerify;
       client_auth = state.client_auth;
       resumption = Undefined;
       renegotiation = state.renegotiation;
       ntick = state.ntick;
       msg_list = state.msg_list;
       log = state.log;
       log_length = state.log_length;
     }
  | ClientKeyExchange ->
     { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ClientKeyExchange;
       client_auth = state.client_auth;
       resumption = Undefined;
       renegotiation = state.renegotiation;
       ntick = state.ntick;
       msg_list = state.msg_list;
       log = state.log;
       log_length = state.log_length;
     }
  | ClientCertificate ->
     { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ClientCertificate;
       client_auth = state.client_auth;
       resumption = Undefined;
       renegotiation = state.renegotiation;
       ntick = state.ntick;
       msg_list = state.msg_list;
       log = state.log;
       log_length = state.log_length;
     }

#reset-options

val client_ccs_log_lemma:
    state:state_mon{ StateAfterClientCCS state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\(Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let client_ccs_log_lemma state =
  let prev_state = getPreviousStateFromClientCCS state in
  if prev_state.last_message = ClientCertificate then client_certificate_log_lemma prev_state
else if prev_state.last_message = ClientKeyExchange then client_key_exchange_log_lemma prev_state
else client_certificate_verify_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

val client_ccs_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientCCS s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterClientCCS s2 
              \/ StateAfterClientCertificate s2
              \/ StateAfterClientKeyExchange s2
              \/ StateAfterClientCertificateVerify s2))
let client_ccs_aux_lemma s1 s2 = ()

#reset-options

val client_ccs_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires ( StateAfterClientCCS s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let client_ccs_lemma s1 s2 =
  client_ccs_aux_lemma s2 s1;
  let s1' = if s1.last_message = ClientCCS then getPreviousStateFromClientCCS s1 else s1 in
  let s2' = getPreviousStateFromClientCCS s2 in
  if s2'.last_message = ClientCertificateVerify then client_certificate_verify_lemma s1' s2'
  else if s2'.last_message = ClientKeyExchange then client_key_exchange_lemma s1' s2'
  else client_certificate_lemma s1' s2';
  ()
