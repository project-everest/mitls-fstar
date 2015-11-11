module ClientKeyExchangeLemma

open FStar.Seq
open FStar.List
open Predicates
open ClientCertificateLemma
open ServerHelloDoneLemma

#reset-options

val getPreviousStateFromClientKeyExchange:
  state:state_mon{ StateAfterClientKeyExchange state } ->
  Tot (state':state_mon{ NextStateAfterClientKeyExchange state state' })
let getPreviousStateFromClientKeyExchange state =
  let last_msg::prev_log = state.msg_list in
  let last_last_msg::_ = prev_log in
  let msg_type = readMessageType (index last_last_msg 0) in
  cut ( msg_type = ServerHelloDone \/ msg_type = Certificate );
  match msg_type with
  | Certificate ->
     let old_state = { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ClientCertificate;
       client_auth = state.client_auth;
       resumption = state.resumption;
       renegotiation = state.renegotiation;
       ntick = state.ntick;
       msg_list = prev_log;
       log = build_log prev_log;
       log_length = Seq.length (build_log prev_log);
     } in
     old_state
  | ServerHelloDone ->
     let state' = { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ServerHelloDone;
       client_auth = state.client_auth;
       resumption = state.resumption;
       renegotiation = state.renegotiation;
       ntick = state.ntick;
       msg_list = prev_log;
       log = build_log prev_log;
       log_length = Seq.length (build_log prev_log);
     } in
     state'

#reset-options

val client_key_exchange_log_lemma:
  state:state_mon{ StateAfterClientKeyExchange state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\(Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let client_key_exchange_log_lemma state =
  let prev_state = getPreviousStateFromClientKeyExchange state in
  if prev_state.last_message = ServerHelloDone then server_hello_done_log_lemma prev_state
  else client_certificate_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

#reset-options

val client_key_exchange_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientKeyExchange s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterClientKeyExchange s2))
let client_key_exchange_aux_lemma s1 s2 = ()

#reset-options

val client_key_exchange_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientKeyExchange s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let client_key_exchange_lemma s1 s2 =
  client_key_exchange_aux_lemma s2 s1;
  let s1' = getPreviousStateFromClientKeyExchange s1 in
  let s2' = getPreviousStateFromClientKeyExchange s2 in
  if s2'.last_message = ServerHelloDone then
    server_hello_done_lemma s1' s2'
  else 
    client_certificate_lemma s1' s2';
  ()
