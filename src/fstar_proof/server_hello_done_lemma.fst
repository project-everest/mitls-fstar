module ServerHelloDoneLemma

open FStar.Seq
open FStar.List
open Predicates
open ServerKeyExchangeLemma
open ServerCertificateLemma
open ServerCertificateRequestLemma

#reset-options

val getPreviousStateFromServerHelloDone:
  state:state_mon{ StateAfterServerHelloDone state } ->
  Tot (state':state_mon{ NextStateAfterServerHelloDone state state'} )
let getPreviousStateFromServerHelloDone state =
  let last_msg::prev_log = state.msg_list in
  let last_last_msg::_ = prev_log in
  let msg_type = readMessageType (index last_last_msg 0) in
  cut ( (msg_type = Certificate )
        \/ (msg_type = ServerKeyExchange)
        \/ (msg_type = ServerCertificateRequest) );
  match msg_type with
  | Certificate ->
     { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ServerCertificate;
       client_auth = UndefinedAuth;
       resumption = state.resumption;
       renegotiation = state.renegotiation;
       ntick = state.ntick;
       msg_list = prev_log;
       log = build_log prev_log;
       log_length = Seq.length (build_log prev_log);
     }
  | ServerKeyExchange ->
     { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ServerKeyExchange;
       client_auth = UndefinedAuth;
       resumption = state.resumption;
       renegotiation = state.renegotiation;
       ntick = state.ntick;
       msg_list = prev_log;
       log = build_log prev_log;
       log_length = Seq.length (build_log prev_log);
     }
  | ServerCertificateRequest ->
     { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ServerCertificateRequest;
       client_auth = Auth_requested;
       resumption = state.resumption;
       renegotiation = state.renegotiation;
       ntick = state.ntick;
       msg_list = prev_log;
       log = build_log prev_log;
       log_length = Seq.length (build_log prev_log);
     }

#reset-options

val server_hello_done_log_lemma:
  state:state_mon{ StateAfterServerHelloDone state } ->
  Lemma
    (requires (True))
    (ensures (  ( is_Some (parse state.log) )
		/\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let server_hello_done_log_lemma state =
  let prev_state = getPreviousStateFromServerHelloDone state in
  if prev_state.last_message = ServerCertificate then server_certificate_log_lemma prev_state
  else if prev_state.last_message = ServerKeyExchange then server_key_exchange_log_lemma prev_state
  else server_certificate_request_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()


val server_hello_done_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterServerHelloDone s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterServerHelloDone s2))
let server_hello_done_aux_lemma s1 s2 = ()

#reset-options

val server_hello_done_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (isValidState s1 /\ StateAfterServerHelloDone s2 /\ s1.msg_list = s2.msg_list))
    (ensures (HaveSameStateValues s1 s2))
let server_hello_done_lemma s1 s2 =
  server_hello_done_aux_lemma s2 s1;
  let s1' = getPreviousStateFromServerHelloDone s1 in
  let s2' = getPreviousStateFromServerHelloDone s2 in
  if s2'.last_message = ServerKeyExchange then
    server_key_exchange_lemma s1' s2'
  else if s2'.last_message = ServerCertificate then
    server_certificate_lemma s1' s2'
  else 
    server_certificate_request_lemma s1' s2';
  ()
