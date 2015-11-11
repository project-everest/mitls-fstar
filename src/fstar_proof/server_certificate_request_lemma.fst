module ServerCertificateRequestLemma

open FStar.Seq
open FStar.List
open Predicates
open ServerCertificateLemma
open ServerKeyExchangeLemma

#reset-options

val getPreviousStateFromServerCertificateRequest:
  state:state_mon{ StateAfterServerCertificateRequest state } ->
  Tot (state':state_mon{ NextStateAfterServerCertificateRequest state state'} )
let getPreviousStateFromServerCertificateRequest state =
  let last_msg::prev_log = state.msg_list in
  let last_last_msg::_ = prev_log in
  cut ( readMessageType (index last_last_msg 0) = Certificate 
        \/ readMessageType (index last_last_msg 0) = ServerKeyExchange );
  match readMessageType (index last_last_msg 0) with
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

#reset-options

val server_certificate_request_log_lemma:
    state:state_mon{ StateAfterServerCertificateRequest state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\ ( Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let server_certificate_request_log_lemma state =
  let prev_state = getPreviousStateFromServerCertificateRequest state in
  if prev_state.last_message = ServerCertificate then server_certificate_log_lemma prev_state
  else server_key_exchange_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

#reset-options

val server_certificate_request_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires ( StateAfterServerCertificateRequest s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterServerCertificateRequest s2))
let server_certificate_request_aux_lemma s1 s2 = ()

#reset-options

val server_certificate_request_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires ( StateAfterServerCertificateRequest s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let server_certificate_request_lemma s1 s2 =
  server_certificate_request_aux_lemma s2 s1;
  let s1' = getPreviousStateFromServerCertificateRequest s1 in
  let s2' = getPreviousStateFromServerCertificateRequest s2 in
  if s2'.last_message = ServerKeyExchange then
    server_key_exchange_lemma s2' s1'
  else 
    server_certificate_lemma s2' s1';
  ()
