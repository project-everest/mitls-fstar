module ServerNewSessionTicketLemma

open FStar.Seq
open FStar.List
open Predicates
open ServerHelloLemma
open ClientFinLemma

#reset-options

val getPreviousStateFromServerNewSessionTicket:
  state:state_mon{ StateAfterServerNewSessionTicket state } ->
  Tot (state':state_mon{ NextStateAfterServerNewSessionTicket state state'} )
let getPreviousStateFromServerNewSessionTicket state =
  let last_msg::prev_log = state.msg_list in
  let last_last_msg::_ = prev_log in
  let msg_type = readMessageType (index last_last_msg 0) in
  cut ( (msg_type = ServerHello) \/ (msg_type = Finished) );
  match msg_type with
  | ServerHello ->
     { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ServerHello;
       client_auth = state.client_auth;
       resumption = Undefined;
       renegotiation = state.renegotiation;
       ntick = Undefined;
       msg_list = prev_log;
       log = build_log prev_log;
       log_length = Seq.length (build_log prev_log);
     }
  | Finished ->
     { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ClientFinished;
       client_auth = state.client_auth;
       resumption = No;
       renegotiation = state.renegotiation;
       ntick = Undefined;
       msg_list = prev_log;
       log = build_log prev_log;
       log_length = Seq.length (build_log prev_log);
     }

#reset-options

val server_new_session_ticket_log_lemma:
  state:state_mon{ StateAfterServerNewSessionTicket state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\(Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let server_new_session_ticket_log_lemma state =
  let prev_state = getPreviousStateFromServerNewSessionTicket state in
  if prev_state.last_message = ClientFinished then client_fin_log_lemma prev_state
  else server_hello_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

#reset-options

val server_new_session_ticket_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterServerNewSessionTicket s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterServerNewSessionTicket s2))
let server_new_session_ticket_aux_lemma s1 s2 = ()

#reset-options

val server_new_session_ticket_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterServerNewSessionTicket s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let server_new_session_ticket_lemma s1 s2 =
  server_new_session_ticket_aux_lemma s2 s1;
  let s1' = getPreviousStateFromServerNewSessionTicket s1 in
  let s2' = getPreviousStateFromServerNewSessionTicket s2 in
  if s2'.last_message = ServerHello then server_hello_lemma s1' s2'
  else client_fin_lemma s1' s2';
  ()
