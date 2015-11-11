module ServerCCSLemma

open FStar.Seq
open FStar.List
open Predicates
open ServerHelloLemma
open ClientFinLemma
open ServerNewSessionTicketLemma

#reset-options

val getPreviousStateFromServerCCS:
  state:state_mon{ StateAfterServerCCS state } ->
  Tot (state':state_mon{ NextStateAfterServerCCS state state'} )
let getPreviousStateFromServerCCS state =
  let last_msg::prev_log = state.msg_list in
  let msg_type = readMessageType (index last_msg 0) in
  cut ( (msg_type = ServerHello) 
        \/ (msg_type = Finished)
        \/ (msg_type = ServerNewSessionTicket) );
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
       msg_list = state.msg_list;
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
       msg_list = state.msg_list;
       log = build_log prev_log;
       log_length = Seq.length (build_log prev_log);
     }
  | ServerNewSessionTicket ->
     { 
       pv = state.pv; 
       role = state.role; 
       kem = state.kem; 
       last_message = ServerNewSessionTicket;
       log = state.log;
       log_length = state.log_length;
       client_auth = state.client_auth;
       resumption = state.ntick;
       renegotiation = state.renegotiation;
       ntick = state.ntick;
       state_mon_initialized = state.state_mon_initialized;
       msg_list = state.msg_list;
       log = build_log prev_log;
       log_length = Seq.length (build_log prev_log);
     }

#reset-options

val server_ccs_log_lemma:
  state:state_mon{ StateAfterServerCCS state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\(Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let server_ccs_log_lemma state =
  let prev_state = getPreviousStateFromServerCCS state in
  if prev_state.last_message = ServerHello then server_hello_log_lemma prev_state
  else if prev_state.last_message = ClientFinished then client_fin_log_lemma prev_state
  else server_new_session_ticket_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

#reset-options

val server_ccs_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterServerCCS s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterServerCCS s2 
              \/ StateAfterServerNewSessionTicket s2
              \/ StateAfterClientFin s2 
              \/ StateAfterServerHello s2))
let server_ccs_aux_lemma s1 s2 = ()

#reset-options

val server_ccs_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterServerCCS s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1 ))
    (ensures (HaveSameStateValues s1 s2))
let server_ccs_lemma s1 s2 =
  server_ccs_aux_lemma s2 s1;
  let s1' = if s1.last_message = ServerCCS then getPreviousStateFromServerCCS s1 else s1 in
  let s2' = getPreviousStateFromServerCCS s2 in
  if s2'.last_message = ServerHello then server_hello_lemma s1' s2'
  else if s2'.last_message = ClientFinished then client_fin_lemma s1' s2'
  else server_new_session_ticket_lemma s1' s2';
  ()

