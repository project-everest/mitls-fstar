module ServerFinLemma

open FStar.Seq
open FStar.List
open Predicates
open ServerCCSLemma

#reset-options

val getPreviousStateFromServerFin:
  state:state_mon{ StateAfterServerFin state } ->
  Tot (state':state_mon{ NextStateAfterServerFin state state'} )
let getPreviousStateFromServerFin state =
  let last_msg::prev_log = state.msg_list in
  { 
    pv = state.pv; 
    role = state.role; 
    kem = state.kem; 
    last_message = ServerCCS;
    client_auth = state.client_auth;
    resumption = state.resumption;
    renegotiation = state.renegotiation;
    ntick = state.ntick;
    msg_list = prev_log;
    log = build_log prev_log;
    log_length = Seq.length (build_log prev_log);
  }

#reset-options

val server_fin_log_lemma:
  state:state_mon{ StateAfterServerFin state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let server_fin_log_lemma state =
  let prev_state = getPreviousStateFromServerFin state in
  server_ccs_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()


#reset-options
	
val server_fin_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires ( StateAfterServerFin s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2 ))
    (ensures (StateAfterServerFin s2))
let server_fin_aux_lemma s1 s2 = ()
#reset-options
	
val server_fin_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterServerFin s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let server_fin_lemma s1 s2 =
  server_fin_aux_lemma s2 s1;
  let s1' = getPreviousStateFromServerFin s1 in
  let s2' = getPreviousStateFromServerFin s2 in
  server_ccs_lemma s1' s2';
  ()
