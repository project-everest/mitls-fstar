module ClientCCSLastMsgLemma

open FStar.Seq
open FStar.List
open Predicates
open ServerFinLemma

#reset-options

val getPreviousStateFromClientCCSLastMsg:
  state:state_mon{ StateAfterClientCCSLastMsg state } ->
  Tot (state':state_mon{ NextStateAfterClientCCSLastMsg state state'} )
let getPreviousStateFromClientCCSLastMsg state =
  let last_msg::prev_log = state.msg_list in
  { 
    pv = state.pv; 
    role = state.role; 
    kem = state.kem; 
    last_message = ServerFinished;
    client_auth = state.client_auth;
    resumption = state.resumption;
    renegotiation = state.renegotiation;
    ntick = state.ntick;
    msg_list = state.msg_list;
    log = build_log prev_log;
    log_length = Seq.length (build_log prev_log);
  }

#reset-options

val client_ccs_last_msg_log_lemma:
  state:state_mon{ StateAfterClientCCSLastMsg state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let client_ccs_last_msg_log_lemma state =
  let prev_state = getPreviousStateFromClientCCSLastMsg state in
  server_fin_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

#reset-options

val client_ccs_last_msg_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientCCSLastMsg s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterClientCCSLastMsg s2))
let client_ccs_last_msg_aux_lemma s1 s2 =  ()

#reset-options

val client_ccs_last_msg_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientCCSLastMsg s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let client_ccs_last_msg_lemma s1 s2 =
  client_ccs_last_msg_aux_lemma s2 s1;
  let s1' = if s1.last_message = ClientCCS then getPreviousStateFromClientCCSLastMsg s1 else s1 in
  let s2' = getPreviousStateFromClientCCSLastMsg s2 in
  server_fin_lemma s1' s2';
  ()
