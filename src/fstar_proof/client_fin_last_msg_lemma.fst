module ClientFinLastMsgLemma

open FStar.Seq
open FStar.List
open Predicates
open ClientCCSLastMsgLemma

#reset-options

val getPreviousStateFromClientFinLastMsg:
  state:state_mon{ StateAfterClientFinLastMsg state } ->
  Tot (state':state_mon{ NextStateAfterClientFinLastMsg state state'} )
let getPreviousStateFromClientFinLastMsg state =
  let last_msg::prev_log = state.msg_list in
  { 
    pv = state.pv; 
    role = state.role; 
    kem = state.kem; 
    last_message = ClientCCS;
    client_auth = state.client_auth;
    resumption = state.resumption;
    renegotiation = state.renegotiation;
    ntick = state.ntick;
    msg_list = prev_log;
    log = build_log prev_log;
    log_length = Seq.length (build_log prev_log);
  }

#reset-options

val client_fin_last_msg_log_lemma:
  state:state_mon{ StateAfterClientFinLastMsg state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let client_fin_last_msg_log_lemma state =
  let prev_state = getPreviousStateFromClientFinLastMsg state in
  client_ccs_last_msg_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

#reset-options

val client_fin_last_msg_aux_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientFinLastMsg s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterClientFinLastMsg s2))
let client_fin_last_msg_aux_lemma s1 s2 =  ()

#reset-options

val client_fin_last_msg_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientFinLastMsg s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let client_fin_last_msg_lemma s1 s2 =
  client_fin_last_msg_aux_lemma s2 s1;
  let s1' = getPreviousStateFromClientFinLastMsg s1 in
  let s2' = getPreviousStateFromClientFinLastMsg s2 in
  client_ccs_last_msg_lemma s1' s2';
  ()
