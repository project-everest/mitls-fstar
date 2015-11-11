module ServerHelloLemma

open FStar.Seq
open FStar.List
open Predicates
open ClientHelloLemma

#reset-options

val getPreviousStateFromServerHello:
  state:state_mon{ StateAfterServerHello state } ->
  Tot (state':state_mon{ NextStateAfterServerHello state state'} )
let getPreviousStateFromServerHello state =
  let last_msg::prev_log = state.msg_list in
  let state' =
  { 
    pv = UndefinedPV; 
    role = state.role; 
    kem = UndefinedKEM; 
    last_message = ClientHello;
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

val server_hello_log_lemma:
  state:state_mon{ StateAfterServerHello state } ->
  Lemma
    (requires (True))
    (ensures ( ( is_Some (parse state.log) )
	       /\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let server_hello_log_lemma state =
  let prev_state = getPreviousStateFromServerHello state in
  client_hello_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

#reset-options

val server_hello_aux_lemma:
  s1:state_mon -> s2:state_mon -> 
  Lemma
    (requires (StateAfterServerHello s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterServerHello s2))
let server_hello_aux_lemma s1 s2 = ()

#reset-options

val server_hello_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterServerHello s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let server_hello_lemma s1 s2 =
  server_hello_aux_lemma s2 s1;
  let s1' = getPreviousStateFromServerHello s1 in
  let s2' = getPreviousStateFromServerHello s2 in
  client_hello_lemma s1' s2'; ()
