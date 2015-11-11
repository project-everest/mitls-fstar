module ClientHelloLemma

open FStar.List
open FStar.Seq
open Predicates
open InitialStateLemma

#reset-options

let initialState = 
  { 
    pv = UndefinedPV; 
    role = UndefinedRole; 
    kem = UndefinedKEM; 
    last_message = UndefinedMessageType;
    client_auth = UndefinedAuth;
    resumption = Undefined;
    renegotiation = Undefined;
    ntick = Undefined;
    msg_list = [];
    log = build_log [];
    log_length = 0;
  }

val getPreviousStateFromClientHello:
  state:state_mon{ StateAfterClientHello state } ->
  Tot (state':state_mon{ NextStateAfterClientHello state state'})
let getPreviousStateFromClientHello state =
  initialState

#reset-options

val client_hello_log_lemma:
  state:state_mon{ StateAfterClientHello state } ->
  Lemma
    (requires (True))
    (ensures ( (is_Some (parse state.log))
	       /\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))
let client_hello_log_lemma state =
  let prev_state = getPreviousStateFromClientHello state in
  initial_state_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) = prev_state.msg_list /\ True );
  let msg::old = state.msg_list in
  cut (old = prev_state.msg_list /\ True);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) msg) /\ True );
  intermediate_lemma_1 prev_state.log msg;
  cut ( Some.v (parse state.log) = state.msg_list /\ True );
  ()

#reset-options

val client_hello_aux_lemma:
  s1:state_mon -> s2:state_mon -> 
  Lemma
    (requires (StateAfterClientHello s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterClientHello s2))
let client_hello_aux_lemma s1 s2 = ()

#reset-options

val client_hello_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientHello s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
let client_hello_lemma s1 s2 =
  client_hello_aux_lemma s2 s1;
  let s1' = getPreviousStateFromClientHello s1 in
  let s2' = getPreviousStateFromClientHello s2 in
  initial_state_lemma s1' s2'; ()
 
