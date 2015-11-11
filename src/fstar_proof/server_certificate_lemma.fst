module ServerCertificateLemma

open FStar.Seq
open FStar.List
open Predicates
open ServerHelloLemma

val getPreviousStateFromServerCertificate:
  state:state_mon{ StateAfterServerCertificate state } ->
  Tot (state':state_mon{ NextStateAfterServerCertificate state state' })
  
let getPreviousStateFromServerCertificate 
  (state:state_mon{ StateAfterServerCertificate state }) =
  let last_msg::prev_log = state.msg_list in
  let state' =
  { 
    pv = state.pv; 
    role = state.role; 
    kem = state.kem; 
    last_message = ServerHello;
    client_auth = state.client_auth;
    resumption = Undefined;
    renegotiation = state.renegotiation;
    ntick = state.ntick;
    msg_list = prev_log;
    log = build_log prev_log;
    log_length = Seq.length (build_log prev_log);
  }
 in state'


#reset-options


val server_certificate_log_lemma:
  state:state_mon{ StateAfterServerCertificate state } ->
  Lemma
    (requires True)
    (ensures ((is_Some (parse state.log) )
              /\ (Some.v (parse state.log) = state.msg_list)
	      /\ (forall (msg:byte_string).
                 mem msg state.msg_list ==> isMessageLength msg (Seq.length msg))))


let server_certificate_log_lemma state =
  let prev_state = getPreviousStateFromServerCertificate state in
  server_hello_log_lemma prev_state;
  cut ( Some.v (parse prev_state.log) == prev_state.msg_list );
  let last_msg::prev_log = state.msg_list in
  cut (prev_log == prev_state.msg_list);
  cut ( Seq.Eq state.log (Seq.append (prev_state.log) last_msg ));
  intermediate_lemma_1 prev_state.log last_msg;
  cut ( Some.v (parse state.log) == state.msg_list );
  ()

#reset-options

val server_certificate_aux_lemma:
  s1:state_mon -> s2:state_mon -> 
  Lemma
    (requires (StateAfterServerCertificate s1 /\ s1.msg_list = s2.msg_list /\ isValidState s2))
    (ensures (StateAfterServerCertificate s2))
let server_certificate_aux_lemma s1 s2 = ()

#reset-options

val server_certificate_lemma:
	 s1:state_mon -> s2:state_mon ->
	 Lemma
	   (requires StateAfterServerCertificate s2 /\ s1.msg_list = s2.msg_list /\ (isValidState s1))
	   (ensures (HaveSameStateValues s1 s2))
let server_certificate_lemma s1 s2 =
  server_certificate_aux_lemma s2 s1;
  let s1' = getPreviousStateFromServerCertificate s1 in
  let s2' = getPreviousStateFromServerCertificate s2 in
  server_hello_lemma s1' s2'; ()
