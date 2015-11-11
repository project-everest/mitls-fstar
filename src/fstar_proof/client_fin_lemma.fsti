module ClientFinLemma

open FStar.Seq
open FStar.List
open Predicates
open ClientCCSLemma

#reset-options

val client_fin_log_lemma:
  state:state_mon{ StateAfterClientFin state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))

#reset-options
	
val client_fin_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientFin s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
