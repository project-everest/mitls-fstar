module ClientFinLastMsgLemma

open FStar.Seq
open FStar.List
open Predicates
open ClientCCSLastMsgLemma

#reset-options

val client_fin_last_msg_log_lemma:
  state:state_mon{ StateAfterClientFinLastMsg state } ->
  Lemma
    (requires (True))
    (ensures (  (is_Some (parse state.log) )
		/\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))

#reset-options

val client_fin_last_msg_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (StateAfterClientFinLastMsg s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
