module InitialStateLemma

open FStar.Seq
open FStar.List
open Predicates

val initial_state_log_lemma:
  state:state_mon{ StateAfterInitialState state } ->
  Lemma
    (requires (True))
    (ensures ( (is_Some (parse state.log))
	       /\ (Some.v (parse state.log) = (state.msg_list) )
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))

#reset-options

val initial_state_lemma:
  s1:state_mon{ StateAfterInitialState s1 } -> s2:state_mon{ StateAfterInitialState s2 /\ s1.msg_list = s2.msg_list } ->
  Lemma
    (requires (True))
    (ensures (HaveSameStateValues s1 s2))
