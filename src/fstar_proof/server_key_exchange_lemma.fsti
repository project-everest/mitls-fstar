module ServerKeyExchangeLemma

open FStar.Seq
open FStar.List
open Predicates
open ServerCertificateLemma
open ServerHelloLemma

#reset-options

val server_key_exchange_log_lemma:
  state:state_mon{ StateAfterServerKeyExchange state } ->
  Lemma
    (requires (True))
    (ensures (  ( is_Some (parse state.log) )
		/\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))

#reset-options

val server_key_exchange_lemma:
	 s1:state_mon -> s2:state_mon ->
	 Lemma
	   (requires ( StateAfterServerKeyExchange s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
	   (ensures (HaveSameStateValues s1 s2))
