module ServerHelloDoneLemma

open FStar.Seq
open FStar.List
open Predicates
open ServerKeyExchangeLemma
open ServerCertificateLemma
open ServerCertificateRequestLemma

#reset-options

val server_hello_done_log_lemma:
  state:state_mon{ StateAfterServerHelloDone state } ->
  Lemma
    (requires (True))
    (ensures (  ( is_Some (parse state.log) )
		/\ (Some.v (parse state.log) = (state.msg_list))
		/\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))

#reset-options

val server_hello_done_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (isValidState s1 /\ StateAfterServerHelloDone s2 /\ s1.msg_list = s2.msg_list))
    (ensures (HaveSameStateValues s1 s2))
