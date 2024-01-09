module MiTLS.ServerCertificateRequestLemma
open MiTLS

open FStar.Seq
open FStar.List
open MiTLS.Predicates
open MiTLS.ServerCertificateLemma
open MiTLS.ServerKeyExchangeLemma

#reset-options

val server_certificate_request_log_lemma:
    state:state_mon{ StateAfterServerCertificateRequest state } ->
  Lemma
    (requires (True))
    (ensures ( ( is_Some (parse state.log) )
	       /\ (Some.v (parse state.log) = (state.msg_list))
	       /\ (forall (msg:byte_string). mem msg state.msg_list ==> isMessageLength msg (Seq.length msg) )))

#reset-options

val server_certificate_request_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires ( StateAfterServerCertificateRequest s2 /\ s1.msg_list = s2.msg_list /\ isValidState s1))
    (ensures (HaveSameStateValues s1 s2))
