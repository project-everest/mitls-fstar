module InjectivityLemma

open FStar.List
open FStar.Seq
open Predicates
open InitialStateLemma
open ClientHelloLemma
open ServerHelloLemma
open ServerCertificateLemma
open ServerKeyExchangeLemma
open ServerCertificateRequestLemma
open ServerHelloDoneLemma
open ClientCertificateLemma
open ClientKeyExchangeLemma
open ClientCertificateVerifyLemma
open ClientCCSLemma
open ClientFinLemma
open ServerNewSessionTicketLemma
open ServerCCSLemma
open ServerFinLemma
open ClientCCSLastMsgLemma
open ClientFinLastMsgLemma
open HelperLemmas

#reset-options

(* the parse function is injective on a valid state log *)	 
val valid_log_implies_valid_msg_list:
  s:state_mon ->
  Lemma
    (requires (isValidState s))
    (ensures ( (is_Some (parse s.log))
	       /\ (Some.v (parse s.log) = s.msg_list)
	       /\ (forall (msg:byte_string). mem msg s.msg_list ==> isMessageLength msg (Seq.length msg)) ))
let valid_log_implies_valid_msg_list s =
  match s.last_message with
  | UndefinedMessageType -> initial_state_log_lemma s
  | ClientHello -> client_hello_log_lemma s
  | ServerHello -> server_hello_log_lemma s
  | ServerCertificate -> server_certificate_log_lemma s
  | ServerKeyExchange -> server_key_exchange_log_lemma s
  | ServerCertificateRequest -> server_certificate_request_log_lemma s
  | ServerHelloDone -> server_hello_done_log_lemma s
  | ClientCertificate -> client_certificate_log_lemma s
  | ClientKeyExchange -> client_key_exchange_log_lemma s
  | ClientCertificateVerify -> client_certificate_verify_log_lemma s
  | ServerNewSessionTicket -> server_new_session_ticket_log_lemma s
  | ServerCCS -> server_ccs_log_lemma s
  | ServerFinished -> server_fin_log_lemma s
  | ClientCCS -> 
     let last_msg_type = get_discriminating_message_from_client_ccs s in
     if last_msg_type = Finished then client_ccs_last_msg_log_lemma s
     else client_ccs_log_lemma s
  | ClientFinished -> 
     let last_msg_type = get_discriminating_message_from_client_fin s in
     if last_msg_type = Finished then client_fin_last_msg_log_lemma s
     else client_fin_log_lemma s

#reset-options

(* Because of the preceding lemma, two valid states having the same log have the same msg list *)
val same_log_implies_same_msg_list:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (isValidState s1 /\ isValidState s2 /\ s1.log = s2.log))
    (ensures (s1.msg_list = s2.msg_list))
let same_log_implies_same_msg_list s1 s2 = 
  valid_log_implies_valid_msg_list s1;
  valid_log_implies_valid_msg_list s2
      
#reset-options

(* If two states have the same message list, then the have the same negociated values *)
val injectivity_lemma_aux:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (isValidState s1 /\ isValidState s2 /\ s1.msg_list = s2.msg_list))
    (ensures (HaveSameStateValues s1 s2))
let injectivity_lemma_aux s1 s2 =
  match s2.last_message with
  | UndefinedMessageType ->  
     initial_state_helper s2;
     initial_state_lemma s1 s2
  | ClientHello -> 
     client_hello_helper s2;
     client_hello_lemma s1 s2
  | ServerHello -> 
     server_hello_helper s2;
     server_hello_lemma s1 s2
  | ServerCertificate -> 
     server_certificate_helper s2;
     server_certificate_lemma s1 s2
  | ServerKeyExchange -> 
     ske_helper s2;
     server_key_exchange_lemma s1 s2
  | ServerCertificateRequest -> 
     scr_helper s2;
     server_certificate_request_lemma s1 s2
  | ServerHelloDone -> 
     shd_helper s2;
     server_hello_done_lemma s1 s2
  | ClientCertificate -> 
     cc_helper s2;
     client_certificate_lemma s1 s2
  | ClientKeyExchange -> 
     cke_helper s2;
     client_key_exchange_lemma s1 s2
  | ClientCertificateVerify -> 
     ccv_helper s2;
     client_certificate_verify_lemma s1 s2
  | ServerNewSessionTicket -> 
     snst_helper s2;
     server_new_session_ticket_lemma s1 s2
  | ServerCCS -> 
     sccs_helper s2;
     server_ccs_lemma s1 s2
  | ServerFinished -> 
     sfin_helper s2;
     server_fin_lemma s1 s2
  | ClientCCS -> 
     let last_msg_type = get_discriminating_message_from_client_ccs s2 in
     if last_msg_type = Finished then
       begin
	 cccs_helper s2;
	 client_ccs_last_msg_lemma s1 s2
       end
     else 
       begin
	 cccs_helper s2;
	 client_ccs_lemma s1 s2
       end
  | ClientFinished -> 
     let last_msg_type = get_discriminating_message_from_client_fin s2 in
     if last_msg_type = Finished then
       begin
	 cccs_helper s2;
	 client_fin_last_msg_lemma s1 s2
       end
     else 
       begin
	 cccs_helper s2;
	 client_fin_lemma s1 s2
       end

#reset-options

(* Injectivity lemma : two states having the same logs have the same negociated values *)
val injectivity_lemma:
  s1:state_mon -> s2:state_mon ->
  Lemma
    (requires (isValidState s1 /\ isValidState s2 /\ s1.log = s2.log))
    (ensures (HaveSameStateValues s1 s2))  
let injectivity_lemma s1 s2 =
  same_log_implies_same_msg_list s1 s2;
  injectivity_lemma_aux s1 s2
