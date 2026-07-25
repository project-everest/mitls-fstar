module TLS13.ConnectionState.ServerCertificateVerifyEvent

open FStar.List.Tot

module CL = TLS13.ConnectionLog
module M = TLS13.Messages

open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.StateMachine.Replay

noextract
val contains_sent_certificate_verify
  : events:list conn_event -> Tot prop

val lemma_contains_sent_certificate_verify_split
  (events:list conn_event)
  : Lemma
      (requires contains_sent_certificate_verify events)
      (ensures
        exists prefix cv suffix.
          events ==
            prefix @
            (ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            } :: suffix))

noextract
val server_certificate_verify_sent_event_log_invariant
  : st:connection_state -> Tot prop

val lemma_connection_state_consistent_server_certificate_verify_sent_event_log
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures server_certificate_verify_sent_event_log_invariant st)

val lemma_server_application_ready_sent_certificate_verify_event
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlApplicationData)
      (ensures contains_sent_certificate_verify st.cs_event_log)
