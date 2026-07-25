module TLS13.ConnectionState.ClientCertificateVerifyEvent

module CL = TLS13.ConnectionLog
module CVR = TLS13.ConnectionState.ClientCertificateVerifyReachability
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
val contains_received_certificate_verify
  : events:list conn_event -> Tot prop

val lemma_contains_received_certificate_verify_split
  (events:list conn_event)
  : Lemma
      (requires contains_received_certificate_verify events)
      (ensures
        exists prefix cv suffix.
          events ==
            prefix @
            (ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            } :: suffix))

noextract
val client_certificate_verify_event_log_invariant
  : st:connection_state -> Tot prop

val lemma_connection_state_consistent_client_certificate_verify_event_log
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures client_certificate_verify_event_log_invariant st)

val lemma_client_application_ready_received_certificate_verify_event
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        st.cs_model.model_control == ControlApplicationData)
      (ensures contains_received_certificate_verify st.cs_event_log)
