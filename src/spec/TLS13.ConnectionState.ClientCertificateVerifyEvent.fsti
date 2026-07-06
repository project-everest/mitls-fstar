module TLS13.ConnectionState.ClientCertificateVerifyEvent

module CL = TLS13.ConnectionLog
module CVR = TLS13.ConnectionState.ClientCertificateVerifyReachability
module M = TLS13.Messages

open TLS13.Spec.ConnectionState

noextract
val contains_received_certificate_verify
  : events:list conn_event -> Tot prop

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
