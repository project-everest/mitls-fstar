module TLS13.Symbolic.Labels

module DY = DY.Core
module Terms = TLS13.Symbolic.Terms

let server_signing_key_label
  (server:DY.principal)
  (credential_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label server credential_state_id

let ephemeral_key_label
  (session:Terms.endpoint_session)
  (ephemeral_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label
    session.session_principal
    ephemeral_state_id

let handshake_state_label
  (session:Terms.endpoint_session)
  (handshake_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label
    session.session_principal
    handshake_state_id

let application_state_label
  (session:Terms.endpoint_session)
  (application_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label
    session.session_principal
    application_state_id

let honest_application_data_label
  (session:Terms.endpoint_session)
  (application_state_id:DY.state_id)
  : DY.label =
  application_state_label session application_state_id

let traffic_key_label
  (session:Terms.endpoint_session)
  (traffic_key_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label
    session.session_principal
    traffic_key_state_id

let shared_secret_label
  (client_ephemeral server_ephemeral:DY.label)
  : DY.label =
  DY.join client_ephemeral server_ephemeral
