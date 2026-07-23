module TLS13.Symbolic.Labels

(*
 * Confidentiality labels intended for TLS credentials and endpoint state.
 *
 * DY labels identify the principal/state pair whose corruption permits a term
 * to become public.  These constructors provide the intended labels; theorem
 * callers must still prove that their symbolic terms actually carry them.
 * In particular, Secrecy.ephemeral_pair_has_labels accepts supplied labels and
 * does not itself force use of ephemeral_key_label.
 *)

module DY = DY.Core
module Terms = TLS13.Symbolic.Terms

(* Label a server's long-lived signing credential by its owning state cell. *)
let server_signing_key_label
  (server:DY.principal)
  (credential_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label server credential_state_id

(* Label one endpoint session's ephemeral private-key state. *)
let ephemeral_key_label
  (session:Terms.endpoint_session)
  (ephemeral_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label
    session.session_principal
    ephemeral_state_id

(* Label the mutable state that owns an in-progress handshake's secrets. *)
let handshake_state_label
  (session:Terms.endpoint_session)
  (handshake_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label
    session.session_principal
    handshake_state_id

(* Label the post-handshake application state that owns application secrets. *)
let application_state_label
  (session:Terms.endpoint_session)
  (application_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label
    session.session_principal
    application_state_id

(* Give honest application input the label of its owning application state. *)
let honest_application_data_label
  (session:Terms.endpoint_session)
  (application_state_id:DY.state_id)
  : DY.label =
  application_state_label session application_state_id

(* Label explicitly stored traffic-key state for a particular endpoint. *)
let traffic_key_label
  (session:Terms.endpoint_session)
  (traffic_key_state_id:DY.state_id)
  : DY.label =
  DY.principal_state_label
    session.session_principal
    traffic_key_state_id

(*
 * Join the two ephemeral labels that protect a DH shared secret.
 *
 * Under DY label semantics, disclosure is permitted when either contributing
 * endpoint state is corrupt.
 *)
let shared_secret_label
  (client_ephemeral server_ephemeral:DY.label)
  : DY.label =
  DY.join client_ephemeral server_ephemeral
