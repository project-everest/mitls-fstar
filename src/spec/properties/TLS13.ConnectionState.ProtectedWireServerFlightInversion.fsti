module TLS13.ConnectionState.ProtectedWireServerFlightInversion

(**
  Stage 3 of the counting-free server-flight derivation: the counting-free
  BRIDGE that produces the four server-flight protected-handshake projection
  pairs (EncryptedExtensions / Certificate / CertificateVerify / Finished)
  from the flagship JOINT byte facts available at the front door
  [TLS13.System.lemma_pw_establish].

  Re-based (Option C) off plain [CS.connection_state] endpoints instead of a
  [TLS13.System.tls_system_state] wrapper, so the module no longer imports
  [TLS13.System] (breaking the module dependency cycle that would otherwise
  arise when [TLS13.System.lemma_pw_establish] calls this bridge).  The
  hypotheses below are the System-free restatements of the corresponding
  [TLS13.System] predicates (client/server byte reachability, byte pairing at
  TlsQuiet collapsed to raw-log equality, driver application-readiness,
  hello key-share agreement), a SUBSET of the facts [lemma_pw_establish]
  provides.

  The tails ([server_rest]/[client_rest]) are kept ABSTRACT / existential:
  they are consumed by the separate client-finished milestone.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module SMReplay = TLS13.Spec.StateMachine.Replay
module CD = TLS13.Impl.Client.Driver
module SD = TLS13.Impl.Server.Driver
module WStep = TLS13.System.WireStep
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.ConnectionState.ProtectedWireBase

(* ------------------------------------------------------------------ *)
(* The allowed flagship facts (System-free restatements; a subset of  *)
(* [lemma_pw_establish]).                                             *)
(* ------------------------------------------------------------------ *)

(** The four cleartext hellos are recorded on both endpoints. **)
let four_hellos_present (client server : CS.connection_state) : prop =
  Some? client.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
  Some? server.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
  Some? client.CS.cs_model.CS.model_handshake.CS.hs_server_hello /\
  Some? server.CS.cs_model.CS.model_handshake.CS.hs_server_hello

(** The endpoint roles. **)
let roles_ok (client server : CS.connection_state) : prop =
  client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint

(** System-free restatement of [TLS13.System.hello_key_shares_ok]. **)
let hks_ok (client server : CS.connection_state) : prop =
  (Some? client.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
   Some? server.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
   Some? client.CS.cs_model.CS.model_handshake.CS.hs_server_hello /\
   Some? server.CS.cs_model.CS.model_handshake.CS.hs_server_hello) ==>
    WFL.paired_cleartext_hello_key_shares client server

(** The complete allowed-hypothesis bundle for the bridge — the System-free
    restatement of the [lemma_pw_establish] subset used here.  Introduces NO
    hypothesis outside that set (in particular NO `ch_wire_equiv`,
    `sh_wire_equiv`, `hello_coupling`, `tls_no_rekeying`,
    `supported_client_config_wire_profile`, and NO event-log length count). **)
let server_flight_bridge_inputs (client server : CS.connection_state) : prop =
  WStep.client_reachable (CS.initial client.CS.cs_model.CS.model_config) client /\
  WStep.server_reachable (CS.initial server.CS.cs_model.CS.model_config) server /\
  Seq.equal client.CS.cs_wire_log.CL.raw_sent server.CS.cs_wire_log.CL.raw_received /\
  Seq.equal server.CS.cs_wire_log.CL.raw_sent client.CS.cs_wire_log.CL.raw_received /\
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  hks_ok client server /\
  four_hellos_present client server /\
  roles_ok client server

(* ------------------------------------------------------------------ *)
(* The bridge's conclusion, in FLAGSHIP-COMPOSABLE shape.              *)
(* The four SERVER protected-handshake projection pairs, each PINNED   *)
(* to the ACTUAL model handshake fields on both endpoints (mirroring   *)
(* ProtectedWireBase.fsti:428-448): sent projects the SERVER's field,  *)
(* received projects the CLIENT's field.  Requires all four fields     *)
(* present (Some) on both endpoints, else False.                       *)
(* ------------------------------------------------------------------ *)
let server_flight_pairs_conclusion (client server : CS.connection_state) : prop =
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match
    client_hs.CS.hs_encrypted_extensions, server_hs.CS.hs_encrypted_extensions,
    client_hs.CS.hs_certificate, server_hs.CS.hs_certificate,
    client_hs.CS.hs_certificate_verify, server_hs.CS.hs_certificate_verify,
    client_hs.CS.hs_server_finished, server_hs.CS.hs_server_finished
  with
  | Some client_ee, Some server_ee_msg,
    Some client_cert, Some server_cert_msg,
    Some client_cv, Some server_cv_msg,
    Some client_sf, Some server_sf ->
    (exists
      (server_ee:protected_message_replay)
      (server_cert:protected_message_replay)
      (server_cv:protected_message_replay)
      (server_finished:protected_message_replay).
      protected_handshake_event_projection_pair
        server_ee
        (M.EncryptedExtensions server_ee_msg)
        (M.EncryptedExtensions client_ee) /\
      protected_handshake_event_projection_pair
        server_cert
        (M.Certificate server_cert_msg)
        (M.Certificate client_cert) /\
      protected_handshake_event_projection_pair
        server_cv
        (M.CertificateVerify server_cv_msg)
        (M.CertificateVerify client_cv) /\
      protected_handshake_event_projection_pair
        server_finished
        (M.Finished server_sf)
        (M.Finished client_sf))
  | _, _, _, _, _, _, _, _ ->
    False

val lemma_server_flight_pairs_from_replays_and_pairing
  (client server : CS.connection_state)
  : Lemma
      (requires server_flight_bridge_inputs client server)
      (ensures server_flight_pairs_conclusion client server)
