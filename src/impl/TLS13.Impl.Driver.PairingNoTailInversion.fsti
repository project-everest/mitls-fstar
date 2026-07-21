module TLS13.Impl.Driver.PairingNoTailInversion

#lang-pulse

open Pulse.Lib.Pervasives

module CL = TLS13.ConnectionLog
module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module SD = TLS13.Impl.Server.Driver

noextract
let client_no_tail_handshake_traffic_install_event
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    install.CS.install_epoch == CS.TrafficHandshake
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ClientEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake
  | _ ->
    False

(**
  Role-local, direction-insensitive counterpart of
  [client_no_tail_handshake_traffic_install_event]: [ev] installs *some*
  [ServerEndpoint]/[TrafficHandshake] key-schedule material via the role-local
  server install event, without committing to [TrafficWrite] vs [TrafficRead].
  This is deliberately weaker than naming a fixed write-then-read order: see the length-16 server
  boundary discussion in [PairingNoTailServerShape] and `PAIRING_THEOREM.md`
  for why a fixed order is not derivable from
  [SD.server_driver_application_ready] alone.
**)
noextract
let server_no_tail_handshake_traffic_install_event
  (ev:CS.conn_event)
  : prop =
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    role_install.CS.install_role == CS.ServerEndpoint /\
    role_install.CS.install_payload.CS.install_epoch == CS.TrafficHandshake
  | _ ->
    False

(**
  Key-schedule progress-rank machinery shared by the no-tail inversion proofs.

  [client_application_progress_rank] is a numeric upper bound on the number of
  events a client-role connection still needs to reach [ControlApplicationData]:
  it decreases by at most one per legal step (see
  [lemma_client_application_progress_rank_replay_lower_bound] below), so a
  replay of length [n] can only originate from a model whose rank is [<= n].
**)
noextract
let option_missing #a (o:option a) : nat =
  match o with
  | Some _ -> 0
  | None -> 1

noextract
let client_app_obligation_rank
  (keys:CS.key_schedule_state)
  : nat =
  option_missing keys.CS.ks_client_application_traffic +
  option_missing keys.CS.ks_server_application_traffic

noextract
let client_early_obligation_rank
  (keys:CS.key_schedule_state)
  : nat =
  option_missing keys.CS.ks_shared_secret +
  option_missing keys.CS.ks_client_handshake_traffic +
  option_missing keys.CS.ks_server_handshake_traffic +
  client_app_obligation_rank keys

noextract
let client_late_obligation_rank
  (keys:CS.key_schedule_state)
  : nat =
  option_missing keys.CS.ks_shared_secret +
  option_missing keys.CS.ks_client_handshake_traffic +
  client_app_obligation_rank keys

noextract
let client_final_obligation_rank
  (keys:CS.key_schedule_state)
  : nat =
  option_missing keys.CS.ks_shared_secret +
  client_app_obligation_rank keys

noextract
let client_application_progress_rank
  (model:CS.connection_model)
  : nat =
  let keys = model.CS.model_handshake.CS.hs_keys in
  match model.CS.model_control with
  | CS.ControlApplicationData ->
    client_final_obligation_rank keys
  | CS.ControlClosing
  | CS.ControlClosed ->
    client_final_obligation_rank keys
  | CS.ControlHandshaking stage ->
    (match stage with
     | CS.HsStarted ->
       10 + client_early_obligation_rank keys
     | CS.HsClientHelloSent ->
       9 + client_early_obligation_rank keys
     | CS.HsServerHelloReceived ->
       8 + client_early_obligation_rank keys
     | CS.HsEncryptedExtensionsReceived ->
       7 + client_late_obligation_rank keys
     | CS.HsCertificateReceived ->
       6 + client_late_obligation_rank keys
     | CS.HsCertificateValidated ->
       5 + client_late_obligation_rank keys
     | CS.HsCertificateVerifyReceived ->
       4 + client_late_obligation_rank keys
     | CS.HsCertificateVerifyVerified ->
       3 + client_late_obligation_rank keys
     | CS.HsServerFinishedReceived ->
       2 + client_late_obligation_rank keys
     | CS.HsServerFinishedVerified ->
       1 + client_late_obligation_rank keys
     | _ ->
       0)
  | _ ->
    0

(* Interface trimmed to definitions-only for Phase-1 clean16 removal.
   The now-false rank step-lemmas + byte-derivation val declarations were
   removed; their .fst realization is excluded (attic). Definitions above
   feed ProgressCount/SeqCountBase/System progress. *)
