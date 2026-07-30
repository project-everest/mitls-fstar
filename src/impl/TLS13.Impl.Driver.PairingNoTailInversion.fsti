module TLS13.Impl.Driver.PairingNoTailInversion

#lang-pulse

open Pulse.Lib.Pervasives

module CL = TLS13.ConnectionLog
module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module CS = TLS13.Spec.StateMachine
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
  option_missing keys.CS.ks_client_application_traffic

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
     9 + client_early_obligation_rank keys
     | CS.HsClientHelloSent ->
     8 + client_early_obligation_rank keys
     | CS.HsServerHelloReceived ->
     7 + client_early_obligation_rank keys
     | CS.HsEncryptedExtensionsReceived ->
     6 + client_late_obligation_rank keys
     | CS.HsCertificateReceived ->
     5 + client_late_obligation_rank keys
     | CS.HsCertificateValidated ->
     4 + client_late_obligation_rank keys
     | CS.HsCertificateVerifyReceived ->
     3 + client_late_obligation_rank keys
     | CS.HsCertificateVerifyVerified ->
     2 + client_late_obligation_rank keys
     | CS.HsServerFinishedReceived ->
       2 + client_late_obligation_rank keys
     | CS.HsServerFinishedVerified ->
       1 + client_late_obligation_rank keys
     | _ ->
       0)
  | _ ->
    0

val lemma_conn_events_raw_replay_from_failed_results_failed
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.ControlFailed? model.CS.model_control /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (ensures CS.ControlFailed? final_model.CS.model_control)

val lemma_client_hs_server_hello_received_local_event_step_none
  (model:CS.connection_model)
  (local:CS.local_event)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        (match local with
         | CS.LocalFail _ -> False
         | CS.LocalDeriveSharedSecret _ -> False
         | CS.LocalInstallTrafficKeys _ -> False
         | CS.LocalInstallTrafficKeysForRole _ -> False
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnLocalEvent local) == None)

val lemma_client_hs_server_hello_received_non_encrypted_extensions_network_step_none
  (model:CS.connection_model)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        (match msg.CL.message_value with
         | M.TlsAlert _ -> False
         | M.TlsChangeCipherSpec -> False
         | M.TlsHandshake (M.EncryptedExtensions _) ->
           msg.CL.message_direction == CL.Sent
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnNetworkEvent msg) == None)

val lemma_client_hs_server_hello_received_empty_keys_encrypted_extensions_illegal
  (model:CS.connection_model)
  (ee:GEE.encryptedExtensions)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        CS.legal_event
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          })))
      (ensures False)

(**
  One-step rank bound (exposed for the System-level length invariant): a single
  legal client-role step decreases [client_application_progress_rank] by at most
  one (unless it lands in a failed control).  This is the "at most +1 progress"
  half used to force the strict-progress System guard to advance the event-log
  length by exactly one per handshake step.
**)
val lemma_client_application_progress_rank_step
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model')
      (ensures
        CS.ControlFailed? model'.CS.model_control \/
        client_application_progress_rank model <=
        client_application_progress_rank model' + 1)

val lemma_client_application_progress_rank_replay_lower_bound
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model events raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        client_application_progress_rank final_model == 0)
      (ensures
        client_application_progress_rank model <= FStar.List.Tot.length events)

