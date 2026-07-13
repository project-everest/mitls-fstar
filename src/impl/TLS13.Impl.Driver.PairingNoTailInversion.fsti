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

val lemma_conn_events_raw_replay_from_failed_results_failed
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.ControlFailed? model.CS.model_control /\
        CS.conn_events_raw_replay
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

val lemma_client_application_progress_rank_replay_lower_bound
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        CS.conn_events_raw_replay model events raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        client_application_progress_rank final_model == 0)
      (ensures
        client_application_progress_rank model <= FStar.List.Tot.length events)

val lemma_client_post_derive_next_event_handshake_traffic_install
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        CS.conn_events_raw_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        client_application_progress_rank final_model == 0 /\
        FStar.List.Tot.length rest == 11)
      (ensures client_no_tail_handshake_traffic_install_event ev)

val lemma_client_no_tail_log_spine
  (client:CS.connection_state)
  : Lemma
      (requires FStar.List.Tot.length client.CS.cs_event_log == 15)
      (ensures
        exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
          client.CS.cs_event_log ==
            [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])

val lemma_server_no_tail_log_spine
  (server:CS.connection_state)
  : Lemma
      (requires FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
          server.CS.cs_event_log ==
            [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])

val lemma_client_no_tail_log_spine16
  (client:CS.connection_state)
  : Lemma
      (requires FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
          client.CS.cs_event_log ==
            [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])

(**
  Server-side analogue of [lemma_client_no_tail_log_spine16], at the corrected
  no-tail server boundary length of 16 (not 15): a satisfiable server
  no-tail trace must have room for the [ServerEndpoint]/[TrafficHandshake]
  read-key install (needed to legally receive the protected [ClientFinished]
  in [HsServerFinishedSent]) in addition to the 15-event shape used by the
  stale [lemma_server_no_tail_log_spine].  This lemma only fixes the list
  spine (existence of 16 named slots); it does not yet name what occupies
  each slot -- see [PairingNoTailServerShape.server_no_tail_start_spine16].
**)
val lemma_server_no_tail_log_spine16
  (server:CS.connection_state)
  : Lemma
      (requires FStar.List.Tot.length server.CS.cs_event_log == 16)
      (ensures
        exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
          server.CS.cs_event_log ==
            [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])

val lemma_client_no_tail_first_event_start
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) :: rest)

val lemma_server_no_tail_first_event_start
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer :: rest)

(**
  Length-16 counterpart of [lemma_server_no_tail_first_event_start], for the
  corrected server no-tail boundary (see [lemma_server_no_tail_log_spine16]).
  The underlying argument (the first event out of [CS.ControlNew] is either
  [LocalStartServer] or illegal/failing) does not depend on the total event
  count, so this is the same proof against the 16-slot spine.
**)
val lemma_server_no_tail_first_event_start16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16)
      (ensures
        exists rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer :: rest)

(**
  After the mandatory first event [LocalStartHandshake start], the only event that
  makes further progress from the [HsStarted] handshake stage is [Sent ClientHello].
  A [TlsChangeCipherSpec] network event (in either direction) is a legal no-op at
  every [ControlHandshaking] stage (see [legal_tls_message]/[step_tls_message]).
  This one-step inversion keeps the explicit non-CCS premise; the clean no-tail
  lemma below discharges it using the length-16 minimum-progress argument.
**)
val lemma_client_no_tail_second_event_client_hello
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16 /\
        (exists start e1 rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) :: e1 :: rest /\
          ~ (exists m.
              e1 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists start ch rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)

(**
  Minimum-progress/no-leading-no-op corollary for the no-tail client boundary.

  A leading [TlsChangeCipherSpec] after [LocalStartHandshake] would leave the
  model in [HsStarted].  The private progress-rank replay lemma in the
  implementation shows that a client still needs at least fifteen subsequent
  events to reach application-ready state, but the length-16 no-tail boundary
  leaves only fourteen.
**)
val lemma_client_no_tail_second_event_not_ccs
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start e1 rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) :: e1 :: rest /\
          ~ (exists m.
              e1 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec))

val lemma_client_no_tail_second_event_client_hello_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)

val lemma_client_no_tail_third_event_server_hello_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            rest)

val lemma_client_no_tail_fourth_event_derive_shared_secret_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
            rest)

(**
  Witness extraction for the state right after the fourth ([LocalDeriveSharedSecret])
  event: [model4] is the post-derive key-schedule state (shared/handshake/master
  secrets present, all four traffic-key slots empty), and the tail of the client's
  event log from the fifth event [e4] onward raw-replays from [model4] to the
  client's final (application-ready) model. This is exactly the state the fifth-
  and sixth-event no-tail inversion lemmas pivot on.
**)
val lemma_client_no_tail_model4_witness
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 rest model4 tail_sent tail_received.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
            e4 ::
            rest /\
          FStar.List.Tot.length rest == 11 /\
          model4.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived /\
          model4.CS.model_config.CS.config_role == CS.ClientEndpoint /\
          Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
          Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret /\
          Some? model4.CS.model_handshake.CS.hs_keys.CS.ks_master_secret /\
          model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
          model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
          model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
          model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
          CS.conn_events_raw_replay model4 (e4 :: rest) tail_sent tail_received client.CS.cs_model /\
          client_application_progress_rank client.CS.cs_model == 0)

val lemma_client_no_tail_fifth_event_handshake_traffic_install_clean
  (client:CS.connection_state)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        FStar.List.Tot.length client.CS.cs_event_log == 16)
      (ensures
        exists start ch sh client_shared e4 rest.
          client.CS.cs_event_log ==
            CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            }) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
            e4 ::
            rest /\
          client_no_tail_handshake_traffic_install_event e4)
