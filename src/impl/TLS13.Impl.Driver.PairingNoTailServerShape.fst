module TLS13.Impl.Driver.PairingNoTailServerShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PWL = TLS13.ConnectionState.ProtectedWireBase
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module SD = TLS13.Impl.Server.Driver
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types

let rec lemma_conn_events_raw_replay_from_failed_results_failed
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
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    assert_norm (
      CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model));
    eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model
    returns
      CS.ControlFailed? final_model.CS.model_control
    with _.
    (
      CSL.lemma_step_model_from_failed_results_failed model ev model1;
      lemma_conn_events_raw_replay_from_failed_results_failed
        model1
        rest
        tail_sent
        tail_received
        final_model
    )

let lemma_server_hs_awaiting_install_traffic_keys_illegal
  (model:CS.connection_model)
  (install:CS.traffic_key_install)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsAwaitingClientHello /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event
          model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)))
      (ensures False)
=
  assert (CS.legal_local_event model (CS.LocalInstallTrafficKeys install));
  assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
  assert False

let lemma_server_hs_awaiting_role_install_illegal
  (model:CS.connection_model)
  (role_install:CS.role_traffic_key_install)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsAwaitingClientHello /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event
          model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)))
      (ensures False)
=
  let install = role_install.CS.install_payload in
  assert (CS.legal_local_event
    model
    (CS.LocalInstallTrafficKeysForRole role_install));
  assert (role_install.CS.install_role == model.CS.model_config.CS.config_role);
  assert (role_install.CS.install_role == CS.ServerEndpoint);
  assert (CS.traffic_install_allowed_at_stage_for_role
    role_install.CS.install_role
    CS.HsAwaitingClientHello
    install);
  assert (CS.traffic_install_allowed_at_stage_for_role
    CS.ServerEndpoint
    CS.HsAwaitingClientHello
    install);
  match install.CS.install_epoch with
  | CS.TrafficHandshake ->
    assert (CS.HsAwaitingClientHello == CS.HsServerHelloSent);
    assert False
  | CS.TrafficApplication ->
    (match install.CS.install_direction with
    | CS.TrafficWrite ->
      assert (CS.HsAwaitingClientHello == CS.HsServerFinishedSent);
      assert False
    | CS.TrafficRead ->
      assert (CS.HsAwaitingClientHello == CS.HsClientFinishedReceived);
      assert False)

let lemma_server_hs_awaiting_non_client_hello_received_network_step_none
  (model:CS.connection_model)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsAwaitingClientHello /\
        (match msg.CL.message_value with
         | M.TlsAlert _ -> False
         | M.TlsChangeCipherSpec -> False
         | M.TlsHandshake (M.ClientHello _) ->
           msg.CL.message_direction == CL.Sent
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnNetworkEvent msg) == None)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsAwaitingClientHello ->
    (match msg.CL.message_value with
    | M.TlsAlert _ ->
      assert False
    | M.TlsChangeCipherSpec ->
      assert False
    | M.TlsHandshake hs ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        (match hs with
        | M.ClientHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.ServerHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
      | CL.Received ->
        (match hs with
        | M.ClientHello _ ->
          assert False
        | M.ServerHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
    | M.TlsApplicationData _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsIgnoredPostHandshake _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsKeyUpdate _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
  | _ ->
    assert False

let lemma_server_hs_client_hello_received_install_traffic_keys_illegal
  (model:CS.connection_model)
  (install:CS.traffic_key_install)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event
          model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install)))
      (ensures False)
=
  assert (CS.legal_local_event model (CS.LocalInstallTrafficKeys install));
  assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
  assert False

let lemma_server_hs_client_hello_received_role_install_illegal
  (model:CS.connection_model)
  (role_install:CS.role_traffic_key_install)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event
          model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)))
      (ensures False)
=
  let install = role_install.CS.install_payload in
  assert (CS.legal_local_event
    model
    (CS.LocalInstallTrafficKeysForRole role_install));
  assert (role_install.CS.install_role == model.CS.model_config.CS.config_role);
  assert (role_install.CS.install_role == CS.ServerEndpoint);
  assert (CS.traffic_install_allowed_at_stage_for_role
    CS.ServerEndpoint
    CS.HsClientHelloReceived
    install);
  match install.CS.install_epoch with
  | CS.TrafficHandshake ->
    assert (CS.HsClientHelloReceived == CS.HsServerHelloSent);
    assert False
  | CS.TrafficApplication ->
    (match install.CS.install_direction with
    | CS.TrafficWrite ->
      assert (CS.HsClientHelloReceived == CS.HsServerFinishedSent);
      assert False
    | CS.TrafficRead ->
      assert (CS.HsClientHelloReceived == CS.HsClientFinishedReceived);
      assert False)

let lemma_server_hs_client_hello_received_no_selection_derive_illegal
  (model:CS.connection_model)
  (shared:C.x25519_shared_secret)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_handshake.CS.hs_server_selection == None /\
        CS.legal_event
          model
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)))
      (ensures False)
=
  assert (CS.legal_local_event
    model
    (CS.LocalDeriveSharedSecret shared));
  match model.CS.model_handshake.CS.hs_server_selection with
  | None ->
    assert False
  | Some _ ->
    assert False

let lemma_server_hs_client_hello_received_local_event_step_none
  (model:CS.connection_model)
  (local:CS.local_event)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        (match local with
         | CS.LocalFail _ -> False
         | CS.LocalInstallTrafficKeys _ -> False
         | CS.LocalInstallTrafficKeysForRole _ -> False
         | CS.LocalSelectServerParameters _ -> False
         | CS.LocalDeriveSharedSecret _ -> False
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnLocalEvent local) == None)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsClientHelloReceived ->
    (match local with
    | CS.LocalFail _ ->
      assert False
    | CS.LocalInstallTrafficKeys _ ->
      assert False
    | CS.LocalInstallTrafficKeysForRole _ ->
      assert False
    | CS.LocalSelectServerParameters _ ->
      assert False
    | CS.LocalDeriveSharedSecret _ ->
      assert False
    | CS.LocalStartHandshake _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalStartServer ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalValidateCertificate _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalVerifyCertificateSignature _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalSignCertificateVerify _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalVerifyFinished _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalVerifyClientFinished _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None)
    | CS.LocalDeliverApplicationData _ ->
      assert_norm (CS.step_model model (CS.ConnLocalEvent local) == None))
  | _ ->
    assert False

let lemma_server_hs_client_hello_received_no_selection_sent_server_hello_illegal
  (model:CS.connection_model)
  (sh:M.server_hello)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_handshake.CS.hs_server_selection == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
        CS.legal_event
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          })))
      (ensures False)
=
  assert (CS.legal_tls_message
    model
    CL.Sent
    (M.TlsHandshake (M.ServerHello sh)));
  assert (CS.legal_handshake_message
    model
    CL.Sent
    (M.ServerHello sh));
  assert (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  assert False

let lemma_server_hs_client_hello_received_no_shared_sent_server_hello_illegal
  (model:CS.connection_model)
  (sh:M.server_hello)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
        CS.legal_event
          model
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          })))
      (ensures False)
=
  assert (CS.legal_tls_message
    model
    CL.Sent
    (M.TlsHandshake (M.ServerHello sh)));
  assert (CS.legal_handshake_message
    model
    CL.Sent
    (M.ServerHello sh));
  assert (Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret);
  assert False

let lemma_server_hs_client_hello_received_has_shared_select_illegal
  (model:CS.connection_model)
  (selection:CS.server_handshake_selection)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        CS.legal_event
          model
          (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)))
      (ensures False)
=
  assert (CS.legal_local_event
    model
    (CS.LocalSelectServerParameters selection));
  assert (model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
  match model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret with
  | Some _ ->
    assert False
  | None ->
    assert False

let lemma_server_hs_client_hello_received_derive_shared_secret_step
  (model:CS.connection_model)
  (shared:C.x25519_shared_secret)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived)
      (ensures
        CS.step_model
          model
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
        Some (CS.derive_shared_secret_model
          model
          model.CS.model_handshake
          shared))
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsClientHelloReceived ->
    assert (
      CS.step_model
        model
        (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
      Some (CS.derive_shared_secret_model
        model
        model.CS.model_handshake
        shared))
  | _ ->
    assert False

let lemma_server_hs_client_hello_received_non_server_hello_network_step_none
  (model:CS.connection_model)
  (msg:CL.directed_message M.tls_message)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientHelloReceived /\
        (match msg.CL.message_value with
         | M.TlsAlert _ -> False
         | M.TlsChangeCipherSpec -> False
         | M.TlsHandshake (M.ServerHello _) ->
           msg.CL.message_direction == CL.Received
         | _ -> True))
      (ensures
        CS.step_model model (CS.ConnNetworkEvent msg) == None)
=
  match model.CS.model_control with
  | CS.ControlHandshaking CS.HsClientHelloReceived ->
    (match msg.CL.message_value with
    | M.TlsAlert _ ->
      assert False
    | M.TlsChangeCipherSpec ->
      assert False
    | M.TlsHandshake hs ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        (match hs with
        | M.ClientHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.ServerHello _ ->
          assert False
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
      | CL.Received ->
        (match hs with
        | M.ClientHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.ServerHello _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.EncryptedExtensions _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Certificate _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.CertificateVerify _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.Finished _ ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
        | M.HelloRetryRequest ->
          assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
    | M.TlsApplicationData _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsIgnoredPostHandshake _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None))
    | M.TlsKeyUpdate _ ->
      (match msg.CL.message_direction with
      | CL.Sent ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)
      | CL.Received ->
        assert_norm (CS.step_model model (CS.ConnNetworkEvent msg) == None)))
  | _ ->
    assert False

let option_missing #a (o:option a) : nat =
  match o with
  | Some _ -> 0
  | None -> 1

let server_application_obligation_rank
  (keys:CS.key_schedule_state)
  : nat =
  option_missing keys.CS.ks_shared_secret +
  option_missing keys.CS.ks_server_application_traffic +
  option_missing keys.CS.ks_client_application_traffic

let server_handshake_traffic_obligation_rank
  (keys:CS.key_schedule_state)
  : nat =
  option_missing keys.CS.ks_server_handshake_traffic +
  option_missing keys.CS.ks_client_handshake_traffic

let server_encrypted_flight_constant
  (hs:CS.handshake_state)
  : nat =
  // Since the model fix, [hs_certificate_verify_verified] is a wire-progress
  // marker for sent CertificateVerify, not merely local signing progress.
  match hs.CS.hs_certificate with
  | None -> if hs.CS.hs_certificate_verify_verified then 3 else 5
  | Some _ -> if hs.CS.hs_certificate_verify_verified then 3 else 4

let server_application_progress_rank
  (model:CS.connection_model)
  : nat =
  let hs = model.CS.model_handshake in
  let keys = hs.CS.hs_keys in
  let final_rank = server_application_obligation_rank keys in
  match model.CS.model_control with
  | CS.ControlApplicationData
  | CS.ControlClosing
  | CS.ControlClosed ->
    final_rank
  | CS.ControlHandshaking stage ->
    (match stage with
    | CS.HsAwaitingClientHello ->
      3 +
      server_encrypted_flight_constant hs +
      option_missing hs.CS.hs_server_selection +
      server_handshake_traffic_obligation_rank keys +
      final_rank
    | CS.HsClientHelloReceived ->
      2 +
      server_encrypted_flight_constant hs +
      option_missing hs.CS.hs_server_selection +
      server_handshake_traffic_obligation_rank keys +
      final_rank
    | CS.HsServerHelloSent ->
      1 +
      server_encrypted_flight_constant hs +
      server_handshake_traffic_obligation_rank keys +
      final_rank
    | CS.HsServerEncryptedFlightSent ->
      option_missing keys.CS.ks_client_handshake_traffic +
      final_rank +
      server_encrypted_flight_constant hs
    | CS.HsServerFinishedSent ->
      option_missing keys.CS.ks_client_handshake_traffic + 2 + final_rank
    | CS.HsClientFinishedReceived ->
      1 + final_rank
    | _ ->
      0)
  | _ ->
    0

(**
  Standalone helper factoring out the [HsClientHelloReceived]-with-selection
  arithmetic case of [server_application_progress_rank].  The no-tail
  inversion proofs below establish every hypothesis field here as an
  individual (cheap) fact just before needing this conclusion, but the
  surrounding proof context is a single deeply-nested "eliminate exists"
  term (role-local case split over which local/network event comes next).
  Combining the final numeric fact with that whole context in one SMT query
  dilutes the rlimit budget across everything else in the query, even though
  the fact itself is a two-line unfolding.  Isolating it as its own lemma
  gives it its own small query, independent of how deeply it is invoked from.
**)
let lemma_server_application_progress_rank_client_hello_received_selected
  (model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived /\
        Some? model.CS.model_handshake.CS.hs_server_selection /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
      (ensures server_application_progress_rank model == 12)
= ()

(**
  Companion to [lemma_server_application_progress_rank_client_hello_received_selected]
  for the point right after [LocalDeriveSharedSecret]: still [HsClientHelloReceived]
  (deriving the shared secret does not itself advance the control stage), selection
  and the shared secret are now both set, and the handshake/application traffic
  key slots are still empty.
**)
let lemma_server_application_progress_rank_client_hello_received_selected_shared
  (model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsClientHelloReceived /\
        Some? model.CS.model_handshake.CS.hs_server_selection /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None)
      (ensures server_application_progress_rank model == 11)
= ()

let lemma_server_application_ready_progress_rank_zero
  (server:CS.connection_state)
  : Lemma
      (requires SD.server_driver_application_ready server)
      (ensures server_application_progress_rank server.CS.cs_model == 0)
=
  let keys = server.CS.cs_model.CS.model_handshake.CS.hs_keys in
  CSL.lemma_server_application_ready_stable_x25519_key_share_projection server;
  assert (CS.stable_server_x25519_key_share_projection server);
  assert (CS.server_x25519_key_share_projection server);
  assert (CS.application_record_keys_installed_for_role
    CS.ServerEndpoint
    server.CS.cs_model);
  assert_norm
    (CS.traffic_label_for_endpoint_direction
      CS.ServerEndpoint
      CS.TrafficWrite == CS.ServerTraffic);
  assert_norm
    (CS.traffic_label_for_endpoint_direction
      CS.ServerEndpoint
      CS.TrafficRead == CS.ClientTraffic);
  match
    keys.CS.ks_shared_secret,
    keys.CS.ks_server_application_traffic,
    keys.CS.ks_client_application_traffic
  with
  | Some _, Some _, Some _ ->
    ()
  | _, _, _ ->
    assert False

let lemma_server_progress_rank_role_install
  (model:CS.connection_model)
  (role_install:CS.role_traffic_key_install)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event
          model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)) /\
        CS.step_model
          model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install)) ==
          Some model')
      (ensures
        server_application_progress_rank model <=
        server_application_progress_rank model' + 1)
=
  let install = role_install.CS.install_payload in
  assert (CS.legal_local_event
    model
    (CS.LocalInstallTrafficKeysForRole role_install));
  assert (role_install.CS.install_role == CS.ServerEndpoint);
  assert (CS.step_local_event
    model
    (CS.LocalInstallTrafficKeysForRole role_install) == Some model');
  match model.CS.model_control with
  | CS.ControlHandshaking stage ->
    assert (CS.traffic_install_allowed_at_stage_for_role
      CS.ServerEndpoint
      stage
      install);
    (match stage, install.CS.install_epoch, install.CS.install_direction with
    | CS.HsServerHelloSent, CS.TrafficHandshake, CS.TrafficWrite ->
      assert_norm
        (CS.traffic_label_for_endpoint_direction
          CS.ServerEndpoint
          CS.TrafficWrite == CS.ServerTraffic);
      assert (server_application_progress_rank model <=
        server_application_progress_rank model' + 1)
    | CS.HsServerHelloSent, CS.TrafficHandshake, CS.TrafficRead ->
      assert_norm
        (CS.traffic_label_for_endpoint_direction
          CS.ServerEndpoint
          CS.TrafficRead == CS.ClientTraffic);
      assert (server_application_progress_rank model <=
        server_application_progress_rank model' + 1)
    | CS.HsServerFinishedSent, CS.TrafficApplication, CS.TrafficWrite ->
      assert_norm
        (CS.traffic_label_for_endpoint_direction
          CS.ServerEndpoint
          CS.TrafficWrite == CS.ServerTraffic);
      assert (server_application_progress_rank model <=
        server_application_progress_rank model' + 1)
    | CS.HsClientFinishedReceived, CS.TrafficApplication, CS.TrafficRead ->
      assert_norm
        (CS.traffic_label_for_endpoint_direction
          CS.ServerEndpoint
          CS.TrafficRead == CS.ClientTraffic);
      assert (server_application_progress_rank model <=
        server_application_progress_rank model' + 1)
    | _, _, _ ->
      assert False)
  | _ ->
    assert False

let lemma_server_application_progress_rank_step
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (model':CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.legal_event model ev /\
        CS.step_model model ev == Some model')
      (ensures
        CS.ControlFailed? model'.CS.model_control \/
        server_application_progress_rank model <=
        server_application_progress_rank model' + 1)
=
  CSL.lemma_step_model_preserves_config model ev model';
  match model'.CS.model_control with
  | CS.ControlFailed _ ->
    ()
  | _ ->
    (match ev with
    | CS.ConnLocalEvent local ->
      assert (CS.legal_local_event model local);
      assert (CS.step_local_event model local == Some model');
      (match local with
      | CS.LocalInstallTrafficKeys install ->
        assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert False
      | CS.LocalInstallTrafficKeysForRole role_install ->
        lemma_server_progress_rank_role_install model role_install model'
      | CS.LocalFail _ ->
        assert False
      | _ ->
        (match model.CS.model_control, local with
        | CS.ControlNew, CS.LocalStartServer ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlNew, CS.LocalStartHandshake _ ->
          assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert False
        | CS.ControlHandshaking CS.HsClientHelloReceived,
          CS.LocalSelectServerParameters _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsClientHelloReceived,
          CS.LocalDeriveSharedSecret _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerHelloReceived,
          CS.LocalDeriveSharedSecret _ ->
          assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert False
        | CS.ControlHandshaking CS.HsCertificateReceived,
          CS.LocalValidateCertificate _ ->
          assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert False
        | CS.ControlHandshaking CS.HsCertificateVerifyReceived,
          CS.LocalVerifyCertificateSignature _ ->
          assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert False
        | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
          CS.LocalSignCertificateVerify _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerFinishedReceived,
          CS.LocalVerifyFinished _ ->
          assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert False
        | CS.ControlHandshaking CS.HsClientFinishedReceived,
          CS.LocalVerifyClientFinished _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlApplicationData,
          CS.LocalDeliverApplicationData _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | _, _ ->
          assert (CS.step_local_event model local == None);
          assert False))
    | CS.ConnNetworkEvent msg ->
      assert (CS.legal_tls_message
        model
        msg.CL.message_direction
        msg.CL.message_value);
      assert (CS.step_tls_message
        model
        msg.CL.message_direction
        msg.CL.message_value == Some model');
      (match msg.CL.message_value with
      | M.TlsAlert alert ->
        (match alert, model.CS.model_control, msg.CL.message_direction with
        | T.Close_notify, CS.ControlApplicationData, CL.Sent ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | T.Close_notify, CS.ControlApplicationData, CL.Received ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | T.Close_notify, CS.ControlClosing, CL.Received ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | _, _, _ ->
          assert False)
      | M.TlsChangeCipherSpec ->
        assert (model' == model);
        assert (server_application_progress_rank model <=
          server_application_progress_rank model' + 1)
      | M.TlsHandshake hs_msg ->
        (match model.CS.model_control, msg.CL.message_direction, hs_msg with
        | CS.ControlHandshaking CS.HsAwaitingClientHello,
          CL.Received,
          M.ClientHello _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsClientHelloReceived,
          CL.Sent,
          M.ServerHello _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerHelloSent,
          CL.Sent,
          M.EncryptedExtensions ee ->
          assert (CS.legal_handshake_message
            model
            CL.Sent
            (M.EncryptedExtensions ee));
          assert (Some?
            model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
          let hs0 = model.CS.model_handshake in
          let model_after =
            CS.with_handshake_stage
              {
                model with
                  CS.model_record = {
                    model.CS.model_record with
                      CS.record_write = R.next_seq model.CS.model_record.CS.record_write;
                  };
              }
              (CS.append_handshake_to_transcript
                { hs0 with CS.hs_encrypted_extensions = Some ee }
                (M.EncryptedExtensions ee))
              CS.HsServerEncryptedFlightSent in
          assert_norm (
            CS.step_tls_message
              model
              CL.Sent
              (M.TlsHandshake (M.EncryptedExtensions ee)) ==
            Some model_after);
          assert (model' == model_after);
          assert (model'.CS.model_control ==
            CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
          assert (model'.CS.model_handshake.CS.hs_keys ==
            model.CS.model_handshake.CS.hs_keys);
          assert (model'.CS.model_handshake.CS.hs_certificate ==
            model.CS.model_handshake.CS.hs_certificate);
          assert (model'.CS.model_handshake.CS.hs_certificate_verify_verified ==
            model.CS.model_handshake.CS.hs_certificate_verify_verified);
          (match model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic with
          | Some _ -> ()
          | None -> assert False);
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
          CL.Sent,
          M.Certificate _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
          CL.Sent,
          M.CertificateVerify _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerEncryptedFlightSent,
          CL.Sent,
          M.Finished _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsServerFinishedSent,
          CL.Received,
          M.Finished _ ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | CS.ControlHandshaking CS.HsClientHelloSent,
          CL.Received,
          M.HelloRetryRequest ->
          assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
          assert False
        | _, _, _ ->
          assert (CS.step_handshake_message
            model
            msg.CL.message_direction
            hs_msg == None);
          assert False)
      | M.TlsApplicationData _ ->
        (match model.CS.model_control with
        | CS.ControlApplicationData ->
          assert (server_application_progress_rank model <=
            server_application_progress_rank model' + 1)
        | _ ->
          assert False)
      | M.TlsIgnoredPostHandshake _ ->
        assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert False
      | M.TlsKeyUpdate _ ->
        assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
        assert False))

let rec lemma_server_application_progress_rank_replay_lower_bound
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        CS.conn_events_raw_replay model events raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        server_application_progress_rank final_model == 0)
      (ensures
        server_application_progress_rank model <= FStar.List.Tot.length events)
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    assert_norm (
      CS.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model));
    eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      CS.conn_events_raw_replay model1 rest tail_sent tail_received final_model
    returns
      server_application_progress_rank model <= FStar.List.Tot.length (ev :: rest)
    with _.
    (
      lemma_server_application_progress_rank_step model ev model1;
      match model1.CS.model_control with
      | CS.ControlFailed _ ->
        lemma_conn_events_raw_replay_from_failed_results_failed
          model1
          rest
          tail_sent
          tail_received
          final_model;
        assert (CS.ControlFailed? final_model.CS.model_control);
        assert (final_model.CS.model_control == CS.ControlApplicationData);
        assert False
      | _ ->
        CSL.lemma_step_model_preserves_config model ev model1;
        assert (model1.CS.model_config == model.CS.model_config);
        lemma_server_application_progress_rank_replay_lower_bound
          model1
          rest
          tail_sent
          tail_received
          final_model;
        assert (server_application_progress_rank model <=
          server_application_progress_rank model1 + 1);
        assert (server_application_progress_rank model1 <= FStar.List.Tot.length rest);
        assert (FStar.List.Tot.length (ev :: rest) == FStar.List.Tot.length rest + 1)
    )

let lemma_server_no_tail_start_spine
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures server_no_tail_start_spine server)
=
  PNI.lemma_server_no_tail_log_spine server;
  PNI.lemma_server_no_tail_first_event_start server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
    server.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
  returns
    server_no_tail_start_spine server
  with _.
  (
    eliminate exists rest.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: rest
    returns
      server_no_tail_start_spine server
    with _.
    (
      assert (server.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
      assert (server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: rest);
      assert (e0 == CS.ConnLocalEvent CS.LocalStartServer);
      assert (rest == [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
      assert (server.CS.cs_event_log ==
        [ CS.ConnLocalEvent CS.LocalStartServer;
          e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ])
    )
  )

let lemma_server_no_tail_final_model_witnesses_from_application_ready
  (server:CS.connection_state)
  : Lemma
     (requires
       SD.server_driver_application_ready server)
     (ensures server_no_tail_final_model_witnesses server)
=
  let hs = server.CS.cs_model.CS.model_handshake in
  CSL.lemma_server_application_ready_stable_x25519_key_share_projection server;
  assert (CS.stable_server_x25519_key_share_projection server);
  assert (CS.server_x25519_key_share_projection server);
  assert (CS.application_record_keys_installed_for_role
   CS.ServerEndpoint
   server.CS.cs_model);
  assert_norm
   (CS.traffic_label_for_endpoint_direction
     CS.ServerEndpoint
     CS.TrafficRead == CS.ClientTraffic);
  assert_norm
   (CS.traffic_label_for_endpoint_direction
     CS.ServerEndpoint
     CS.TrafficWrite == CS.ServerTraffic);
  match
   hs.CS.hs_server_selection,
   hs.CS.hs_client_hello,
   hs.CS.hs_server_hello,
   hs.CS.hs_keys.CS.ks_shared_secret
  with
  | Some selection, Some ch, Some sh, Some server_shared ->
   (match
     CS.traffic_material_for_label
       hs.CS.hs_keys
       CS.TrafficApplication
       CS.ClientTraffic,
     CS.traffic_material_for_label
       hs.CS.hs_keys
       CS.TrafficApplication
       CS.ServerTraffic
   with
   | Some server_app_read_material, Some server_app_write_material ->
     ()
   | _, _ ->
     assert False)
  | _, _, _, _ ->
   assert False

let lemma_server_no_tail_final_model_witnesses
  (server:CS.connection_state)
  : Lemma
     (requires
       SD.server_driver_application_ready server /\
       FStar.List.Tot.length server.CS.cs_event_log == 15)
     (ensures server_no_tail_final_model_witnesses server)
=
  lemma_server_no_tail_final_model_witnesses_from_application_ready server

let lemma_server_no_tail_final_model_witnesses16
  (server:CS.connection_state)
  : Lemma
     (requires
       SD.server_driver_application_ready server /\
       FStar.List.Tot.length server.CS.cs_event_log == 16)
     (ensures server_no_tail_final_model_witnesses server)
=
  lemma_server_no_tail_final_model_witnesses_from_application_ready server

let lemma_server_no_tail_start_spine_and_final_model_witnesses
  (server:CS.connection_state)
  : Lemma
     (requires
       SD.server_driver_application_ready server /\
       FStar.List.Tot.length server.CS.cs_event_log == 15)
     (ensures
       server_no_tail_start_spine server /\
       server_no_tail_final_model_witnesses server)
=
  lemma_server_no_tail_start_spine server;
  lemma_server_no_tail_final_model_witnesses server

let lemma_server_no_tail_second_event_client_hello_if_not_ccs
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15 /\
        (exists e1 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
          ~ (exists m.
              e1 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists ch rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)
=
  PNI.lemma_server_no_tail_log_spine server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
    server.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
  returns
    exists ch rest.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        rest
  with _.
  (
    eliminate exists e1' rest'.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: e1' :: rest' /\
      ~ (exists m.
          e1' == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec)
    returns
      exists ch rest.
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          rest
    with _.
    (
      assert (server.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
      assert (server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: e1' :: rest');
      assert (e0 == CS.ConnLocalEvent CS.LocalStartServer);
      assert (e1 == e1');
      assert (rest' == [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
      assert (~ (exists m.
        e1 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec));

      assert (ST.server_end_to_end_invariant server);
      assert (CS.connection_state_raw_event_replay_consistent server);
      let initial = CS.initial_model server.CS.cs_model.CS.model_config in
      assert (CS.conn_events_raw_replay
        initial
        server.CS.cs_event_log
        server.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received
        server.CS.cs_model);
      assert_norm (
        CS.conn_events_raw_replay
          initial
          (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
          server.CS.cs_wire_log.CL.raw_sent
          server.CS.cs_wire_log.CL.raw_received
          server.CS.cs_model ==
        (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
          CS.legal_event initial e0 /\
          CS.step_model initial e0 == Some model1 /\
          CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_sent
            (B.append delta_sent0 tail_sent0) /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_received
            (B.append delta_received0 tail_received0) /\
          CS.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
            tail_sent0
            tail_received0
            server.CS.cs_model));
      eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
        CS.legal_event initial e0 /\
        CS.step_model initial e0 == Some model1 /\
        CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_sent
          (B.append delta_sent0 tail_sent0) /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_received
          (B.append delta_received0 tail_received0) /\
        CS.conn_events_raw_replay
          model1
          [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
          tail_sent0
          tail_received0
          server.CS.cs_model
      returns
        exists ch rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest
      with _.
      (
        assert (initial.CS.model_control == CS.ControlNew);
        assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
        assert_norm (
          CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) ==
          Some (CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello));
        assert (CS.step_model initial e0 ==
          Some (CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello));
        assert (model1 ==
          CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello);
        assert (model1.CS.model_control ==
          CS.ControlHandshaking CS.HsAwaitingClientHello);
        assert (model1.CS.model_config == initial.CS.model_config);
        assert (model1.CS.model_config.CS.config_role == CS.ServerEndpoint);

        assert_norm (
          CS.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
            tail_sent0
            tail_received0
            server.CS.cs_model ==
          (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
            CS.legal_event model1 e1 /\
            CS.step_model model1 e1 == Some model2 /\
            CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
            Seq.equal
              tail_sent0
              (B.append delta_sent1 tail_sent1) /\
            Seq.equal
              tail_received0
              (B.append delta_received1 tail_received1) /\
            CS.conn_events_raw_replay
              model2
              [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
              tail_sent1
              tail_received1
              server.CS.cs_model));
        eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
          CS.legal_event model1 e1 /\
          CS.step_model model1 e1 == Some model2 /\
          CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
          Seq.equal
            tail_sent0
            (B.append delta_sent1 tail_sent1) /\
          Seq.equal
            tail_received0
            (B.append delta_received1 tail_received1) /\
          CS.conn_events_raw_replay
            model2
            [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
            tail_sent1
            tail_received1
            server.CS.cs_model
        returns
          exists ch rest.
            server.CS.cs_event_log ==
              CS.ConnLocalEvent CS.LocalStartServer ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              }) ::
              rest
        with _.
        (
          match e1 with
          | CS.ConnLocalEvent local ->
            (match local with
            | CS.LocalFail err ->
              assert (e1 == CS.ConnLocalEvent (CS.LocalFail err));
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                Some (CS.fail_model model1 err));
              assert (model2.CS.model_control == CS.ControlFailed err);
              lemma_conn_events_raw_replay_from_failed_results_failed
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent1
                tail_received1
                server.CS.cs_model;
              assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
              assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
              assert False
            | CS.LocalInstallTrafficKeys install ->
              lemma_server_hs_awaiting_install_traffic_keys_illegal model1 install;
              assert False
            | CS.LocalInstallTrafficKeysForRole role_install ->
              lemma_server_hs_awaiting_role_install_illegal model1 role_install;
              assert False
            | CS.LocalStartHandshake start ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalStartServer ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent CS.LocalStartServer) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalSelectServerParameters selection ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalDeriveSharedSecret shared ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalValidateCertificate peer ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalVerifyCertificateSignature cv ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalSignCertificateVerify cv ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalVerifyFinished fin ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalVerifyFinished fin)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalVerifyClientFinished fin ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalDeliverApplicationData bytes ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False)
          | CS.ConnNetworkEvent msg ->
            (match msg.CL.message_value with
            | M.TlsAlert alert ->
              assert (e1 == CS.ConnNetworkEvent msg);
              assert_norm (
                CS.step_model model1 (CS.ConnNetworkEvent msg) ==
                Some (CS.fail_model model1 (T.AlertError alert)));
              assert (CS.step_model model1 e1 ==
                Some (CS.fail_model model1 (T.AlertError alert)));
              assert (model2 == CS.fail_model model1 (T.AlertError alert));
              assert (model2.CS.model_control == CS.ControlFailed (T.AlertError alert));
              lemma_conn_events_raw_replay_from_failed_results_failed
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent1
                tail_received1
                server.CS.cs_model;
              assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
              assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
              assert False
            | M.TlsChangeCipherSpec ->
              assert (e1 == CS.ConnNetworkEvent msg);
              assert (exists m.
                e1 == CS.ConnNetworkEvent m /\
                m.CL.message_value == M.TlsChangeCipherSpec);
              assert False
            | M.TlsHandshake handshake_msg ->
              (match msg.CL.message_direction, handshake_msg with
              | CL.Received, M.ClientHello ch ->
                assert (e1 == CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch);
                }));
                assert (server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) ::
                  [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
              | _, _ ->
                lemma_server_hs_awaiting_non_client_hello_received_network_step_none
                  model1
                  msg;
                assert (CS.step_model model1 e1 == None);
                assert False)
            | M.TlsApplicationData _ ->
              lemma_server_hs_awaiting_non_client_hello_received_network_step_none
                model1
                msg;
              assert (CS.step_model model1 e1 == None);
              assert False
            | M.TlsIgnoredPostHandshake _ ->
              lemma_server_hs_awaiting_non_client_hello_received_network_step_none
                model1
                msg;
              assert (CS.step_model model1 e1 == None);
              assert False
            | M.TlsKeyUpdate _ ->
              lemma_server_hs_awaiting_non_client_hello_received_network_step_none
                model1
                msg;
              assert (CS.step_model model1 e1 == None);
              assert False)
        )
      )
    )
  )

let lemma_server_no_tail_second_event_client_hello_if_not_ccs16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16 /\
        (exists e1 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
          ~ (exists m.
              e1 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec)))
      (ensures
        exists ch rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)
=
  PNI.lemma_server_no_tail_log_spine16 server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
    server.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
  returns
    exists ch rest.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        rest
  with _.
  (
    eliminate exists e1' rest'.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: e1' :: rest' /\
      ~ (exists m.
          e1' == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec)
    returns
      exists ch rest.
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          rest
    with _.
    (
      assert (server.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert (server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: e1' :: rest');
      assert (e0 == CS.ConnLocalEvent CS.LocalStartServer);
      assert (e1 == e1');
      assert (rest' == [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert (~ (exists m.
        e1 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec));

      assert (ST.server_end_to_end_invariant server);
      assert (CS.connection_state_raw_event_replay_consistent server);
      let initial = CS.initial_model server.CS.cs_model.CS.model_config in
      assert (CS.conn_events_raw_replay
        initial
        server.CS.cs_event_log
        server.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received
        server.CS.cs_model);
      assert_norm (
        CS.conn_events_raw_replay
          initial
          (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
          server.CS.cs_wire_log.CL.raw_sent
          server.CS.cs_wire_log.CL.raw_received
          server.CS.cs_model ==
        (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
          CS.legal_event initial e0 /\
          CS.step_model initial e0 == Some model1 /\
          CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_sent
            (B.append delta_sent0 tail_sent0) /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_received
            (B.append delta_received0 tail_received0) /\
          CS.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent0
            tail_received0
            server.CS.cs_model));
      eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
        CS.legal_event initial e0 /\
        CS.step_model initial e0 == Some model1 /\
        CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_sent
          (B.append delta_sent0 tail_sent0) /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_received
          (B.append delta_received0 tail_received0) /\
        CS.conn_events_raw_replay
          model1
          [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
          tail_sent0
          tail_received0
          server.CS.cs_model
      returns
        exists ch rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest
      with _.
      (
        assert (initial.CS.model_control == CS.ControlNew);
        assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
        assert_norm (
          CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) ==
          Some (CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello));
        assert (CS.step_model initial e0 ==
          Some (CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello));
        assert (model1 ==
          CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello);
        assert (model1.CS.model_control ==
          CS.ControlHandshaking CS.HsAwaitingClientHello);
        assert (model1.CS.model_config == initial.CS.model_config);
        assert (model1.CS.model_config.CS.config_role == CS.ServerEndpoint);

        assert_norm (
          CS.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent0
            tail_received0
            server.CS.cs_model ==
          (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
            CS.legal_event model1 e1 /\
            CS.step_model model1 e1 == Some model2 /\
            CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
            Seq.equal
              tail_sent0
              (B.append delta_sent1 tail_sent1) /\
            Seq.equal
              tail_received0
              (B.append delta_received1 tail_received1) /\
            CS.conn_events_raw_replay
              model2
              [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
              tail_sent1
              tail_received1
              server.CS.cs_model));
        eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
          CS.legal_event model1 e1 /\
          CS.step_model model1 e1 == Some model2 /\
          CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
          Seq.equal
            tail_sent0
            (B.append delta_sent1 tail_sent1) /\
          Seq.equal
            tail_received0
            (B.append delta_received1 tail_received1) /\
          CS.conn_events_raw_replay
            model2
            [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
            tail_sent1
            tail_received1
            server.CS.cs_model
        returns
          exists ch rest.
            server.CS.cs_event_log ==
              CS.ConnLocalEvent CS.LocalStartServer ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              }) ::
              rest
        with _.
        (
          match e1 with
          | CS.ConnLocalEvent local ->
            (match local with
            | CS.LocalFail err ->
              assert (e1 == CS.ConnLocalEvent (CS.LocalFail err));
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                Some (CS.fail_model model1 err));
              assert (model2.CS.model_control == CS.ControlFailed err);
              lemma_conn_events_raw_replay_from_failed_results_failed
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                tail_sent1
                tail_received1
                server.CS.cs_model;
              assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
              assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
              assert False
            | CS.LocalInstallTrafficKeys install ->
              lemma_server_hs_awaiting_install_traffic_keys_illegal model1 install;
              assert False
            | CS.LocalInstallTrafficKeysForRole role_install ->
              lemma_server_hs_awaiting_role_install_illegal model1 role_install;
              assert False
            | CS.LocalStartHandshake start ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalStartHandshake start)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalStartServer ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent CS.LocalStartServer) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalSelectServerParameters selection ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalDeriveSharedSecret shared ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalValidateCertificate peer ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalVerifyCertificateSignature cv ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalSignCertificateVerify cv ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalVerifyFinished fin ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalVerifyFinished fin)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalVerifyClientFinished fin ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False
            | CS.LocalDeliverApplicationData bytes ->
              assert_norm (
                CS.step_model model1 (CS.ConnLocalEvent (CS.LocalDeliverApplicationData bytes)) ==
                None);
              assert (CS.step_model model1 e1 == None);
              assert False)
          | CS.ConnNetworkEvent msg ->
            (match msg.CL.message_value with
            | M.TlsAlert alert ->
              assert (e1 == CS.ConnNetworkEvent msg);
              assert_norm (
                CS.step_model model1 (CS.ConnNetworkEvent msg) ==
                Some (CS.fail_model model1 (T.AlertError alert)));
              assert (CS.step_model model1 e1 ==
                Some (CS.fail_model model1 (T.AlertError alert)));
              assert (model2 == CS.fail_model model1 (T.AlertError alert));
              assert (model2.CS.model_control == CS.ControlFailed (T.AlertError alert));
              lemma_conn_events_raw_replay_from_failed_results_failed
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
                tail_sent1
                tail_received1
                server.CS.cs_model;
              assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
              assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
              assert False
            | M.TlsChangeCipherSpec ->
              assert (e1 == CS.ConnNetworkEvent msg);
              assert (exists m.
                e1 == CS.ConnNetworkEvent m /\
                m.CL.message_value == M.TlsChangeCipherSpec);
              assert False
            | M.TlsHandshake handshake_msg ->
              (match msg.CL.message_direction, handshake_msg with
              | CL.Received, M.ClientHello ch ->
                assert (e1 == CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch);
                }));
                assert (server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) ::
                  [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15])
              | _, _ ->
                lemma_server_hs_awaiting_non_client_hello_received_network_step_none
                  model1
                  msg;
                assert (CS.step_model model1 e1 == None);
                assert False)
            | M.TlsApplicationData _ ->
              lemma_server_hs_awaiting_non_client_hello_received_network_step_none
                model1
                msg;
              assert (CS.step_model model1 e1 == None);
              assert False
            | M.TlsIgnoredPostHandshake _ ->
              lemma_server_hs_awaiting_non_client_hello_received_network_step_none
                model1
                msg;
              assert (CS.step_model model1 e1 == None);
              assert False
            | M.TlsKeyUpdate _ ->
              lemma_server_hs_awaiting_non_client_hello_received_network_step_none
                model1
                msg;
              assert (CS.step_model model1 e1 == None);
              assert False)
        )
      )
    )
  )

let lemma_server_no_tail_second_event_not_ccs
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists e1 rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
          ~ (exists m.
              e1 == CS.ConnNetworkEvent m /\
              m.CL.message_value == M.TlsChangeCipherSpec))
=
  PNI.lemma_server_no_tail_log_spine server;
  PNI.lemma_server_no_tail_first_event_start server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
    server.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
  returns
    exists e1 rest.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
      ~ (exists m.
          e1 == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec)
  with _.
  (
    eliminate exists rest0.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: rest0
    returns
      exists e1 rest.
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
        ~ (exists m.
            e1 == CS.ConnNetworkEvent m /\
            m.CL.message_value == M.TlsChangeCipherSpec)
    with _.
    (
      assert (server.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
      assert (server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: rest0);
      assert (e0 == CS.ConnLocalEvent CS.LocalStartServer);
      assert (rest0 == [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);

      match e1 with
      | CS.ConnLocalEvent _ ->
        ()
      | CS.ConnNetworkEvent msg ->
        (match msg.CL.message_value with
        | M.TlsChangeCipherSpec ->
          assert (ST.server_end_to_end_invariant server);
          assert (CS.connection_state_raw_event_replay_consistent server);
          lemma_server_application_ready_progress_rank_zero server;
          let initial = CS.initial_model server.CS.cs_model.CS.model_config in
          assert (CS.conn_events_raw_replay
            initial
            server.CS.cs_event_log
            server.CS.cs_wire_log.CL.raw_sent
            server.CS.cs_wire_log.CL.raw_received
            server.CS.cs_model);
          assert_norm (
            CS.conn_events_raw_replay
              initial
              (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
              server.CS.cs_wire_log.CL.raw_sent
              server.CS.cs_wire_log.CL.raw_received
              server.CS.cs_model ==
            (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
              CS.legal_event initial e0 /\
              CS.step_model initial e0 == Some model1 /\
              CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
              Seq.equal
                server.CS.cs_wire_log.CL.raw_sent
                (B.append delta_sent0 tail_sent0) /\
              Seq.equal
                server.CS.cs_wire_log.CL.raw_received
                (B.append delta_received0 tail_received0) /\
              CS.conn_events_raw_replay
                model1
                [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent0
                tail_received0
                server.CS.cs_model));
          eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
            CS.legal_event initial e0 /\
            CS.step_model initial e0 == Some model1 /\
            CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
            Seq.equal
              server.CS.cs_wire_log.CL.raw_sent
              (B.append delta_sent0 tail_sent0) /\
            Seq.equal
              server.CS.cs_wire_log.CL.raw_received
              (B.append delta_received0 tail_received0) /\
            CS.conn_events_raw_replay
              model1
              [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
              tail_sent0
              tail_received0
              server.CS.cs_model
          returns
            exists e1 rest.
              server.CS.cs_event_log ==
                CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
              ~ (exists m.
                  e1 == CS.ConnNetworkEvent m /\
                  m.CL.message_value == M.TlsChangeCipherSpec)
          with _.
          (
            assert (initial.CS.model_control == CS.ControlNew);
            assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
            assert_norm (
              CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) ==
              Some (CS.with_handshake_stage
                initial
                initial.CS.model_handshake
                CS.HsAwaitingClientHello));
            assert (CS.step_model initial e0 ==
              Some (CS.with_handshake_stage
                initial
                initial.CS.model_handshake
                CS.HsAwaitingClientHello));
            assert (model1 ==
              CS.with_handshake_stage
                initial
                initial.CS.model_handshake
                CS.HsAwaitingClientHello);
            assert (model1.CS.model_control ==
              CS.ControlHandshaking CS.HsAwaitingClientHello);
            assert (model1.CS.model_config == initial.CS.model_config);
            assert_norm (
              server_application_progress_rank
                (CS.with_handshake_stage
                  initial
                  initial.CS.model_handshake
                  CS.HsAwaitingClientHello) == 14);
            assert (server_application_progress_rank model1 == 14);

            assert_norm (
              CS.conn_events_raw_replay
                model1
                [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent0
                tail_received0
                server.CS.cs_model ==
              (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
                CS.legal_event model1 e1 /\
                CS.step_model model1 e1 == Some model2 /\
                CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
                Seq.equal
                  tail_sent0
                  (B.append delta_sent1 tail_sent1) /\
                Seq.equal
                  tail_received0
                  (B.append delta_received1 tail_received1) /\
                CS.conn_events_raw_replay
                  model2
                  [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                  tail_sent1
                  tail_received1
                  server.CS.cs_model));
            eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
              CS.legal_event model1 e1 /\
              CS.step_model model1 e1 == Some model2 /\
              CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
              Seq.equal
                tail_sent0
                (B.append delta_sent1 tail_sent1) /\
              Seq.equal
                tail_received0
                (B.append delta_received1 tail_received1) /\
              CS.conn_events_raw_replay
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent1
                tail_received1
                server.CS.cs_model
            returns
              exists e1 rest.
                server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
                ~ (exists m.
                    e1 == CS.ConnNetworkEvent m /\
                    m.CL.message_value == M.TlsChangeCipherSpec)
            with _.
            (
              assert (e1 == CS.ConnNetworkEvent msg);
              assert (msg.CL.message_value == M.TlsChangeCipherSpec);
              assert_norm (CS.step_model model1 e1 == Some model1);
              assert (model2 == model1);
              assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
              assert (server_application_progress_rank server.CS.cs_model == 0);
              lemma_server_application_progress_rank_replay_lower_bound
                model2
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent1
                tail_received1
                server.CS.cs_model;
              assert (server_application_progress_rank model2 == 14);
              assert (FStar.List.Tot.length
                [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14] == 13);
              assert False
            )
          )
        | _ ->
          ());
      assert (~ (exists m.
        e1 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec));
      assert (server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        e1 ::
        [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
    )
  )

let lemma_server_no_tail_second_event_client_hello_clean
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists ch rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            rest)
=
  lemma_server_no_tail_second_event_not_ccs server;
  lemma_server_no_tail_second_event_client_hello_if_not_ccs server

let lemma_server_no_tail_third_event_select_parameters_clean
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists ch selection rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            rest)
=
  PNI.lemma_server_no_tail_log_spine server;
  lemma_server_no_tail_second_event_client_hello_clean server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
    server.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
  returns
    exists ch selection rest.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
        rest
  with _.
  (
    eliminate exists ch rest_after_ch.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        rest_after_ch
    returns
      exists ch selection rest.
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
          rest
    with _.
    (
      assert (server.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
      assert (server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        rest_after_ch);
      assert (e0 == CS.ConnLocalEvent CS.LocalStartServer);
      assert (e1 == CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }));
      assert (rest_after_ch == [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);

      assert (ST.server_end_to_end_invariant server);
      assert (CS.connection_state_raw_event_replay_consistent server);
      lemma_server_application_ready_progress_rank_zero server;
      let initial = CS.initial_model server.CS.cs_model.CS.model_config in
      assert (CS.conn_events_raw_replay
        initial
        server.CS.cs_event_log
        server.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received
        server.CS.cs_model);
      assert (server.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
      assert_norm (
        CS.conn_events_raw_replay
          initial
          (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
          server.CS.cs_wire_log.CL.raw_sent
          server.CS.cs_wire_log.CL.raw_received
          server.CS.cs_model ==
        (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
          CS.legal_event initial e0 /\
          CS.step_model initial e0 == Some model1 /\
          CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_sent
            (B.append delta_sent0 tail_sent0) /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_received
            (B.append delta_received0 tail_received0) /\
          CS.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
            tail_sent0
            tail_received0
            server.CS.cs_model));
      eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
        CS.legal_event initial e0 /\
        CS.step_model initial e0 == Some model1 /\
        CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_sent
          (B.append delta_sent0 tail_sent0) /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_received
          (B.append delta_received0 tail_received0) /\
        CS.conn_events_raw_replay
          model1
          [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
          tail_sent0
          tail_received0
          server.CS.cs_model
      returns
        exists ch selection rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            rest
      with _.
      (
        assert (initial.CS.model_control == CS.ControlNew);
        assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
        assert_norm (
          CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) ==
          Some (CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello));
        assert (CS.step_model initial e0 ==
          Some (CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello));
        assert (model1 ==
          CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello);
        assert (model1.CS.model_control ==
          CS.ControlHandshaking CS.HsAwaitingClientHello);
        assert (model1.CS.model_config == initial.CS.model_config);
        assert (model1.CS.model_config.CS.config_role == CS.ServerEndpoint);

        assert_norm (
          CS.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
            tail_sent0
            tail_received0
            server.CS.cs_model ==
          (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
            CS.legal_event model1 e1 /\
            CS.step_model model1 e1 == Some model2 /\
            CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
            Seq.equal
              tail_sent0
              (B.append delta_sent1 tail_sent1) /\
            Seq.equal
              tail_received0
              (B.append delta_received1 tail_received1) /\
            CS.conn_events_raw_replay
              model2
              [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
              tail_sent1
              tail_received1
              server.CS.cs_model));
        eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
          CS.legal_event model1 e1 /\
          CS.step_model model1 e1 == Some model2 /\
          CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
          Seq.equal
            tail_sent0
            (B.append delta_sent1 tail_sent1) /\
          Seq.equal
            tail_received0
            (B.append delta_received1 tail_received1) /\
          CS.conn_events_raw_replay
            model2
            [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
            tail_sent1
            tail_received1
            server.CS.cs_model
        returns
          exists ch selection rest.
            server.CS.cs_event_log ==
              CS.ConnLocalEvent CS.LocalStartServer ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              }) ::
              CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
              rest
        with _.
        (
          assert_norm (
            CS.step_model
              model1
              (CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              })) ==
            Some (CS.with_handshake_stage
              model1
              (CS.append_handshake_to_transcript
                ({ model1.CS.model_handshake with
                    CS.hs_client_hello = Some ch;
                    CS.hs_buffers =
                      { model1.CS.model_handshake.CS.hs_buffers with
                          CS.hb_client_hello_bytes =
                            TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                      };
                })
                (M.ClientHello ch))
              CS.HsClientHelloReceived));
          assert (CS.step_model model1 e1 ==
            Some (CS.with_handshake_stage
              model1
              (CS.append_handshake_to_transcript
                ({ model1.CS.model_handshake with
                    CS.hs_client_hello = Some ch;
                    CS.hs_buffers =
                      { model1.CS.model_handshake.CS.hs_buffers with
                          CS.hb_client_hello_bytes =
                            TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                      };
                })
                (M.ClientHello ch))
              CS.HsClientHelloReceived));
          assert (model2 ==
            CS.with_handshake_stage
              model1
              (CS.append_handshake_to_transcript
                ({ model1.CS.model_handshake with
                    CS.hs_client_hello = Some ch;
                    CS.hs_buffers =
                      { model1.CS.model_handshake.CS.hs_buffers with
                          CS.hb_client_hello_bytes =
                            TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                      };
                })
                (M.ClientHello ch))
              CS.HsClientHelloReceived);
          assert (model2.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived);
          assert (model2.CS.model_config == model1.CS.model_config);
          assert (model2.CS.model_config.CS.config_role == CS.ServerEndpoint);
          assert (model2.CS.model_handshake.CS.hs_server_selection == None);
          assert (model2.CS.model_handshake.CS.hs_keys ==
            model1.CS.model_handshake.CS.hs_keys);
          assert (model1.CS.model_handshake.CS.hs_keys ==
            initial.CS.model_handshake.CS.hs_keys);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
          assert (model2.CS.model_handshake.CS.hs_certificate == None);
          assert (model2.CS.model_handshake.CS.hs_certificate_verify_verified == false);
          assert (server_encrypted_flight_constant model2.CS.model_handshake == 5);
          assert (server_handshake_traffic_obligation_rank
            model2.CS.model_handshake.CS.hs_keys == 2);
          assert (server_application_obligation_rank
            model2.CS.model_handshake.CS.hs_keys == 3);
          assert (option_missing model2.CS.model_handshake.CS.hs_server_selection == 1);
          assert (server_application_progress_rank model2 == 13);

          assert_norm (
            CS.conn_events_raw_replay
              model2
              [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
              tail_sent1
              tail_received1
              server.CS.cs_model ==
            (exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
              CS.legal_event model2 e2 /\
              CS.step_model model2 e2 == Some model3 /\
              CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
              Seq.equal
                tail_sent1
                (B.append delta_sent2 tail_sent2) /\
              Seq.equal
                tail_received1
                (B.append delta_received2 tail_received2) /\
              CS.conn_events_raw_replay
                model3
                [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent2
                tail_received2
                server.CS.cs_model));
          eliminate exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
            CS.legal_event model2 e2 /\
            CS.step_model model2 e2 == Some model3 /\
            CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
            Seq.equal
              tail_sent1
              (B.append delta_sent2 tail_sent2) /\
            Seq.equal
              tail_received1
              (B.append delta_received2 tail_received2) /\
            CS.conn_events_raw_replay
              model3
              [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
              tail_sent2
              tail_received2
              server.CS.cs_model
          returns
            exists ch selection rest.
              server.CS.cs_event_log ==
                CS.ConnLocalEvent CS.LocalStartServer ::
                CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch);
                }) ::
                CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                rest
          with _.
          (
            match e2 with
            | CS.ConnLocalEvent local ->
              (match local with
              | CS.LocalFail err ->
                assert (e2 == CS.ConnLocalEvent (CS.LocalFail err));
                assert_norm (
                  CS.step_model model2 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                  Some (CS.fail_model model2 err));
                assert (model3.CS.model_control == CS.ControlFailed err);
                lemma_conn_events_raw_replay_from_failed_results_failed
                  model3
                  [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                  tail_sent2
                  tail_received2
                  server.CS.cs_model;
                assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
                assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                assert False
              | CS.LocalInstallTrafficKeys install ->
                lemma_server_hs_client_hello_received_install_traffic_keys_illegal model2 install;
                assert False
              | CS.LocalInstallTrafficKeysForRole role_install ->
                lemma_server_hs_client_hello_received_role_install_illegal model2 role_install;
                assert False
              | CS.LocalSelectServerParameters selection ->
                assert (e2 == CS.ConnLocalEvent (CS.LocalSelectServerParameters selection));
                assert (server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                  [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
              | CS.LocalDeriveSharedSecret shared ->
                lemma_server_hs_client_hello_received_no_selection_derive_illegal
                  model2
                  shared;
                assert False
              | _ ->
                lemma_server_hs_client_hello_received_local_event_step_none model2 local;
                assert (CS.step_model model2 e2 == None);
                assert False)
            | CS.ConnNetworkEvent msg ->
              (match msg.CL.message_value with
              | M.TlsAlert alert ->
                assert (e2 == CS.ConnNetworkEvent msg);
                assert_norm (
                  CS.step_model model2 (CS.ConnNetworkEvent msg) ==
                  Some (CS.fail_model model2 (T.AlertError alert)));
                assert (CS.step_model model2 e2 ==
                  Some (CS.fail_model model2 (T.AlertError alert)));
                assert (model3.CS.model_control == CS.ControlFailed (T.AlertError alert));
                lemma_conn_events_raw_replay_from_failed_results_failed
                  model3
                  [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                  tail_sent2
                  tail_received2
                  server.CS.cs_model;
                assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
                assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                assert False
              | M.TlsChangeCipherSpec ->
                assert (e2 == CS.ConnNetworkEvent msg);
                assert (msg.CL.message_value == M.TlsChangeCipherSpec);
                assert_norm (CS.step_model model2 (CS.ConnNetworkEvent msg) == Some model2);
                assert (CS.step_model model2 e2 == Some model2);
                assert (model3 == model2);
                assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                assert (server_application_progress_rank server.CS.cs_model == 0);
                lemma_server_application_progress_rank_replay_lower_bound
                  model3
                  [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                  tail_sent2
                  tail_received2
                  server.CS.cs_model;
                assert (server_application_progress_rank model3 == 13);
                assert_norm (FStar.List.Tot.length
                  [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14] == 12);
                assert False
              | M.TlsHandshake handshake_msg ->
                (match msg.CL.message_direction, handshake_msg with
                | CL.Sent, M.ServerHello sh ->
                  assert (e2 == CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Sent;
                    CL.message_value = M.TlsHandshake (M.ServerHello sh);
                  }));
                  lemma_server_hs_client_hello_received_no_selection_sent_server_hello_illegal
                    model2
                    sh;
                  assert False
                | _, _ ->
                  lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                    model2
                    msg;
                  assert (CS.step_model model2 e2 == None);
                  assert False)
              | M.TlsApplicationData _ ->
                lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                  model2
                  msg;
                assert (CS.step_model model2 e2 == None);
                assert False
              | M.TlsIgnoredPostHandshake _ ->
                lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                  model2
                  msg;
                assert (CS.step_model model2 e2 == None);
                assert False
              | M.TlsKeyUpdate _ ->
                lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                  model2
                  msg;
                assert (CS.step_model model2 e2 == None);
                assert False)
          )
        )
      )
    )
  )

let lemma_server_no_tail_fourth_event_derive_shared_secret_clean
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 15)
      (ensures
        exists ch selection server_shared rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
            rest)
=
  PNI.lemma_server_no_tail_log_spine server;
  lemma_server_no_tail_third_event_select_parameters_clean server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
    server.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
  returns
    exists ch selection server_shared rest.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
        rest
  with _.
  (
    eliminate exists ch selection rest_after_selection.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
        rest_after_selection
    returns
      exists ch selection server_shared rest.
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          }) ::
          CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
          rest
    with _.
    (
      assert (server.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
      assert (server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello ch);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
        rest_after_selection);
      assert (e0 == CS.ConnLocalEvent CS.LocalStartServer);
      assert (e1 == CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }));
      assert (e2 == CS.ConnLocalEvent (CS.LocalSelectServerParameters selection));
      assert (rest_after_selection ==
        [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);

      assert (ST.server_end_to_end_invariant server);
      assert (CS.connection_state_raw_event_replay_consistent server);
      lemma_server_application_ready_progress_rank_zero server;
      let initial = CS.initial_model server.CS.cs_model.CS.model_config in
      assert (CS.conn_events_raw_replay
        initial
        server.CS.cs_event_log
        server.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received
        server.CS.cs_model);
      assert (server.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
      assert_norm (
        CS.conn_events_raw_replay
          initial
          (e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
          server.CS.cs_wire_log.CL.raw_sent
          server.CS.cs_wire_log.CL.raw_received
          server.CS.cs_model ==
        (exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
          CS.legal_event initial e0 /\
          CS.step_model initial e0 == Some model1 /\
          CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_sent
            (B.append delta_sent0 tail_sent0) /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_received
            (B.append delta_received0 tail_received0) /\
          CS.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
            tail_sent0
            tail_received0
            server.CS.cs_model));
      eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
        CS.legal_event initial e0 /\
        CS.step_model initial e0 == Some model1 /\
        CS.event_raw_delta_legal initial e0 delta_sent0 delta_received0 /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_sent
          (B.append delta_sent0 tail_sent0) /\
        Seq.equal
          server.CS.cs_wire_log.CL.raw_received
          (B.append delta_received0 tail_received0) /\
        CS.conn_events_raw_replay
          model1
          [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
          tail_sent0
          tail_received0
          server.CS.cs_model
      returns
        exists ch selection server_shared rest.
          server.CS.cs_event_log ==
            CS.ConnLocalEvent CS.LocalStartServer ::
            CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch);
            }) ::
            CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
            CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
            rest
      with _.
      (
        assert (initial.CS.model_control == CS.ControlNew);
        assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
        assert_norm (
          CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) ==
          Some (CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello));
        assert (CS.step_model initial e0 ==
          Some (CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello));
        assert (model1 ==
          CS.with_handshake_stage
            initial
            initial.CS.model_handshake
            CS.HsAwaitingClientHello);
        assert (model1.CS.model_control ==
          CS.ControlHandshaking CS.HsAwaitingClientHello);
        assert (model1.CS.model_config == initial.CS.model_config);
        assert (model1.CS.model_config.CS.config_role == CS.ServerEndpoint);

        assert_norm (
          CS.conn_events_raw_replay
            model1
            [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
            tail_sent0
            tail_received0
            server.CS.cs_model ==
          (exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
            CS.legal_event model1 e1 /\
            CS.step_model model1 e1 == Some model2 /\
            CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
            Seq.equal
              tail_sent0
              (B.append delta_sent1 tail_sent1) /\
            Seq.equal
              tail_received0
              (B.append delta_received1 tail_received1) /\
            CS.conn_events_raw_replay
              model2
              [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
              tail_sent1
              tail_received1
              server.CS.cs_model));
        eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
          CS.legal_event model1 e1 /\
          CS.step_model model1 e1 == Some model2 /\
          CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
          Seq.equal
            tail_sent0
            (B.append delta_sent1 tail_sent1) /\
          Seq.equal
            tail_received0
            (B.append delta_received1 tail_received1) /\
          CS.conn_events_raw_replay
            model2
            [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
            tail_sent1
            tail_received1
            server.CS.cs_model
        returns
          exists ch selection server_shared rest.
            server.CS.cs_event_log ==
              CS.ConnLocalEvent CS.LocalStartServer ::
              CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              }) ::
              CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
              CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
              rest
        with _.
        (
          assert_norm (
            CS.step_model
              model1
              (CS.ConnNetworkEvent ({
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.ClientHello ch);
              })) ==
            Some (CS.with_handshake_stage
              model1
              (CS.append_handshake_to_transcript
                ({ model1.CS.model_handshake with
                    CS.hs_client_hello = Some ch;
                    CS.hs_buffers =
                      { model1.CS.model_handshake.CS.hs_buffers with
                          CS.hb_client_hello_bytes =
                            TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                      };
                })
                (M.ClientHello ch))
              CS.HsClientHelloReceived));
          assert (CS.step_model model1 e1 ==
            Some (CS.with_handshake_stage
              model1
              (CS.append_handshake_to_transcript
                ({ model1.CS.model_handshake with
                    CS.hs_client_hello = Some ch;
                    CS.hs_buffers =
                      { model1.CS.model_handshake.CS.hs_buffers with
                          CS.hb_client_hello_bytes =
                            TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                      };
                })
                (M.ClientHello ch))
              CS.HsClientHelloReceived));
          assert (model2 ==
            CS.with_handshake_stage
              model1
              (CS.append_handshake_to_transcript
                ({ model1.CS.model_handshake with
                    CS.hs_client_hello = Some ch;
                    CS.hs_buffers =
                      { model1.CS.model_handshake.CS.hs_buffers with
                          CS.hb_client_hello_bytes =
                            TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                      };
                })
                (M.ClientHello ch))
              CS.HsClientHelloReceived);
          assert (model2.CS.model_control ==
            CS.ControlHandshaking CS.HsClientHelloReceived);
          assert (model2.CS.model_config == model1.CS.model_config);
          assert (model2.CS.model_config.CS.config_role == CS.ServerEndpoint);
          assert (model2.CS.model_handshake.CS.hs_server_selection == None);
          assert (model2.CS.model_handshake.CS.hs_keys ==
            model1.CS.model_handshake.CS.hs_keys);
          assert (model1.CS.model_handshake.CS.hs_keys ==
            initial.CS.model_handshake.CS.hs_keys);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
          assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
          assert (model2.CS.model_handshake.CS.hs_certificate == None);
          assert (model2.CS.model_handshake.CS.hs_certificate_verify_verified == false);

          assert_norm (
            CS.conn_events_raw_replay
              model2
              [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
              tail_sent1
              tail_received1
              server.CS.cs_model ==
            (exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
              CS.legal_event model2 e2 /\
              CS.step_model model2 e2 == Some model3 /\
              CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
              Seq.equal
                tail_sent1
                (B.append delta_sent2 tail_sent2) /\
              Seq.equal
                tail_received1
                (B.append delta_received2 tail_received2) /\
              CS.conn_events_raw_replay
                model3
                [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent2
                tail_received2
                server.CS.cs_model));
          eliminate exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
            CS.legal_event model2 e2 /\
            CS.step_model model2 e2 == Some model3 /\
            CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
            Seq.equal
              tail_sent1
              (B.append delta_sent2 tail_sent2) /\
            Seq.equal
              tail_received1
              (B.append delta_received2 tail_received2) /\
            CS.conn_events_raw_replay
              model3
              [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
              tail_sent2
              tail_received2
              server.CS.cs_model
          returns
            exists ch selection server_shared rest.
              server.CS.cs_event_log ==
                CS.ConnLocalEvent CS.LocalStartServer ::
                CS.ConnNetworkEvent ({
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.ClientHello ch);
                }) ::
                CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                rest
          with _.
          (
            assert_norm (
              CS.step_model
                model2
                (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
              Some (CS.with_handshake_stage
                model2
                { model2.CS.model_handshake with
                    CS.hs_server_selection = Some selection;
                    CS.hs_client_hello =
                      Some selection.CS.server_selected_client_hello;
                }
                CS.HsClientHelloReceived));
            assert (CS.step_model model2 e2 ==
              Some (CS.with_handshake_stage
                model2
                { model2.CS.model_handshake with
                    CS.hs_server_selection = Some selection;
                    CS.hs_client_hello =
                      Some selection.CS.server_selected_client_hello;
                }
                CS.HsClientHelloReceived));
            assert (model3 ==
              CS.with_handshake_stage
                model2
                { model2.CS.model_handshake with
                    CS.hs_server_selection = Some selection;
                    CS.hs_client_hello =
                      Some selection.CS.server_selected_client_hello;
                }
                CS.HsClientHelloReceived);
            assert (model3.CS.model_control ==
              CS.ControlHandshaking CS.HsClientHelloReceived);
            assert (model3.CS.model_config == model2.CS.model_config);
            assert (model3.CS.model_config.CS.config_role == CS.ServerEndpoint);
            assert (model3.CS.model_handshake.CS.hs_server_selection ==
              Some selection);
            assert (model3.CS.model_handshake.CS.hs_keys ==
              model2.CS.model_handshake.CS.hs_keys);
            assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
            assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
            assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
            assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
            assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
            assert (model3.CS.model_handshake.CS.hs_certificate == None);
            assert (model3.CS.model_handshake.CS.hs_certificate_verify_verified == false);
            assert (server_encrypted_flight_constant model3.CS.model_handshake == 5);
            assert (server_handshake_traffic_obligation_rank
              model3.CS.model_handshake.CS.hs_keys == 2);
            assert (server_application_obligation_rank
              model3.CS.model_handshake.CS.hs_keys == 3);
            assert (option_missing model3.CS.model_handshake.CS.hs_server_selection == 0);
            lemma_server_application_progress_rank_client_hello_received_selected model3;
            assert (server_application_progress_rank model3 == 12);

            assert_norm (
              CS.conn_events_raw_replay
                model3
                [e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent2
                tail_received2
                server.CS.cs_model ==
              (exists model4 delta_sent3 delta_received3 tail_sent3 tail_received3.
                CS.legal_event model3 e3 /\
                CS.step_model model3 e3 == Some model4 /\
                CS.event_raw_delta_legal model3 e3 delta_sent3 delta_received3 /\
                Seq.equal
                  tail_sent2
                  (B.append delta_sent3 tail_sent3) /\
                Seq.equal
                  tail_received2
                  (B.append delta_received3 tail_received3) /\
                CS.conn_events_raw_replay
                  model4
                  [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                  tail_sent3
                  tail_received3
                  server.CS.cs_model));
            eliminate exists model4 delta_sent3 delta_received3 tail_sent3 tail_received3.
              CS.legal_event model3 e3 /\
              CS.step_model model3 e3 == Some model4 /\
              CS.event_raw_delta_legal model3 e3 delta_sent3 delta_received3 /\
              Seq.equal
                tail_sent2
                (B.append delta_sent3 tail_sent3) /\
              Seq.equal
                tail_received2
                (B.append delta_received3 tail_received3) /\
              CS.conn_events_raw_replay
                model4
                [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                tail_sent3
                tail_received3
                server.CS.cs_model
            returns
              exists ch selection server_shared rest.
                server.CS.cs_event_log ==
                  CS.ConnLocalEvent CS.LocalStartServer ::
                  CS.ConnNetworkEvent ({
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello ch);
                  }) ::
                  CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                  CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                  rest
            with _.
            (
              match e3 with
              | CS.ConnLocalEvent local ->
                (match local with
                | CS.LocalFail err ->
                  assert (e3 == CS.ConnLocalEvent (CS.LocalFail err));
                  assert_norm (
                    CS.step_model model3 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                    Some (CS.fail_model model3 err));
                  assert (model4.CS.model_control == CS.ControlFailed err);
                  lemma_conn_events_raw_replay_from_failed_results_failed
                    model4
                    [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                    tail_sent3
                    tail_received3
                    server.CS.cs_model;
                  assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
                  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                  assert False
                | CS.LocalInstallTrafficKeys install ->
                  lemma_server_hs_client_hello_received_install_traffic_keys_illegal model3 install;
                  assert False
                | CS.LocalInstallTrafficKeysForRole role_install ->
                  lemma_server_hs_client_hello_received_role_install_illegal model3 role_install;
                  assert False
                | CS.LocalSelectServerParameters selection' ->
                  assert (e3 == CS.ConnLocalEvent (CS.LocalSelectServerParameters selection'));
                  assert_norm (
                    CS.step_model
                      model3
                      (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection')) ==
                    Some (CS.with_handshake_stage
                      model3
                      { model3.CS.model_handshake with
                          CS.hs_server_selection = Some selection';
                          CS.hs_client_hello =
                            Some selection'.CS.server_selected_client_hello;
                      }
                      CS.HsClientHelloReceived));
                  assert (CS.step_model model3 e3 ==
                    Some (CS.with_handshake_stage
                      model3
                      { model3.CS.model_handshake with
                          CS.hs_server_selection = Some selection';
                          CS.hs_client_hello =
                            Some selection'.CS.server_selected_client_hello;
                      }
                      CS.HsClientHelloReceived));
                  assert (model4 ==
                    CS.with_handshake_stage
                      model3
                      { model3.CS.model_handshake with
                          CS.hs_server_selection = Some selection';
                          CS.hs_client_hello =
                            Some selection'.CS.server_selected_client_hello;
                      }
                      CS.HsClientHelloReceived);
                  assert (model4.CS.model_control ==
                    CS.ControlHandshaking CS.HsClientHelloReceived);
                  assert (model4.CS.model_config == model3.CS.model_config);
                  assert (model4.CS.model_config.CS.config_role == CS.ServerEndpoint);
                  assert (model4.CS.model_handshake.CS.hs_server_selection ==
                    Some selection');
                  assert (model4.CS.model_handshake.CS.hs_keys ==
                    model3.CS.model_handshake.CS.hs_keys);
                  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
                  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
                  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
                  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
                  assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
                  assert (model4.CS.model_handshake.CS.hs_certificate == None);
                  assert (model4.CS.model_handshake.CS.hs_certificate_verify_verified == false);
                  assert (server_encrypted_flight_constant model4.CS.model_handshake == 5);
                  assert (server_handshake_traffic_obligation_rank
                    model4.CS.model_handshake.CS.hs_keys == 2);
                  assert (server_application_obligation_rank
                    model4.CS.model_handshake.CS.hs_keys == 3);
                  assert (option_missing model4.CS.model_handshake.CS.hs_server_selection == 0);
                  lemma_server_application_progress_rank_client_hello_received_selected model4;
                  assert (server_application_progress_rank model4 == 12);
                  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                  assert (server_application_progress_rank server.CS.cs_model == 0);
                  lemma_server_application_progress_rank_replay_lower_bound
                    model4
                    [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                    tail_sent3
                    tail_received3
                    server.CS.cs_model;
                  assert_norm (FStar.List.Tot.length
                    [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14] == 11);
                  assert False
                | CS.LocalDeriveSharedSecret server_shared ->
                  assert (e3 == CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared));
                  assert (server.CS.cs_event_log ==
                    CS.ConnLocalEvent CS.LocalStartServer ::
                    CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Received;
                      CL.message_value = M.TlsHandshake (M.ClientHello ch);
                    }) ::
                    CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                    CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                    [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
                | _ ->
                  lemma_server_hs_client_hello_received_local_event_step_none model3 local;
                  assert (CS.step_model model3 e3 == None);
                  assert False)
              | CS.ConnNetworkEvent msg ->
                (match msg.CL.message_value with
                | M.TlsAlert alert ->
                  assert (e3 == CS.ConnNetworkEvent msg);
                  assert_norm (
                    CS.step_model model3 (CS.ConnNetworkEvent msg) ==
                    Some (CS.fail_model model3 (T.AlertError alert)));
                  assert (CS.step_model model3 e3 ==
                    Some (CS.fail_model model3 (T.AlertError alert)));
                  assert (model4.CS.model_control == CS.ControlFailed (T.AlertError alert));
                  lemma_conn_events_raw_replay_from_failed_results_failed
                    model4
                    [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                    tail_sent3
                    tail_received3
                    server.CS.cs_model;
                  assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
                  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                  assert False
                | M.TlsChangeCipherSpec ->
                  assert (e3 == CS.ConnNetworkEvent msg);
                  assert (msg.CL.message_value == M.TlsChangeCipherSpec);
                  assert_norm (CS.step_model model3 (CS.ConnNetworkEvent msg) == Some model3);
                  assert (CS.step_model model3 e3 == Some model3);
                  assert (model4 == model3);
                  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                  assert (server_application_progress_rank server.CS.cs_model == 0);
                  lemma_server_application_progress_rank_replay_lower_bound
                    model4
                    [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                    tail_sent3
                    tail_received3
                    server.CS.cs_model;
                  assert (server_application_progress_rank model4 == 12);
                  assert_norm (FStar.List.Tot.length
                    [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14] == 11);
                  assert False
                | M.TlsHandshake handshake_msg ->
                  (match msg.CL.message_direction, handshake_msg with
                  | CL.Sent, M.ServerHello sh ->
                    assert (e3 == CS.ConnNetworkEvent ({
                      CL.message_direction = CL.Sent;
                      CL.message_value = M.TlsHandshake (M.ServerHello sh);
                    }));
                    lemma_server_hs_client_hello_received_no_shared_sent_server_hello_illegal
                      model3
                      sh;
                    assert False
                  | _, _ ->
                    lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                      model3
                      msg;
                    assert (CS.step_model model3 e3 == None);
                    assert False)
                | M.TlsApplicationData _ ->
                  lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                    model3
                    msg;
                  assert (CS.step_model model3 e3 == None);
                  assert False
                | M.TlsIgnoredPostHandshake _ ->
                  lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                    model3
                    msg;
                  assert (CS.step_model model3 e3 == None);
                  assert False
                | M.TlsKeyUpdate _ ->
                  lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                    model3
                    msg;
                  assert (CS.step_model model3 e3 == None);
                  assert False)
            )
          )
        )
      )
    )
  )

(**
  This lemma nests five levels of role-local case analysis (one per event
  after [LocalStartServer]), so its final "eliminate exists" step -- deriving
  the fifth event's raw-replay witness from [PWR.lemma_conn_events_raw_replay_head]
  -- sits inside a much larger elaboration/typing context than the earlier
  no-tail inversion lemmas.  The default rlimit is enough for every other
  proof obligation in this lemma but not quite enough at that final depth;
  bump it locally rather than growing it project-wide.
**)
#push-options "--z3rlimit 10"
let lemma_server_no_tail_fifth_event_server_hello_clean
  (server:CS.connection_state)
  : Lemma
     (requires
       SD.server_driver_application_ready server /\
       FStar.List.Tot.length server.CS.cs_event_log == 15)
     (ensures
       exists ch selection server_shared sh rest.
         server.CS.cs_event_log ==
           CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello sh);
           }) ::
           rest)
=
  PNI.lemma_server_no_tail_log_spine server;
  lemma_server_no_tail_fourth_event_derive_shared_secret_clean server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
    server.CS.cs_event_log ==
     [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
  returns
    exists ch selection server_shared sh rest.
     server.CS.cs_event_log ==
       CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello ch);
       }) ::
       CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ServerHello sh);
       }) ::
       rest
  with _.
  (
    eliminate exists ch selection server_shared rest_after_shared.
     server.CS.cs_event_log ==
       CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello ch);
       }) ::
       CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
       rest_after_shared
    returns
     exists ch selection server_shared sh rest.
       server.CS.cs_event_log ==
         CS.ConnLocalEvent CS.LocalStartServer ::
         CS.ConnNetworkEvent ({
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.ClientHello ch);
         }) ::
         CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
         CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
         CS.ConnNetworkEvent ({
           CL.message_direction = CL.Sent;
           CL.message_value = M.TlsHandshake (M.ServerHello sh);
         }) ::
         rest
    with _.
    (
     assert (server.CS.cs_event_log ==
       e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);
     assert (server.CS.cs_event_log ==
       CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello ch);
       }) ::
       CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
       rest_after_shared);
     assert (e0 == CS.ConnLocalEvent CS.LocalStartServer);
     assert (e1 == CS.ConnNetworkEvent ({
       CL.message_direction = CL.Received;
       CL.message_value = M.TlsHandshake (M.ClientHello ch);
     }));
     assert (e2 == CS.ConnLocalEvent (CS.LocalSelectServerParameters selection));
     assert (e3 == CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared));
     assert (rest_after_shared ==
       [e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]);

     assert (ST.server_end_to_end_invariant server);
     assert (CS.connection_state_raw_event_replay_consistent server);
     lemma_server_application_ready_progress_rank_zero server;
     let initial = CS.initial_model server.CS.cs_model.CS.model_config in
     assert (CS.conn_events_raw_replay
       initial
       server.CS.cs_event_log
       server.CS.cs_wire_log.CL.raw_sent
       server.CS.cs_wire_log.CL.raw_received
       server.CS.cs_model);
     assert (server.CS.cs_event_log ==
       CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello ch);
       }) ::
       CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
       e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: e14 :: []);
     PWR.lemma_conn_events_raw_replay_head
       initial
       (CS.ConnLocalEvent CS.LocalStartServer)
       [ e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
       server.CS.cs_wire_log.CL.raw_sent
       server.CS.cs_wire_log.CL.raw_received
       server.CS.cs_model;
     eliminate exists model1 delta_sent0 delta_received0 tail_sent0 tail_received0.
       CS.legal_event initial (CS.ConnLocalEvent CS.LocalStartServer) /\
       CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) == Some model1 /\
       CS.event_raw_delta_legal initial (CS.ConnLocalEvent CS.LocalStartServer) delta_sent0 delta_received0 /\
       Seq.equal
         server.CS.cs_wire_log.CL.raw_sent
         (B.append delta_sent0 tail_sent0) /\
       Seq.equal
         server.CS.cs_wire_log.CL.raw_received
         (B.append delta_received0 tail_received0) /\
       CS.conn_events_raw_replay
         model1
         [ e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
         tail_sent0
         tail_received0
         server.CS.cs_model
     returns
       exists ch selection server_shared sh rest.
         server.CS.cs_event_log ==
           CS.ConnLocalEvent CS.LocalStartServer ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch);
           }) ::
           CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello sh);
           }) ::
           rest
     with _.
     (
       assert (initial.CS.model_control == CS.ControlNew);
       assert (initial.CS.model_config.CS.config_role == CS.ServerEndpoint);
       assert_norm (
         CS.step_model initial (CS.ConnLocalEvent CS.LocalStartServer) ==
         Some (CS.with_handshake_stage
           initial
           initial.CS.model_handshake
           CS.HsAwaitingClientHello));
       assert (model1 ==
         CS.with_handshake_stage
           initial
           initial.CS.model_handshake
           CS.HsAwaitingClientHello);
       assert (model1.CS.model_control ==
         CS.ControlHandshaking CS.HsAwaitingClientHello);
       assert (model1.CS.model_config == initial.CS.model_config);
       assert (model1.CS.model_config.CS.config_role == CS.ServerEndpoint);

       PWR.lemma_conn_events_raw_replay_head
         model1
         e1
         [ e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
         tail_sent0
         tail_received0
         server.CS.cs_model;
       eliminate exists model2 delta_sent1 delta_received1 tail_sent1 tail_received1.
         CS.legal_event model1 e1 /\
         CS.step_model model1 e1 == Some model2 /\
         CS.event_raw_delta_legal model1 e1 delta_sent1 delta_received1 /\
         Seq.equal tail_sent0 (B.append delta_sent1 tail_sent1) /\
         Seq.equal tail_received0 (B.append delta_received1 tail_received1) /\
         CS.conn_events_raw_replay
           model2
           [ e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
           tail_sent1
           tail_received1
           server.CS.cs_model
       returns
         exists ch selection server_shared sh rest.
           server.CS.cs_event_log ==
             CS.ConnLocalEvent CS.LocalStartServer ::
             CS.ConnNetworkEvent ({
               CL.message_direction = CL.Received;
               CL.message_value = M.TlsHandshake (M.ClientHello ch);
             }) ::
             CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
             CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
             CS.ConnNetworkEvent ({
               CL.message_direction = CL.Sent;
               CL.message_value = M.TlsHandshake (M.ServerHello sh);
             }) ::
             rest
       with _.
       (
         assert_norm (
           CS.step_model
             model1
             (CS.ConnNetworkEvent ({
               CL.message_direction = CL.Received;
               CL.message_value = M.TlsHandshake (M.ClientHello ch);
             })) ==
           Some (CS.with_handshake_stage
             model1
             (CS.append_handshake_to_transcript
               ({ model1.CS.model_handshake with
                   CS.hs_client_hello = Some ch;
                   CS.hs_buffers =
                     { model1.CS.model_handshake.CS.hs_buffers with
                         CS.hb_client_hello_bytes =
                           TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                     };
               })
               (M.ClientHello ch))
             CS.HsClientHelloReceived));
         assert (CS.step_model model1 e1 ==
           Some (CS.with_handshake_stage
             model1
             (CS.append_handshake_to_transcript
               ({ model1.CS.model_handshake with
                   CS.hs_client_hello = Some ch;
                   CS.hs_buffers =
                     { model1.CS.model_handshake.CS.hs_buffers with
                         CS.hb_client_hello_bytes =
                           TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                     };
               })
               (M.ClientHello ch))
             CS.HsClientHelloReceived));
         assert (model2 ==
           CS.with_handshake_stage
             model1
             (CS.append_handshake_to_transcript
               ({ model1.CS.model_handshake with
                   CS.hs_client_hello = Some ch;
                   CS.hs_buffers =
                     { model1.CS.model_handshake.CS.hs_buffers with
                         CS.hb_client_hello_bytes =
                           TLS13.Wire.Spec.serialize_handshake (M.ClientHello ch);
                     };
               })
               (M.ClientHello ch))
             CS.HsClientHelloReceived);
         assert (model2.CS.model_control ==
           CS.ControlHandshaking CS.HsClientHelloReceived);
         assert (model2.CS.model_config == model1.CS.model_config);
         assert (model2.CS.model_config.CS.config_role == CS.ServerEndpoint);
         assert (model2.CS.model_handshake.CS.hs_server_selection == None);
         assert (model2.CS.model_handshake.CS.hs_keys ==
           model1.CS.model_handshake.CS.hs_keys);
         assert (model1.CS.model_handshake.CS.hs_keys ==
           initial.CS.model_handshake.CS.hs_keys);
         assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
         assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
         assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
         assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
         assert (model2.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
         assert (model2.CS.model_handshake.CS.hs_certificate == None);
         assert (model2.CS.model_handshake.CS.hs_certificate_verify_verified == false);

         PWR.lemma_conn_events_raw_replay_head
           model2
           e2
           [ e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
           tail_sent1
           tail_received1
           server.CS.cs_model;
         eliminate exists model3 delta_sent2 delta_received2 tail_sent2 tail_received2.
           CS.legal_event model2 e2 /\
           CS.step_model model2 e2 == Some model3 /\
           CS.event_raw_delta_legal model2 e2 delta_sent2 delta_received2 /\
           Seq.equal tail_sent1 (B.append delta_sent2 tail_sent2) /\
           Seq.equal tail_received1 (B.append delta_received2 tail_received2) /\
           CS.conn_events_raw_replay
             model3
             [ e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
             tail_sent2
             tail_received2
             server.CS.cs_model
         returns
           exists ch selection server_shared sh rest.
             server.CS.cs_event_log ==
               CS.ConnLocalEvent CS.LocalStartServer ::
               CS.ConnNetworkEvent ({
                 CL.message_direction = CL.Received;
                 CL.message_value = M.TlsHandshake (M.ClientHello ch);
               }) ::
               CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
               CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
               CS.ConnNetworkEvent ({
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.ServerHello sh);
               }) ::
               rest
         with _.
         (
           assert_norm (
             CS.step_model
               model2
               (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
             Some (CS.with_handshake_stage
               model2
               { model2.CS.model_handshake with
                   CS.hs_server_selection = Some selection;
                   CS.hs_client_hello =
                     Some selection.CS.server_selected_client_hello;
               }
               CS.HsClientHelloReceived));
           assert (CS.step_model model2 e2 ==
             Some (CS.with_handshake_stage
               model2
               { model2.CS.model_handshake with
                   CS.hs_server_selection = Some selection;
                   CS.hs_client_hello =
                     Some selection.CS.server_selected_client_hello;
               }
               CS.HsClientHelloReceived));
           assert (model3 ==
             CS.with_handshake_stage
               model2
               { model2.CS.model_handshake with
                   CS.hs_server_selection = Some selection;
                   CS.hs_client_hello =
                     Some selection.CS.server_selected_client_hello;
               }
               CS.HsClientHelloReceived);
           assert (model3.CS.model_control ==
             CS.ControlHandshaking CS.HsClientHelloReceived);
           assert (model3.CS.model_config == model2.CS.model_config);
           assert (model3.CS.model_config.CS.config_role == CS.ServerEndpoint);
           assert (model3.CS.model_handshake.CS.hs_server_selection ==
             Some selection);
           assert (model3.CS.model_handshake.CS.hs_keys ==
             model2.CS.model_handshake.CS.hs_keys);
           assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == None);
           assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
           assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
           assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
           assert (model3.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
           assert (model3.CS.model_handshake.CS.hs_certificate == None);
           assert (model3.CS.model_handshake.CS.hs_certificate_verify_verified == false);

           PWR.lemma_conn_events_raw_replay_head
             model3
             e3
             [ e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
             tail_sent2
             tail_received2
             server.CS.cs_model;
           eliminate exists model4 delta_sent3 delta_received3 tail_sent3 tail_received3.
             CS.legal_event model3 e3 /\
             CS.step_model model3 e3 == Some model4 /\
             CS.event_raw_delta_legal model3 e3 delta_sent3 delta_received3 /\
             Seq.equal tail_sent2 (B.append delta_sent3 tail_sent3) /\
             Seq.equal tail_received2 (B.append delta_received3 tail_received3) /\
             CS.conn_events_raw_replay
               model4
               [ e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
               tail_sent3
               tail_received3
               server.CS.cs_model
           returns
             exists ch selection server_shared sh rest.
               server.CS.cs_event_log ==
                 CS.ConnLocalEvent CS.LocalStartServer ::
                 CS.ConnNetworkEvent ({
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.ClientHello ch);
                 }) ::
                 CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                 CS.ConnNetworkEvent ({
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.ServerHello sh);
                 }) ::
                 rest
           with _.
           (
             lemma_server_hs_client_hello_received_derive_shared_secret_step
               model3
               server_shared;
             assert (CS.step_model model3 e3 ==
               Some (CS.derive_shared_secret_model
                 model3
                 model3.CS.model_handshake
                 server_shared));
             assert (model4 ==
               CS.derive_shared_secret_model
                 model3
                 model3.CS.model_handshake
                 server_shared);
             assert (model4.CS.model_control ==
               CS.ControlHandshaking CS.HsClientHelloReceived);
             assert (model4.CS.model_config == model3.CS.model_config);
             assert (model4.CS.model_config.CS.config_role == CS.ServerEndpoint);
             assert (model4.CS.model_handshake.CS.hs_server_selection ==
               Some selection);
             assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
               Some server_shared);
             assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
             assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
             assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
             assert (model4.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
             assert (model4.CS.model_handshake.CS.hs_certificate == None);
             assert (model4.CS.model_handshake.CS.hs_certificate_verify_verified == false);
             assert (server_encrypted_flight_constant model4.CS.model_handshake == 5);
             assert (server_handshake_traffic_obligation_rank
               model4.CS.model_handshake.CS.hs_keys == 2);
             assert (server_application_obligation_rank
               model4.CS.model_handshake.CS.hs_keys == 2);
             assert (option_missing model4.CS.model_handshake.CS.hs_server_selection == 0);
             lemma_server_application_progress_rank_client_hello_received_selected_shared model4;
             assert (server_application_progress_rank model4 == 11);

             PWR.lemma_conn_events_raw_replay_head
               model4
               e4
               [ e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
               tail_sent3
               tail_received3
               server.CS.cs_model;
             eliminate exists model5 delta_sent4 delta_received4 tail_sent4 tail_received4.
               CS.legal_event model4 e4 /\
               CS.step_model model4 e4 == Some model5 /\
               CS.event_raw_delta_legal model4 e4 delta_sent4 delta_received4 /\
               Seq.equal tail_sent3 (B.append delta_sent4 tail_sent4) /\
               Seq.equal tail_received3 (B.append delta_received4 tail_received4) /\
               CS.conn_events_raw_replay
                 model5
                 [ e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]
                 tail_sent4
                 tail_received4
                 server.CS.cs_model
             returns
               exists ch selection server_shared sh rest.
                 server.CS.cs_event_log ==
                   CS.ConnLocalEvent CS.LocalStartServer ::
                   CS.ConnNetworkEvent ({
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsHandshake (M.ClientHello ch);
                   }) ::
                   CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                   CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                   CS.ConnNetworkEvent ({
                     CL.message_direction = CL.Sent;
                     CL.message_value = M.TlsHandshake (M.ServerHello sh);
                   }) ::
                   rest
             with _.
             (
               match e4 with
               | CS.ConnLocalEvent local ->
                 (match local with
                 | CS.LocalFail err ->
                   assert (e4 == CS.ConnLocalEvent (CS.LocalFail err));
                   assert_norm (
                     CS.step_model model4 (CS.ConnLocalEvent (CS.LocalFail err)) ==
                     Some (CS.fail_model model4 err));
                   assert (model5.CS.model_control == CS.ControlFailed err);
                   lemma_conn_events_raw_replay_from_failed_results_failed
                     model5
                     [e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                     tail_sent4
                     tail_received4
                     server.CS.cs_model;
                   assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
                   assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                   assert False
                 | CS.LocalInstallTrafficKeys install ->
                   lemma_server_hs_client_hello_received_install_traffic_keys_illegal
                     model4
                     install;
                   assert False
                 | CS.LocalInstallTrafficKeysForRole role_install ->
                   lemma_server_hs_client_hello_received_role_install_illegal
                     model4
                     role_install;
                   assert False
                 | CS.LocalSelectServerParameters selection' ->
                   lemma_server_hs_client_hello_received_has_shared_select_illegal
                     model4
                     selection';
                   assert False
                 | CS.LocalDeriveSharedSecret shared' ->
                   assert (e4 == CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared'));
                   lemma_server_hs_client_hello_received_derive_shared_secret_step
                     model4
                     shared';
                   assert (model5 ==
                     CS.derive_shared_secret_model
                       model4
                       model4.CS.model_handshake
                       shared');
                   assert (model5.CS.model_control ==
                     CS.ControlHandshaking CS.HsClientHelloReceived);
                   assert (model5.CS.model_config == model4.CS.model_config);
                   assert (model5.CS.model_config.CS.config_role == CS.ServerEndpoint);
                   assert (model5.CS.model_handshake.CS.hs_server_selection ==
                     Some selection);
                   assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
                     Some shared');
                   assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic == None);
                   assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic == None);
                   assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
                   assert (model5.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
                   assert (model5.CS.model_handshake.CS.hs_certificate == None);
                   assert (model5.CS.model_handshake.CS.hs_certificate_verify_verified == false);
                   assert (server_encrypted_flight_constant model5.CS.model_handshake == 5);
                   assert (server_handshake_traffic_obligation_rank
                     model5.CS.model_handshake.CS.hs_keys == 2);
                   assert (server_application_obligation_rank
                     model5.CS.model_handshake.CS.hs_keys == 2);
                   assert (option_missing model5.CS.model_handshake.CS.hs_server_selection == 0);
                   lemma_server_application_progress_rank_client_hello_received_selected_shared model5;
                   assert (server_application_progress_rank model5 == 11);
                   assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                   assert (server_application_progress_rank server.CS.cs_model == 0);
                   lemma_server_application_progress_rank_replay_lower_bound
                     model5
                     [e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                     tail_sent4
                     tail_received4
                     server.CS.cs_model;
                   assert_norm (FStar.List.Tot.length
                     [e5; e6; e7; e8; e9; e10; e11; e12; e13; e14] == 10);
                   assert False
                 | _ ->
                   lemma_server_hs_client_hello_received_local_event_step_none
                     model4
                     local;
                   assert (CS.step_model model4 e4 == None);
                   assert False)
               | CS.ConnNetworkEvent msg ->
                 (match msg.CL.message_value with
                 | M.TlsAlert alert ->
                   assert (e4 == CS.ConnNetworkEvent msg);
                   assert_norm (
                     CS.step_model model4 (CS.ConnNetworkEvent msg) ==
                     Some (CS.fail_model model4 (T.AlertError alert)));
                   assert (model5.CS.model_control == CS.ControlFailed (T.AlertError alert));
                   lemma_conn_events_raw_replay_from_failed_results_failed
                     model5
                     [e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                     tail_sent4
                     tail_received4
                     server.CS.cs_model;
                   assert (CS.ControlFailed? server.CS.cs_model.CS.model_control);
                   assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                   assert False
                 | M.TlsChangeCipherSpec ->
                   assert (e4 == CS.ConnNetworkEvent msg);
                   assert (msg.CL.message_value == M.TlsChangeCipherSpec);
                   assert_norm (CS.step_model model4 (CS.ConnNetworkEvent msg) == Some model4);
                   assert (model5 == model4);
                   assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
                   assert (server_application_progress_rank server.CS.cs_model == 0);
                   lemma_server_application_progress_rank_replay_lower_bound
                     model5
                     [e5; e6; e7; e8; e9; e10; e11; e12; e13; e14]
                     tail_sent4
                     tail_received4
                     server.CS.cs_model;
                   assert (server_application_progress_rank model5 == 11);
                   assert_norm (FStar.List.Tot.length
                     [e5; e6; e7; e8; e9; e10; e11; e12; e13; e14] == 10);
                   assert False
                 | M.TlsHandshake handshake_msg ->
                   (match msg.CL.message_direction, handshake_msg with
                   | CL.Sent, M.ServerHello sh ->
                     assert (e4 == CS.ConnNetworkEvent ({
                       CL.message_direction = CL.Sent;
                       CL.message_value = M.TlsHandshake (M.ServerHello sh);
                     }));
                     assert (server.CS.cs_event_log ==
                       CS.ConnLocalEvent CS.LocalStartServer ::
                       CS.ConnNetworkEvent ({
                         CL.message_direction = CL.Received;
                         CL.message_value = M.TlsHandshake (M.ClientHello ch);
                       }) ::
                       CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
                       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
                       CS.ConnNetworkEvent ({
                         CL.message_direction = CL.Sent;
                         CL.message_value = M.TlsHandshake (M.ServerHello sh);
                       }) ::
                       [e5; e6; e7; e8; e9; e10; e11; e12; e13; e14])
                   | _, _ ->
                     lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                       model4
                       msg;
                     assert (CS.step_model model4 e4 == None);
                     assert False)
                 | M.TlsApplicationData _ ->
                   lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                     model4
                     msg;
                   assert (CS.step_model model4 e4 == None);
                   assert False
                 | M.TlsIgnoredPostHandshake _ ->
                   lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                     model4
                     msg;
                   assert (CS.step_model model4 e4 == None);
                   assert False
                 | M.TlsKeyUpdate _ ->
                   lemma_server_hs_client_hello_received_non_server_hello_network_step_none
                     model4
                     msg;
                   assert (CS.step_model model4 e4 == None);
                   assert False)
             )
           )
         )
       )
     )
    )
  )
#pop-options

let lemma_server_no_tail_desired_shape_start_spine
  (server:CS.connection_state)
  : Lemma
     (requires server_no_tail_desired_shape server)
     (ensures server_no_tail_start_spine server)
=
  eliminate exists
   (ch:M.client_hello)
   (selection:CS.server_handshake_selection)
   (server_shared:C.x25519_shared_secret)
   (sh:M.server_hello)
   (server_material:CS.traffic_key_material)
   (sent_msg0:M.handshake_msg)
   (sent_msg1:M.handshake_msg)
   (server_auth_skip:CS.local_event)
   (sent_msg2:M.handshake_msg)
   (sent_msg3:M.handshake_msg)
   (server_app_write_material:CS.traffic_key_material)
   (received_msg4:M.handshake_msg)
   (cf:M.finished)
   (server_app_read_material:CS.traffic_key_material).
   received_msg4 == M.Finished cf /\
   server.CS.cs_event_log ==
     FStar.List.Tot.append
       (PWSeg.server_cleartext_handshake_prefix_events
         ch
          selection
          server_shared
          sh)
        (PWL.server_protected_handshake_contiguous_replay_events
          server_material
          sent_msg0
          sent_msg1
          server_auth_skip
          sent_msg2
          sent_msg3
          server_app_write_material
          received_msg4
          [
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = server_app_read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
          ])

  returns
    server_no_tail_start_spine server
  with _.
  (
    let e1 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      } in
    let e2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
    let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
    let e4 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello sh);
      } in
    let e5 =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_material;
          };
        }) in
    let e6 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake sent_msg0;
      } in
    let e7 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake sent_msg1;
      } in
    let e8 = CS.ConnLocalEvent server_auth_skip in
    let e9 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake sent_msg2;
      } in
    let e10 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake sent_msg3;
      } in
    let e11 =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_app_write_material;
          };
        }) in
    let e12 =
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake received_msg4;
      } in
    let e13 =
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = server_app_read_material;
          };
        }) in
    let e14 = CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf) in
    assert_norm
      (FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (PWL.server_protected_handshake_contiguous_replay_events
          server_material
          sent_msg0
          sent_msg1
          server_auth_skip
          sent_msg2
          sent_msg3
          server_app_write_material
          received_msg4
          [
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = server_app_read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
          ]) ==
       [ CS.ConnLocalEvent CS.LocalStartServer;
         e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ]);
    assert (server.CS.cs_event_log ==
      [ CS.ConnLocalEvent CS.LocalStartServer;
        e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14 ])
  )

let lemma_server_no_tail_desired_shape_length
  (server:CS.connection_state)
  : Lemma
      (requires server_no_tail_desired_shape server)
      (ensures FStar.List.Tot.length server.CS.cs_event_log == 15)
=
  eliminate exists
    (ch:M.client_hello)
    (selection:CS.server_handshake_selection)
    (server_shared:C.x25519_shared_secret)
    (sh:M.server_hello)
    (server_material:CS.traffic_key_material)
    (sent_msg0:M.handshake_msg)
    (sent_msg1:M.handshake_msg)
    (server_auth_skip:CS.local_event)
    (sent_msg2:M.handshake_msg)
    (sent_msg3:M.handshake_msg)
    (server_app_write_material:CS.traffic_key_material)
    (received_msg4:M.handshake_msg)
    (cf:M.finished)
    (server_app_read_material:CS.traffic_key_material).
    received_msg4 == M.Finished cf /\
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (PWL.server_protected_handshake_contiguous_replay_events
          server_material
          sent_msg0
          sent_msg1
          server_auth_skip
          sent_msg2
          sent_msg3
          server_app_write_material
          received_msg4
          [
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = server_app_read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
          ])
  returns
    FStar.List.Tot.length server.CS.cs_event_log == 15
  with _.
  (
    assert_norm
      (FStar.List.Tot.length
        (FStar.List.Tot.append
          (PWSeg.server_cleartext_handshake_prefix_events
            ch
            selection
            server_shared
            sh)
          (PWL.server_protected_handshake_contiguous_replay_events
            server_material
            sent_msg0
            sent_msg1
            server_auth_skip
            sent_msg2
            sent_msg3
            server_app_write_material
            received_msg4
            [
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_app_read_material;
                  };
                });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
            ])) == 15)
  )

(**
  Corrected-length (16) counterpart of [lemma_server_no_tail_start_spine]:
  see [server_no_tail_start_spine16] for why the boundary moves from 15 to
  16.  The proof is the same shape -- fix the generic spine, then pin down
  the mandatory first event -- just against the 16-slot spine and using the
  length-16 first-event lemma.
**)
let lemma_server_no_tail_start_spine16
  (server:CS.connection_state)
  : Lemma
      (requires
        SD.server_driver_application_ready server /\
        FStar.List.Tot.length server.CS.cs_event_log == 16)
      (ensures server_no_tail_start_spine16 server)
=
  PNI.lemma_server_no_tail_log_spine16 server;
  PNI.lemma_server_no_tail_first_event_start16 server;
  eliminate exists e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
    server.CS.cs_event_log ==
      [e0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]
  returns
    server_no_tail_start_spine16 server
  with _.
  (
    eliminate exists rest.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: rest
    returns
      server_no_tail_start_spine16 server
    with _.
    (
      assert (server.CS.cs_event_log ==
        e0 :: [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert (server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: rest);
      assert (e0 == CS.ConnLocalEvent CS.LocalStartServer);
      assert (rest == [e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15]);
      assert (server.CS.cs_event_log ==
        [ CS.ConnLocalEvent CS.LocalStartServer;
          e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15 ])
    )
  )

let lemma_server_no_tail_two_handshake_install_cover_cases
  (e5:CS.conn_event)
  (e6:CS.conn_event)
  : Lemma
      (requires server_no_tail_two_handshake_install_cover e5 e6)
      (ensures
        (server_no_tail_handshake_write_install_event e5 /\
         server_no_tail_handshake_read_install_event e6) \/
        (server_no_tail_handshake_read_install_event e5 /\
         server_no_tail_handshake_write_install_event e6))
=
  ()

let lemma_server_no_tail_handshake_write_install_event_step_model_as_role
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        server_no_tail_handshake_write_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = material;
                };
              })) == Some model1)
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    let install = role_install.CS.install_payload in
    assert (role_install.CS.install_role == CS.ServerEndpoint);
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficWrite);
    introduce exists material.
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = material;
            };
          })) == Some model1
    with install.CS.install_material and ()
  | _ ->
    assert False

let lemma_server_no_tail_handshake_read_install_event_step_model_as_role
  (model model1:CS.connection_model)
  (ev:CS.conn_event)
  : Lemma
      (requires
        server_no_tail_handshake_read_install_event ev /\
        CS.step_model model ev == Some model1)
      (ensures
        exists material.
          CS.step_model
            model
            (CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficHandshake;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = material;
                };
              })) == Some model1)
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    let install = role_install.CS.install_payload in
    assert (role_install.CS.install_role == CS.ServerEndpoint);
    assert (install.CS.install_epoch == CS.TrafficHandshake);
    assert (install.CS.install_direction == CS.TrafficRead);
    introduce exists material.
      CS.step_model
        model
        (CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = material;
            };
          })) == Some model1
    with install.CS.install_material and ()
  | _ ->
    assert False
