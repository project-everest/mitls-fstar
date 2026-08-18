module TLS13.Impl.Driver.PairingNoTailServerFlightShape

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CSL = TLS13.ConnectionState.Lemmas
module M = TLS13.Messages
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PNTWHR = TLS13.Impl.Driver.PairingNoTailServerHelloWindowRank
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module ID = FStar.IndefiniteDescription

#push-options "--z3rlimit 10"

let lemma_server_window_rank_after_two_handshake_installs_is_nine
  (model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false)
      (ensures PNTWHR.server_hello_window_rank model == 9)
=
  assert_norm
    (PNTWHR.server_hello_window_late_flight_progress
      model.CS.model_handshake == 4);
  match model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret,
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic,
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic
  with
  | Some _, Some _, Some _ -> ()
  | _, _, _ -> assert False; false_elim ()

let rec lemma_server_window_stuck_without_server_application_traffic
  (model:CS.connection_model)
  (events:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model events raw_sent raw_received final_model)
      (ensures ~ (final_model.CS.model_control == CS.ControlApplicationData))
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    assert_norm (
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists model1 delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 rest tail_sent tail_received final_model));
    eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 rest tail_sent tail_received final_model
    with
    (
      CSL.lemma_step_model_preserves_config model ev model1;
      match model1.CS.model_control with
      | CS.ControlFailed _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1
          rest
          tail_sent
          tail_received
          final_model
      | _ ->
        (match ev with
        | CS.ConnLocalEvent local ->
          assert (CS.legal_local_event model local);
          assert (CS.step_local_event model local == Some model1);
          (match local with
          | CS.LocalInstallTrafficKeysForRole role_install ->
            let install = role_install.CS.install_payload in
            assert (role_install.CS.install_role == CS.ServerEndpoint);
            assert (CS.traffic_install_allowed_at_stage_for_role
              CS.ServerEndpoint
              CS.HsClientFinishedReceived
              install);
            (match install.CS.install_epoch, install.CS.install_direction with
            | CS.TrafficApplication, CS.TrafficRead ->
              assert (model1.CS.model_control ==
                CS.ControlHandshaking CS.HsClientFinishedReceived);
              assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic ==
                model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
              lemma_server_window_stuck_without_server_application_traffic
                model1
                rest
                tail_sent
                tail_received
                final_model
            | _, _ ->
              assert False; false_elim ())
          | CS.LocalVerifyClientFinished _ ->
            assert (CS.application_record_keys_installed_for_role
              CS.ServerEndpoint
              model);
            assert False; false_elim ()
          | CS.LocalFail _ ->
            assert False; false_elim ()
          | _ ->
            assert (CS.step_local_event model local == None);
            assert False; false_elim ())
        | CS.ConnNetworkEvent msg ->
          assert (CS.legal_tls_message
            model
            msg.CL.message_direction
            msg.CL.message_value);
          assert (CS.step_tls_message
            model
            msg.CL.message_direction
            msg.CL.message_value == Some model1);
          (match msg.CL.message_value with
          | M.TlsAlert _ ->
            assert False; false_elim ()
          | M.TlsChangeCipherSpec ->
            assert (model1 == model);
            lemma_server_window_stuck_without_server_application_traffic
              model1
              rest
              tail_sent
              tail_received
              final_model
          | M.TlsHandshake hs_msg ->
            assert (CS.step_handshake_message
              model
              msg.CL.message_direction
              hs_msg == None);
            assert False; false_elim ()
          | M.TlsApplicationData _ ->
            assert False; false_elim ()
          | M.TlsIgnoredPostHandshake _ ->
            assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
            assert False; false_elim ()
          | M.TlsKeyUpdate _ ->
            assert (model.CS.model_config.CS.config_role == CS.ClientEndpoint);
            assert False; false_elim ()))
    )

(**
  [get_replay_step] : an internal helper that turns one recursive unfolding
  of [TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received
  final_model] into concrete values (rather than a classical existential
  elimination).

  This is deliberately factored into three sub-helpers ([get_model1],
  [get_deltas], [get_tail_pair]), each performing a *single* [FStar.
  IndefiniteDescription.indefinite_description_ghost] extraction (or a short
  chain of at most two). Collapsing all five existentially-bound values
  (model1, delta_sent, delta_received, tail_sent, tail_received) into one
  function was found experimentally to make the final "the returned tuple
  satisfies its ensures clause" query blow up (it does not finish within a
  generous rlimit), even though every individual extraction step is cheap.
  Splitting the extraction this way keeps every SMT query small.
**)
private
let get_model1
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost CS.connection_model
      (requires TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model)
      (ensures fun model1 ->
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        (exists delta_sent delta_received tail_sent tail_received.
          CS.event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model))
=
  assert_norm (
    TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model ==
    (exists model1 delta_sent delta_received tail_sent tail_received.
      CS.legal_event model ev /\
      CS.step_model model ev == Some model1 /\
      CS.event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model));
  ID.indefinite_description_ghost CS.connection_model
    (fun m ->
      exists delta_sent delta_received tail_sent tail_received.
        CS.legal_event model ev /\
        CS.step_model model ev == Some m /\
        CS.event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay m tl tail_sent tail_received final_model)

private
let get_deltas
  (model1:CS.connection_model)
  (ev:CS.conn_event)
  (model:CS.connection_model)
  (tl:list CS.conn_event)
  (raw_sent raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (B.bytes & B.bytes)
      (requires
        exists delta_sent delta_received tail_sent tail_received.
          CS.event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model)
      (ensures fun (delta_sent, delta_received) ->
        exists tail_sent tail_received.
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model)
=
  let delta_sent =
    ID.indefinite_description_ghost B.bytes
      (fun ds ->
        exists delta_received tail_sent tail_received.
          CS.event_raw_delta_legal model ev ds delta_received /\
          Seq.equal raw_sent (B.append ds tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model) in
  let delta_received =
    ID.indefinite_description_ghost B.bytes
      (fun dr ->
        exists tail_sent tail_received.
          CS.event_raw_delta_legal model ev delta_sent dr /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append dr tail_received) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model) in
  (delta_sent, delta_received)

private
let get_tail_pair
  (model1:CS.connection_model)
  (tl:list CS.conn_event)
  (delta_sent delta_received raw_sent raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (B.bytes & B.bytes)
      (requires
        exists tail_sent tail_received.
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model)
      (ensures fun (tail_sent, tail_received) ->
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model)
=
  let tail_sent =
    ID.indefinite_description_ghost B.bytes
      (fun ts ->
        exists tail_received.
          Seq.equal raw_sent (B.append delta_sent ts) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl ts tail_received final_model) in
  let tail_received =
    ID.indefinite_description_ghost B.bytes
      (fun tr ->
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tr) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tr final_model) in
  (tail_sent, tail_received)

private
let get_replay_step
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (CS.connection_model & B.bytes & B.bytes)
      (requires TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model)
      (ensures fun (model1, tail_sent, tail_received) ->
        CS.legal_event model ev /\
        CS.step_model model ev == Some model1 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model)
=
  let model1 = get_model1 model ev tl raw_sent raw_received final_model in
  let (delta_sent, delta_received) = get_deltas model1 ev model tl raw_sent raw_received final_model in
  let (tail_sent, tail_received) =
    get_tail_pair model1 tl delta_sent delta_received raw_sent raw_received final_model in
  (model1, tail_sent, tail_received)

(**
  The nine steps of the server post-[ServerHello] flight are each proved by
  a small standalone [Ghost] function that:
  - takes the *current* model (satisfying the invariant established by the
    previous step, or by the two initial installs for step 0);
  - uses [get_replay_step] to obtain the successor model together with the
    tail raw byte streams (concretely, not via a classical existential
    elimination);
  - matches on the event to rule out every shape other than the one
    expected at this position (deriving [False] in each such case using the
    the "stuck" facts already proved above), returning the payload witness
    together with the successor model and tail streams.

  Each step is independently small enough for Z3 to verify quickly; chaining
  them via ordinary [let]-bindings (rather than nesting them inside 9 levels
  of [eliminate exists ... with _. (...)]) avoids the single monolithic
  proof obligation that made the original all-in-one formulation of this
  lemma time out.
**)

private
let get_flight_step0
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (GEE.encryptedExtensions & CS.connection_model & B.bytes & B.bytes)
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        FStar.List.Tot.length tl == 8 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures fun (ee, model1, tail_sent, tail_received) ->
        ev == CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
        } /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model /\
        model1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        Some? model1.CS.model_handshake.CS.hs_encrypted_extensions /\
        model1.CS.model_handshake.CS.hs_certificate == None /\
        model1.CS.model_handshake.CS.hs_certificate_verify == None /\
        model1.CS.model_handshake.CS.hs_certificate_verify_verified == false)
=
  lemma_server_window_rank_after_two_handshake_installs_is_nine model;
  let (model1, tail_sent, tail_received) =
    get_replay_step model ev tl raw_sent raw_received final_model in
  CSL.lemma_step_model_preserves_config model ev model1;
  let ee =
    match ev with
    | CS.ConnNetworkEvent msg ->
      assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
      (match msg.CL.message_value with
      | M.TlsHandshake (M.EncryptedExtensions ee0) ->
        assert (msg.CL.message_direction == CL.Sent);
        ee0
      | M.TlsChangeCipherSpec ->
        assert (model1 == model);
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert (PNTWHR.server_hello_window_rank model1 <= 8);
        assert False; false_elim ()
      | M.TlsAlert _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | _ ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ())
    | CS.ConnLocalEvent local ->
      assert (CS.legal_local_event model local);
      (match local with
      | CS.LocalInstallTrafficKeysForRole role_install ->
        let install = role_install.CS.install_payload in
        assert (role_install.CS.install_role == CS.ServerEndpoint);
        assert (CS.traffic_install_allowed_at_stage_for_role
          CS.ServerEndpoint
          CS.HsServerHelloSent
          install);
        assert (install.CS.install_epoch == CS.TrafficHandshake);
        assert (model1.CS.model_control ==
          CS.ControlHandshaking CS.HsServerHelloSent);
        assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic);
        assert (Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic);
        assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
        assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None);
        assert (model1.CS.model_handshake.CS.hs_encrypted_extensions == None);
        assert (model1.CS.model_handshake.CS.hs_certificate == None);
        assert (model1.CS.model_handshake.CS.hs_certificate_verify == None);
        assert (model1.CS.model_handshake.CS.hs_certificate_verify_verified == false);
        lemma_server_window_rank_after_two_handshake_installs_is_nine model1;
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert (PNTWHR.server_hello_window_rank model1 <= 8);
        assert False; false_elim ()
      | CS.LocalFail _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | _ ->
        assert (CS.step_model model ev == None);
        assert False; false_elim ()) in
  (ee, model1, tail_sent, tail_received)

private
let get_flight_step1
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (GCert.certificate & CS.connection_model & B.bytes & B.bytes)
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        Some? model.CS.model_handshake.CS.hs_encrypted_extensions /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        FStar.List.Tot.length tl == 7 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures fun (cert, model1, tail_sent, tail_received) ->
        ev == CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Certificate cert);
        } /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model /\
        model1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        Some? model1.CS.model_handshake.CS.hs_certificate /\
        model1.CS.model_handshake.CS.hs_certificate_verify == None /\
        model1.CS.model_handshake.CS.hs_certificate_verify_verified == false)
=
  let (model1, tail_sent, tail_received) =
    get_replay_step model ev tl raw_sent raw_received final_model in
  CSL.lemma_step_model_preserves_config model ev model1;
  let cert =
    match ev with
    | CS.ConnNetworkEvent msg ->
      assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
      (match msg.CL.message_value with
      | M.TlsHandshake (M.Certificate cert0) ->
        assert (msg.CL.message_direction == CL.Sent);
        cert0
      | M.TlsChangeCipherSpec ->
        assert (model1 == model);
        assert (PNTWHR.server_hello_window_rank model1 == 8);
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | M.TlsAlert _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | _ ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ())
    | CS.ConnLocalEvent local ->
      assert (CS.legal_local_event model local);
      (match local with
      | CS.LocalStartHandshake _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalStartServer ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSelectServerParameters _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeriveSharedSecret _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeys _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeysForRole _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalValidateCertificate _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyCertificateSignature _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSignCertificateVerify _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyClientFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeliverApplicationData _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalFail _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()) in
  (cert, model1, tail_sent, tail_received)

private
let get_flight_step2
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (GCV.certificateVerify & CS.connection_model & B.bytes & B.bytes)
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        Some? model.CS.model_handshake.CS.hs_certificate /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        FStar.List.Tot.length tl == 6 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures fun (cv, model1, tail_sent, tail_received) ->
        ev == CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model /\
        model1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        Some? model1.CS.model_handshake.CS.hs_certificate /\
        model1.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
        model1.CS.model_handshake.CS.hs_certificate_verify_verified == false)
=
  let (model1, tail_sent, tail_received) =
    get_replay_step model ev tl raw_sent raw_received final_model in
  let cv =
    match ev with
    | CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv0) ->
      cv0
    | CS.ConnLocalEvent local ->
      assert (CS.legal_local_event model local);
      (match local with
      | CS.LocalStartHandshake _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalStartServer ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSelectServerParameters _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeriveSharedSecret _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeys _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeysForRole _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalValidateCertificate _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyCertificateSignature _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSignCertificateVerify _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyClientFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeliverApplicationData _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalFail _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ())
    | CS.ConnNetworkEvent msg ->
      assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
      (match msg.CL.message_value with
      | M.TlsChangeCipherSpec ->
        assert (model1 == model);
        assert (PNTWHR.server_hello_window_rank model1 == 7);
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | M.TlsAlert _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | _ ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ()) in
  (cv, model1, tail_sent, tail_received)

private
let get_flight_step3
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (cv:GCV.certificateVerify)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (CS.connection_model & B.bytes & B.bytes)
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        Some? model.CS.model_handshake.CS.hs_certificate /\
        model.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        FStar.List.Tot.length tl == 5 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures fun (model1, tail_sent, tail_received) ->
        ev == CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        } /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model /\
        model1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        Some? model1.CS.model_handshake.CS.hs_certificate /\
        Some? model1.CS.model_handshake.CS.hs_certificate_verify /\
        model1.CS.model_handshake.CS.hs_certificate_verify_verified == true)
=
  let (model1, tail_sent, tail_received) =
    get_replay_step model ev tl raw_sent raw_received final_model in
  (match ev with
  | CS.ConnNetworkEvent msg ->
    assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
    (match msg.CL.message_value with
    | M.TlsHandshake (M.CertificateVerify cv1) ->
      assert (msg.CL.message_direction == CL.Sent);
      assert (cv1 == cv)
    | M.TlsChangeCipherSpec ->
      assert (model1 == model);
      assert (PNTWHR.server_hello_window_rank model1 == 6);
      PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
        model1 tl tail_sent tail_received final_model;
      assert False; false_elim ()
    | M.TlsAlert _ ->
      PNI.lemma_conn_events_raw_replay_from_failed_results_failed
        model1 tl tail_sent tail_received final_model;
      assert False; false_elim ()
    | _ ->
      assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
      assert False; false_elim ())
  | CS.ConnLocalEvent local ->
    assert (CS.legal_local_event model local);
    (match local with
    | CS.LocalStartHandshake _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalStartServer ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalSelectServerParameters _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalDeriveSharedSecret _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalInstallTrafficKeys _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalInstallTrafficKeysForRole _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalValidateCertificate _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalVerifyCertificateSignature _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalSignCertificateVerify _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalVerifyFinished _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalVerifyClientFinished _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalDeliverApplicationData _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalFail _ ->
      PNI.lemma_conn_events_raw_replay_from_failed_results_failed
        model1 tl tail_sent tail_received final_model;
      assert False; false_elim ()));
  (model1, tail_sent, tail_received)

private
let get_flight_step4
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (GFin.finished & CS.connection_model & B.bytes & B.bytes)
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        Some? model.CS.model_handshake.CS.hs_certificate /\
        Some? model.CS.model_handshake.CS.hs_certificate_verify /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == true /\
        FStar.List.Tot.length tl == 4 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures fun (sf, model1, tail_sent, tail_received) ->
        ev == CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished sf);
        } /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model /\
        model1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None)
=
  let (model1, tail_sent, tail_received) =
    get_replay_step model ev tl raw_sent raw_received final_model in
  let sf =
    match ev with
    | CS.ConnNetworkEvent msg ->
      assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
      (match msg.CL.message_value with
      | M.TlsHandshake (M.Finished sf0) ->
        assert (msg.CL.message_direction == CL.Sent);
        sf0
      | M.TlsChangeCipherSpec ->
        assert (model1 == model);
        assert (PNTWHR.server_hello_window_rank model1 == 5);
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | M.TlsAlert _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | M.TlsHandshake (M.ClientHello _) ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ()
      | M.TlsHandshake (M.ServerHello _) ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ()
      | M.TlsHandshake (M.EncryptedExtensions _) ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ()
      | M.TlsHandshake (M.Certificate _) ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ()
      | M.TlsHandshake (M.CertificateVerify _) ->
        assert (PNTWHR.server_hello_window_rank model1 == 5);
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | M.TlsHandshake M.HelloRetryRequest ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ()
      | M.TlsApplicationData _ ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ()
      | M.TlsIgnoredPostHandshake _ ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ()
      | M.TlsKeyUpdate _ ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ())
    | CS.ConnLocalEvent local ->
      assert (CS.legal_local_event model local);
      (match local with
      | CS.LocalStartHandshake _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalStartServer ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSelectServerParameters _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeriveSharedSecret _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeys _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeysForRole _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalValidateCertificate _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyCertificateSignature _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSignCertificateVerify _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyClientFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeliverApplicationData _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalFail _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()) in
  (sf, model1, tail_sent, tail_received)

private
let get_flight_step5
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (CS.traffic_key_material & CS.connection_model & B.bytes & B.bytes)
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        FStar.List.Tot.length tl == 3 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures fun (server_app_write_material, model1, tail_sent, tail_received) ->
        ev == CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = server_app_write_material;
            };
          }) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model /\
        model1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model1.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None)
=
  let (model1, tail_sent, tail_received) =
    get_replay_step model ev tl raw_sent raw_received final_model in
  let server_app_write_material =
    match ev with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      let install = role_install.CS.install_payload in
      assert (role_install.CS.install_role == CS.ServerEndpoint);
      assert (CS.traffic_install_allowed_at_stage_for_role
        CS.ServerEndpoint
        CS.HsServerFinishedSent
        install);
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficWrite);
      install.CS.install_material
    | CS.ConnNetworkEvent msg ->
      assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
      (match msg.CL.message_value with
      | M.TlsHandshake (M.Finished _) ->
        assert (msg.CL.message_direction == CL.Received);
        assert (model1.CS.model_control ==
          CS.ControlHandshaking CS.HsClientFinishedReceived);
        assert (model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None);
        lemma_server_window_stuck_without_server_application_traffic
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | M.TlsChangeCipherSpec ->
        assert (model1 == model);
        assert (PNTWHR.server_hello_window_rank model1 == 4);
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | M.TlsAlert _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | _ ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ())
    | CS.ConnLocalEvent local ->
      assert (CS.legal_local_event model local);
      (match local with
      | CS.LocalStartHandshake _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalStartServer ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSelectServerParameters _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeriveSharedSecret _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeys _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeysForRole _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalValidateCertificate _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyCertificateSignature _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSignCertificateVerify _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyClientFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeliverApplicationData _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalFail _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()) in
  (server_app_write_material, model1, tail_sent, tail_received)

private
let get_flight_step6
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (GFin.finished & CS.connection_model & B.bytes & B.bytes)
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        FStar.List.Tot.length tl == 2 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures fun (cf, model1, tail_sent, tail_received) ->
        ev == CS.ConnNetworkEvent {
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.Finished cf);
        } /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model /\
        model1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model1.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model1.CS.model_handshake.CS.hs_client_finished == Some cf /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
        model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None)
=
  let (model1, tail_sent, tail_received) =
    get_replay_step model ev tl raw_sent raw_received final_model in
  let cf =
    match ev with
    | CS.ConnNetworkEvent msg ->
      assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
      (match msg.CL.message_value with
      | M.TlsHandshake (M.Finished cf0) ->
        assert (msg.CL.message_direction == CL.Received);
        cf0
      | M.TlsChangeCipherSpec ->
        assert (model1 == model);
        assert (PNTWHR.server_hello_window_rank model1 == 3);
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | M.TlsAlert _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | _ ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ())
    | CS.ConnLocalEvent local ->
      assert (CS.legal_local_event model local);
      (match local with
      | CS.LocalStartHandshake _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalStartServer ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSelectServerParameters _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeriveSharedSecret _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeys _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeysForRole _ ->
        assert (PNTWHR.server_hello_window_rank model1 == 3);
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | CS.LocalValidateCertificate _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyCertificateSignature _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSignCertificateVerify _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyClientFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeliverApplicationData _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalFail _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()) in
  (cf, model1, tail_sent, tail_received)

private
let get_flight_step7
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (cf:GFin.finished)
  (tl:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost (CS.traffic_key_material & CS.connection_model & B.bytes & B.bytes)
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model.CS.model_handshake.CS.hs_client_finished == Some cf /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        FStar.List.Tot.length tl == 1 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model (ev :: tl) raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures fun (server_app_read_material, model1, tail_sent, tail_received) ->
        ev == CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficApplication;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = server_app_read_material;
            };
          }) /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 tl tail_sent tail_received final_model /\
        model1.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model1.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        model1.CS.model_handshake.CS.hs_client_finished == Some cf /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
        Some? model1.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic)
=
  let (model1, tail_sent, tail_received) =
    get_replay_step model ev tl raw_sent raw_received final_model in
  let server_app_read_material =
    match ev with
    | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
      let install = role_install.CS.install_payload in
      assert (role_install.CS.install_role == CS.ServerEndpoint);
      assert (CS.traffic_install_allowed_at_stage_for_role
        CS.ServerEndpoint
        CS.HsClientFinishedReceived
        install);
      assert (install.CS.install_epoch == CS.TrafficApplication);
      assert (install.CS.install_direction == CS.TrafficRead);
      install.CS.install_material
    | CS.ConnLocalEvent (CS.LocalVerifyClientFinished _) ->
      assert (CS.application_record_keys_installed_for_role
        CS.ServerEndpoint
        model);
      assert False; false_elim ()
    | CS.ConnNetworkEvent msg ->
      assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
      (match msg.CL.message_value with
      | M.TlsChangeCipherSpec ->
        assert (model1 == model);
        assert (PNTWHR.server_hello_window_rank model1 == 2);
        PNTWHR.lemma_server_hello_window_rank_replay_lower_bound
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | M.TlsAlert _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()
      | _ ->
        assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
        assert False; false_elim ())
    | CS.ConnLocalEvent local ->
      assert (CS.legal_local_event model local);
      (match local with
      | CS.LocalStartHandshake _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalStartServer ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSelectServerParameters _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeriveSharedSecret _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeys _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalInstallTrafficKeysForRole _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalValidateCertificate _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyCertificateSignature _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalSignCertificateVerify _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalVerifyClientFinished _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalDeliverApplicationData _ ->
        assert (CS.step_model model ev == None); assert False; false_elim ()
      | CS.LocalFail _ ->
        PNI.lemma_conn_events_raw_replay_from_failed_results_failed
          model1 tl tail_sent tail_received final_model;
        assert False; false_elim ()) in
  (server_app_read_material, model1, tail_sent, tail_received)

private
let get_flight_step8
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (cf:GFin.finished)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Ghost unit
      (requires
        model.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived /\
        model.CS.model_handshake.CS.hs_client_finished == Some cf /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model [ev] raw_sent raw_received final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures fun () ->
        ev == CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf))
=
  let (model1, tail_sent, tail_received) =
    get_replay_step model ev [] raw_sent raw_received final_model in
  match ev with
  | CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf1) ->
    assert (cf1 == cf)
  | CS.ConnNetworkEvent msg ->
    assert (CS.legal_tls_message model msg.CL.message_direction msg.CL.message_value);
    (match msg.CL.message_value with
    | M.TlsChangeCipherSpec ->
      assert (model1 == model);
      assert_norm (TLS13.Spec.StateMachine.Replay.conn_events_raw_replay model1 [] tail_sent tail_received final_model ==
        (Seq.equal tail_sent B.empty /\ Seq.equal tail_received B.empty /\ final_model == model1));
      assert (final_model == model1);
      assert (final_model.CS.model_control ==
        CS.ControlHandshaking CS.HsClientFinishedReceived);
      assert False; false_elim ()
    | M.TlsAlert _ ->
      PNI.lemma_conn_events_raw_replay_from_failed_results_failed
        model1 [] tail_sent tail_received final_model;
      assert False; false_elim ()
    | _ ->
      assert (CS.step_tls_message model msg.CL.message_direction msg.CL.message_value == None);
      assert False; false_elim ())
  | CS.ConnLocalEvent local ->
    assert (CS.legal_local_event model local);
    (match local with
    | CS.LocalStartHandshake _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalStartServer ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalSelectServerParameters _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalDeriveSharedSecret _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalInstallTrafficKeys _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalInstallTrafficKeysForRole _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalValidateCertificate _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalVerifyCertificateSignature _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalSignCertificateVerify _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalVerifyFinished _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalVerifyClientFinished _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalDeliverApplicationData _ ->
      assert (CS.step_model model ev == None); assert False; false_elim ()
    | CS.LocalFail _ ->
      PNI.lemma_conn_events_raw_replay_from_failed_results_failed
        model1 [] tail_sent tail_received final_model;
      assert False; false_elim ())

private
let lemma_flight_core
  (model:CS.connection_model)
  (rest:list CS.conn_event)
  (ev0 ev1 ev2 ev3 ev4 ev5 ev6 ev7 ev8:CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        rest == [ev0; ev1; ev2; ev3; ev4; ev5; ev6; ev7; ev8] /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model
          rest
          raw_sent
          raw_received
          final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures server_post_two_handshake_installs_tail_order rest)
=
  assert (rest == ev0 :: ev1 :: ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 :: ev8 :: []);
  assert_norm (FStar.List.Tot.length (ev1 :: ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 :: ev8 :: []) == 8);
  let (ee, model1, sent1, received1) =
    get_flight_step0 model ev0 (ev1 :: ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 :: ev8 :: [])
      raw_sent raw_received final_model in
  assert_norm (FStar.List.Tot.length (ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 :: ev8 :: []) == 7);
  let (cert, model2, sent2, received2) =
    get_flight_step1 model1 ev1 (ev2 :: ev3 :: ev4 :: ev5 :: ev6 :: ev7 :: ev8 :: [])
      sent1 received1 final_model in
  assert_norm (FStar.List.Tot.length (ev3 :: ev4 :: ev5 :: ev6 :: ev7 :: ev8 :: []) == 6);
  let (cv, model3, sent3, received3) =
    get_flight_step2 model2 ev2 (ev3 :: ev4 :: ev5 :: ev6 :: ev7 :: ev8 :: [])
      sent2 received2 final_model in
  assert_norm (FStar.List.Tot.length (ev4 :: ev5 :: ev6 :: ev7 :: ev8 :: []) == 5);
  let (model4, sent4, received4) =
    get_flight_step3 model3 ev3 cv (ev4 :: ev5 :: ev6 :: ev7 :: ev8 :: [])
      sent3 received3 final_model in
  assert_norm (FStar.List.Tot.length (ev5 :: ev6 :: ev7 :: ev8 :: []) == 4);
  let (sf, model5, sent5, received5) =
    get_flight_step4 model4 ev4 (ev5 :: ev6 :: ev7 :: ev8 :: [])
      sent4 received4 final_model in
  assert_norm (FStar.List.Tot.length (ev6 :: ev7 :: ev8 :: []) == 3);
  let (server_app_write_material, model6, sent6, received6) =
    get_flight_step5 model5 ev5 (ev6 :: ev7 :: ev8 :: [])
      sent5 received5 final_model in
  assert_norm (FStar.List.Tot.length (ev7 :: ev8 :: []) == 2);
  let (cf, model7, sent7, received7) =
    get_flight_step6 model6 ev6 (ev7 :: ev8 :: [])
      sent6 received6 final_model in
  assert_norm (FStar.List.Tot.length (ev8 :: []) == 1);
  let (server_app_read_material, model8, sent8, received8) =
    get_flight_step7 model7 ev7 cf (ev8 :: [])
      sent7 received7 final_model in
  get_flight_step8 model8 ev8 cf sent8 received8 final_model;
  assert (rest ==
    [
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      };
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      };
      CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      };
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      };
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = {
            CS.install_epoch = CS.TrafficApplication;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = server_app_write_material;
          };
        });
      CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      };
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
    ]);
  (* Build up the 7-fold existential witness underlying
     [server_post_two_handshake_installs_tail_order] one variable at a time
     via [FStar.Classical.exists_intro], rather than relying on a single
     large SMT query (or the [introduce exists ... with ... and ()] sugar,
     which was observed experimentally to trigger an internal Z3 crash on
     this particular goal). Each [exists_intro] call is a trivial [Lemma]
     whose precondition is already established by the [assert] above, so
     this is cheap and robust. *)
  FStar.Classical.exists_intro
    (fun (read_material:CS.traffic_key_material) ->
      rest ==
        [
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Certificate cert);
          };
          CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished sf);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_app_write_material;
              };
            });
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished cf);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = read_material;
              };
            });
          CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
        ])
    server_app_read_material;
  FStar.Classical.exists_intro
    (fun (write_material:CS.traffic_key_material) ->
      exists (read_material:CS.traffic_key_material).
        rest ==
          [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                };
              });
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished cf);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
          ])
    server_app_write_material;
  FStar.Classical.exists_intro
    (fun (cf1:GFin.finished) ->
      exists (write_material:CS.traffic_key_material) (read_material:CS.traffic_key_material).
        rest ==
          [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished sf);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                };
              });
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished cf1);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf1)
          ])
    cf;
  FStar.Classical.exists_intro
    (fun (sf1:GFin.finished) ->
      exists (cf1:GFin.finished) (write_material:CS.traffic_key_material) (read_material:CS.traffic_key_material).
        rest ==
          [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished sf1);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                };
              });
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished cf1);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf1)
          ])
    sf;
  FStar.Classical.exists_intro
    (fun (cv1:GCV.certificateVerify) ->
      exists (sf1:GFin.finished) (cf1:GFin.finished) (write_material:CS.traffic_key_material) (read_material:CS.traffic_key_material).
        rest ==
          [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Certificate cert);
            };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv1);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv1);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished sf1);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                };
              });
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished cf1);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf1)
          ])
    cv;
  FStar.Classical.exists_intro
    (fun (cert1:GCert.certificate) ->
      exists (cv1:GCV.certificateVerify) (sf1:GFin.finished) (cf1:GFin.finished)
        (write_material:CS.traffic_key_material) (read_material:CS.traffic_key_material).
        rest ==
          [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Certificate cert1);
            };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv1);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv1);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished sf1);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                };
              });
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished cf1);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf1)
          ])
    cert;
  FStar.Classical.exists_intro
    (fun (ee1:GEE.encryptedExtensions) ->
      exists (cert1:GCert.certificate) (cv1:GCV.certificateVerify) (sf1:GFin.finished) (cf1:GFin.finished)
        (write_material:CS.traffic_key_material) (read_material:CS.traffic_key_material).
        rest ==
          [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee1);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Certificate cert1);
            };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv1);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv1);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished sf1);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = write_material;
                };
              });
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished cf1);
            };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = read_material;
                };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf1)
          ])
    ee

private
let lemma_conn_event_list_length_pos_cons (l:list CS.conn_event) (n:nat)
  : Lemma
      (requires FStar.List.Tot.length l == n + 1)
      (ensures exists hd tl. l == hd :: tl /\ FStar.List.Tot.length tl == n)
=
  match l with
  | [] ->
    assert False
  | hd :: tl ->
    assert (FStar.List.Tot.length l == FStar.List.Tot.length tl + 1);
    assert (FStar.List.Tot.length tl == n)

private
let lemma_conn_event_list_length_9
  (rest:list CS.conn_event)
  : Lemma
      (requires FStar.List.Tot.length rest == 9)
      (ensures
        exists ev0 ev1 ev2 ev3 ev4 ev5 ev6 ev7 ev8.
          rest == [ev0; ev1; ev2; ev3; ev4; ev5; ev6; ev7; ev8])
=
  lemma_conn_event_list_length_pos_cons rest 8;
  eliminate exists (ev0:CS.conn_event) (rest1:list CS.conn_event).
    rest == ev0 :: rest1 /\ FStar.List.Tot.length rest1 == 8
  with
  (
    lemma_conn_event_list_length_pos_cons rest1 7;
    eliminate exists (ev1:CS.conn_event) (rest2:list CS.conn_event).
      rest1 == ev1 :: rest2 /\ FStar.List.Tot.length rest2 == 7
    with
    (
      lemma_conn_event_list_length_pos_cons rest2 6;
      eliminate exists (ev2:CS.conn_event) (rest3:list CS.conn_event).
        rest2 == ev2 :: rest3 /\ FStar.List.Tot.length rest3 == 6
      with
      (
        lemma_conn_event_list_length_pos_cons rest3 5;
        eliminate exists (ev3:CS.conn_event) (rest4:list CS.conn_event).
          rest3 == ev3 :: rest4 /\ FStar.List.Tot.length rest4 == 5
        with
        (
          lemma_conn_event_list_length_pos_cons rest4 4;
          eliminate exists (ev4:CS.conn_event) (rest5:list CS.conn_event).
            rest4 == ev4 :: rest5 /\ FStar.List.Tot.length rest5 == 4
          with
          (
            lemma_conn_event_list_length_pos_cons rest5 3;
            eliminate exists (ev5:CS.conn_event) (rest6:list CS.conn_event).
              rest5 == ev5 :: rest6 /\ FStar.List.Tot.length rest6 == 3
            with
            (
              lemma_conn_event_list_length_pos_cons rest6 2;
              eliminate exists (ev6:CS.conn_event) (rest7:list CS.conn_event).
                rest6 == ev6 :: rest7 /\ FStar.List.Tot.length rest7 == 2
              with
              (
                lemma_conn_event_list_length_pos_cons rest7 1;
                eliminate exists (ev7:CS.conn_event) (rest8:list CS.conn_event).
                  rest7 == ev7 :: rest8 /\ FStar.List.Tot.length rest8 == 1
                with
                (
                  lemma_conn_event_list_length_pos_cons rest8 0;
                  eliminate exists (ev8:CS.conn_event) (rest9:list CS.conn_event).
                    rest8 == ev8 :: rest9 /\ FStar.List.Tot.length rest9 == 0
                  with
                  (
                    match rest9 with
                    | [] ->
                      assert (rest ==
                        [ev0; ev1; ev2; ev3; ev4; ev5; ev6; ev7; ev8]);
                      introduce exists
                        (ev0':CS.conn_event)
                        (ev1':CS.conn_event)
                        (ev2':CS.conn_event)
                        (ev3':CS.conn_event)
                        (ev4':CS.conn_event)
                        (ev5':CS.conn_event)
                        (ev6':CS.conn_event)
                        (ev7':CS.conn_event)
                        (ev8':CS.conn_event).
                        rest ==
                          [ev0'; ev1'; ev2'; ev3'; ev4'; ev5'; ev6'; ev7'; ev8']
                      with ev0 ev1 ev2 ev3 ev4 ev5 ev6 ev7 ev8 and ()
                    | _ :: _ ->
                      assert_norm (FStar.List.Tot.length rest9 >= 1);
                      assert False;
                      false_elim ()
                  )
                )
              )
            )
          )
        )
      )
    )
  )

let lemma_server_post_two_handshake_installs_tail_order_from_replay
  (model:CS.connection_model)
  (rest:list CS.conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        model.CS.model_config.CS.config_role == CS.ServerEndpoint /\
        model.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_server_handshake_traffic /\
        Some? model.CS.model_handshake.CS.hs_keys.CS.ks_client_handshake_traffic /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic == None /\
        model.CS.model_handshake.CS.hs_keys.CS.ks_client_application_traffic == None /\
        model.CS.model_handshake.CS.hs_encrypted_extensions == None /\
        model.CS.model_handshake.CS.hs_certificate == None /\
        model.CS.model_handshake.CS.hs_certificate_verify == None /\
        model.CS.model_handshake.CS.hs_certificate_verify_verified == false /\
        FStar.List.Tot.length rest == 9 /\
        TLS13.Spec.StateMachine.Replay.conn_events_raw_replay
          model
          rest
          raw_sent
          raw_received
          final_model /\
        final_model.CS.model_control == CS.ControlApplicationData /\
        PNTWHR.server_hello_window_rank final_model == 0)
      (ensures server_post_two_handshake_installs_tail_order rest)
=
  lemma_conn_event_list_length_9 rest;
  eliminate exists
    (ev0:CS.conn_event)
    (ev1:CS.conn_event)
    (ev2:CS.conn_event)
    (ev3:CS.conn_event)
    (ev4:CS.conn_event)
    (ev5:CS.conn_event)
    (ev6:CS.conn_event)
    (ev7:CS.conn_event)
    (ev8:CS.conn_event).
    rest == [ev0; ev1; ev2; ev3; ev4; ev5; ev6; ev7; ev8]
  with
  (
    lemma_flight_core model rest ev0 ev1 ev2 ev3 ev4 ev5 ev6 ev7 ev8 raw_sent raw_received final_model
  )

#pop-options
