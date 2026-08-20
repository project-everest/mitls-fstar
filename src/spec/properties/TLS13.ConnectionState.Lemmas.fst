module TLS13.ConnectionState.Lemmas

(**
  Proof support for TLS13.Spec.StateMachine.

  The core module is the audit surface. This module contains preservation,
  projection, segmentation, and replay lemmas used by the implementation proofs.
**)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module H = TLS13.Handshake.Spec
module ID = FStar.IndefiniteDescription
module K = TLS13.Keys
module M = TLS13.Messages
module GCH = TLS13.Wire.Generated.ClientHello
module R = TLS13.Record.Spec
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.Spec.StateMachine.ClientTrace
module Seq = FStar.Seq
module T = TLS13.Types
module Tr = TLS13.Transcript
module W = TLS13.Wire.Spec
module X = TLS13.X509.Spec

open FStar.List.Tot
open TLS13.Spec.StateMachine
open TLS13.Spec.StateMachine.Canonical
open TLS13.Spec.StateMachine.KeyIdentifiers
open TLS13.Spec.StateMachine.Reachability
open TLS13.Spec.StateMachine.Correspondence
open TLS13.Spec.StateMachine.KeyMaterial
open TLS13.Spec.StateMachine.Log
open TLS13.Spec.StateMachine.Replay

let lemma_endpoint_direction_traffic_labels
  ()
  : Lemma
      (ensures
        traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic /\
        traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic /\
        traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic /\
        traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic)
=
  ()

let lemma_legal_connection_delta_local_fail_control_failed
  (st0:connection_state)
  (st1:connection_state)
  (err:T.tls_error)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        legal_connection_delta
          st0
          {
            delta_event = ConnLocalEvent (LocalFail err);
            delta_raw_sent = raw_sent;
            delta_raw_received = raw_received;
          }
          st1)
      (ensures st1.cs_model.model_control == ControlFailed err)
=
  assert (step_model st0.cs_model (ConnLocalEvent (LocalFail err)) ==
    Some st1.cs_model);
  assert (step_local_event st0.cs_model (LocalFail err) ==
    Some (fail_model st0.cs_model err));
  assert (st1.cs_model == fail_model st0.cs_model err)

let lemma_step_model_from_failed_results_failed
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        ControlFailed? model0.model_control /\
        step_model model0 ev == Some model1)
      (ensures ControlFailed? model1.model_control)
=
  match model0.model_control with
  | ControlFailed err0 ->
    (match ev with
     | ConnLocalEvent local ->
       (match local with
        | LocalFail err ->
          assert (step_local_event model0 local == Some (fail_model model0 err));
          assert (model1 == fail_model model0 err)
        | _ ->
          assert (step_local_event model0 local == None);
          assert False)
     | ConnNetworkEvent msg ->
       (match msg.CL.message_value with
        | M.TlsAlert alert ->
          assert (step_tls_message
            model0
            msg.CL.message_direction
            msg.CL.message_value ==
            Some (fail_model model0 (T.AlertError alert)));
          assert (model1 == fail_model model0 (T.AlertError alert))
        | _ ->
          assert (step_tls_message
            model0
            msg.CL.message_direction
            msg.CL.message_value == None);
          assert False)
     | ConnProtectedHandshake step ->
       (* A buffering step succeeds without consulting the control state, so
          it is reachable here.  It rewrites only [model_record] and
          [hs_buffers], leaving [ControlFailed] in place.  Every other
          protected step goes through [step_handshake_message], which has no
          arm at [ControlFailed]. *)
       if step.protected_handshake_buffering
       then ()
       else assert False)
  | _ ->
    assert False

#push-options ""

let lemma_step_model_local_event_some
  (model0:connection_model)
  (local:local_event)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 (ConnLocalEvent local) == Some model1)
      (ensures step_local_event model0 local == Some model1)
=
  calc (==) {
    step_local_event model0 local;
  == {}
    step_model model0 (ConnLocalEvent local);
  == {}
    Some model1;
  }

let lemma_step_model_network_event_some
  (model0:connection_model)
  (msg:directed_message M.tls_message)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 (ConnNetworkEvent msg) == Some model1)
      (ensures
        step_tls_message
          model0
          msg.CL.message_direction
          msg.CL.message_value == Some model1)
=
  calc (==) {
    step_tls_message model0 msg.CL.message_direction msg.CL.message_value;
  == {}
    step_model model0 (ConnNetworkEvent msg);
  == {}
    Some model1;
  }

let lemma_legal_local_event_stable_client_x25519_key_share_projection
  (st0:connection_state)
  (local:local_event)
  (st1:connection_state)
  : Lemma
      (requires
        stable_client_x25519_key_share_projection st0 /\
        legal_local_event st0.cs_model local /\
        step_local_event st0.cs_model local == Some st1.cs_model)
      (ensures stable_client_x25519_key_share_projection st1)
=
  assert (client_x25519_key_share_projection st0);
  assert (client_x25519_key_share_projection_stable_control st0.cs_model.model_control);
  let hs0 = st0.cs_model.model_handshake in
  match local, st0.cs_model.model_control with
  | LocalDeriveSharedSecret shared, ControlHandshaking HsServerHelloReceived ->
    assert (st1.cs_model == derive_shared_secret_model st0.cs_model hs0 shared);
    (match
       hs0.hs_start,
       hs0.hs_client_hello,
       hs0.hs_server_hello,
       hs0.hs_keys.ks_shared_secret
     with
     | Some start, Some ch, Some sh, Some old_shared ->
       (match start.start_client_key_share_private with
        | Some sk ->
          (match server_hello_key_share sh with
           | Some ks ->
             assert (C.x25519_shared sk ks == Some old_shared);
             assert (C.x25519_shared sk ks == Some shared);
             assert (shared == old_shared)
           | None -> assert False)
        | None ->
          assert False)
     | _, _, _, _ ->
       assert False);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalInstallTrafficKeys install, ControlHandshaking _ ->
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalInstallTrafficKeysForRole role_install, ControlHandshaking _ ->
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalValidateCertificate peer, ControlHandshaking HsCertificateReceived ->
    assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalVerifyCertificateSignature cv, ControlHandshaking HsCertificateVerifyReceived ->
    assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalVerifyFinished fin, ControlHandshaking HsServerFinishedReceived ->
    assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalDeliverApplicationData bytes, ControlApplicationData ->
    assert (st1.cs_model.model_handshake == hs0);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalFail err, _ ->
    assert (st1.cs_model == fail_model st0.cs_model err);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | _, _ ->
    assert False;
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)

let lemma_legal_local_event_stable_server_x25519_key_share_projection
  (st0:connection_state)
  (local:local_event)
  (st1:connection_state)
  : Lemma
      (requires
        stable_server_x25519_key_share_projection st0 /\
        legal_local_event st0.cs_model local /\
        step_local_event st0.cs_model local == Some st1.cs_model)
      (ensures stable_server_x25519_key_share_projection st1)
=
  assert (server_x25519_key_share_projection st0);
  assert (server_x25519_key_share_projection_stable_control st0.cs_model.model_control);
  let hs0 = st0.cs_model.model_handshake in
  match local, st0.cs_model.model_control with
  | LocalInstallTrafficKeys install, ControlHandshaking _ ->
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalInstallTrafficKeysForRole role_install, ControlHandshaking _ ->
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalSignCertificateVerify cv, ControlHandshaking HsServerEncryptedFlightSent ->
    assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalVerifyClientFinished fin, ControlHandshaking HsClientFinishedReceived ->
    assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalDeliverApplicationData bytes, ControlApplicationData ->
    assert (st1.cs_model.model_handshake == hs0);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | LocalFail err, _ ->
    assert (st1.cs_model == fail_model st0.cs_model err);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | _, _ ->
    assert False;
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)

let lemma_legal_tls_message_stable_client_x25519_key_share_projection
  (st0:connection_state)
  (msg:directed_message M.tls_message)
  (st1:connection_state)
  : Lemma
      (requires
        stable_client_x25519_key_share_projection st0 /\
        legal_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value /\
        step_tls_message
          st0.cs_model
          msg.CL.message_direction
          msg.CL.message_value == Some st1.cs_model)
      (ensures stable_client_x25519_key_share_projection st1)
=
  assert (client_x25519_key_share_projection st0);
  assert (client_x25519_key_share_projection_stable_control st0.cs_model.model_control);
  let hs0 = st0.cs_model.model_handshake in
  match msg.CL.message_value, st0.cs_model.model_control with
  | M.TlsHandshake hmsg, _ ->
    (match msg.CL.message_direction, hmsg, st0.cs_model.model_control with
     | CL.Received, M.EncryptedExtensions ee, ControlHandshaking HsServerHelloReceived ->
       assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (client_x25519_key_share_projection st1);
       assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Received, M.Certificate cert, ControlHandshaking HsEncryptedExtensionsReceived ->
       assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (client_x25519_key_share_projection st1);
       assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Received, M.CertificateVerify cv, ControlHandshaking HsCertificateValidated ->
       assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (client_x25519_key_share_projection st1);
       assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Received, M.Finished fin, ControlHandshaking HsCertificateVerifyVerified ->
       assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (client_x25519_key_share_projection st1);
       assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Sent, M.Finished fin, ControlHandshaking HsServerFinishedVerified ->
       assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (client_x25519_key_share_projection st1);
       assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | _, _, _ ->
       assert False;
       assert (client_x25519_key_share_projection st1);
       assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control))
  | M.TlsApplicationData bytes, ControlApplicationData ->
    assert (st1.cs_model.model_handshake == hs0);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsIgnoredPostHandshake post, ControlApplicationData ->
    assert (st1.cs_model.model_handshake == hs0);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsKeyUpdate req, ControlApplicationData ->
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsAlert T.Close_notify, ControlApplicationData ->
    assert (st1.cs_model.model_handshake == hs0);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsAlert T.Close_notify, ControlClosing ->
    (match msg.CL.message_direction with
     | CL.Received ->
       assert (st1.cs_model.model_handshake == hs0);
       assert (client_x25519_key_share_projection st1);
       assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Sent ->
       assert False;
       assert (client_x25519_key_share_projection st1);
       assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control))
  | M.TlsAlert alert, _ ->
    assert (st1.cs_model == fail_model st0.cs_model (T.AlertError alert));
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsChangeCipherSpec, ControlHandshaking _ ->
    assert (st1.cs_model == st0.cs_model);
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | _, _ ->
    assert False;
    assert (client_x25519_key_share_projection st1);
    assert (client_x25519_key_share_projection_stable_control st1.cs_model.model_control)

let lemma_legal_tls_message_stable_server_x25519_key_share_projection
  (st0:connection_state)
  (msg:directed_message M.tls_message)
  (st1:connection_state)
  : Lemma
      (requires
        stable_server_x25519_key_share_projection st0 /\
        legal_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value /\
        step_tls_message
          st0.cs_model
          msg.CL.message_direction
          msg.CL.message_value == Some st1.cs_model)
      (ensures stable_server_x25519_key_share_projection st1)
=
  assert (server_x25519_key_share_projection st0);
  assert (server_x25519_key_share_projection_stable_control st0.cs_model.model_control);
  let hs0 = st0.cs_model.model_handshake in
  match msg.CL.message_value, st0.cs_model.model_control with
  | M.TlsHandshake hmsg, _ ->
    (match msg.CL.message_direction, hmsg, st0.cs_model.model_control with
     | CL.Sent, M.EncryptedExtensions ee, ControlHandshaking HsServerHelloSent ->
       assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (server_x25519_key_share_projection st1);
       assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Sent, M.Certificate cert, ControlHandshaking HsServerEncryptedFlightSent ->
       assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (server_x25519_key_share_projection st1);
       assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Sent, M.CertificateVerify cv, ControlHandshaking HsServerEncryptedFlightSent ->
       assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (server_x25519_key_share_projection st1);
       assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Sent, M.Finished fin, ControlHandshaking HsServerEncryptedFlightSent ->
       assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (server_x25519_key_share_projection st1);
       assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Received, M.Finished fin, ControlHandshaking HsServerFinishedSent ->
       assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (server_x25519_key_share_projection st1);
       assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | _, _, _ ->
       assert False;
       assert (server_x25519_key_share_projection st1);
       assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control))
  | M.TlsApplicationData bytes, ControlApplicationData ->
    assert (st1.cs_model.model_handshake == hs0);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsIgnoredPostHandshake post, ControlApplicationData ->
    assert (st1.cs_model.model_handshake == hs0);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsKeyUpdate req, ControlApplicationData ->
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsAlert T.Close_notify, ControlApplicationData ->
    assert (st1.cs_model.model_handshake == hs0);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsAlert T.Close_notify, ControlClosing ->
    (match msg.CL.message_direction with
     | CL.Received ->
       assert (st1.cs_model.model_handshake == hs0);
       assert (server_x25519_key_share_projection st1);
       assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
     | CL.Sent ->
       assert False;
       assert (server_x25519_key_share_projection st1);
       assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control))
  | M.TlsAlert alert, _ ->
    assert (st1.cs_model == fail_model st0.cs_model (T.AlertError alert));
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | M.TlsChangeCipherSpec, ControlHandshaking _ ->
    assert (st1.cs_model == st0.cs_model);
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)
  | _, _ ->
    assert False;
    assert (server_x25519_key_share_projection st1);
    assert (server_x25519_key_share_projection_stable_control st1.cs_model.model_control)

let lemma_legal_connection_delta_stable_client_x25519_key_share_projection
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        stable_client_x25519_key_share_projection st0)
      (ensures stable_client_x25519_key_share_projection st1)
=
  assert (legal_event st0.cs_model delta.delta_event);
  assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
  match st0.cs_model.model_control with
  | ControlHandshaking HsServerHelloReceived
  | ControlHandshaking HsEncryptedExtensionsReceived
  | ControlHandshaking HsCertificateReceived
  | ControlHandshaking HsCertificateValidated
  | ControlHandshaking HsCertificateVerifyReceived
  | ControlHandshaking HsCertificateVerifyVerified
  | ControlHandshaking HsServerFinishedReceived
  | ControlHandshaking HsServerFinishedVerified
  | ControlHandshaking HsClientFinishedSent
  | ControlApplicationData
  | ControlClosing ->
    (match delta.delta_event with
     | ConnLocalEvent local ->
       assert (delta.delta_event == ConnLocalEvent local);
       assert (step_model st0.cs_model (ConnLocalEvent local) == Some st1.cs_model);
       assert (legal_local_event st0.cs_model local);
       assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
         step_local_event st0.cs_model local);
       assert (step_model st0.cs_model (ConnLocalEvent local) ==
         step_local_event st0.cs_model local);
       lemma_step_model_local_event_some st0.cs_model local st1.cs_model;
       lemma_legal_local_event_stable_client_x25519_key_share_projection st0 local st1
     | ConnNetworkEvent msg ->
       assert (delta.delta_event == ConnNetworkEvent msg);
       assert (step_model st0.cs_model (ConnNetworkEvent msg) == Some st1.cs_model);
       assert (legal_tls_message
         st0.cs_model
         msg.CL.message_direction
         msg.CL.message_value);
       assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
         step_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value);
       assert (step_model st0.cs_model (ConnNetworkEvent msg) ==
         step_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value);
       lemma_step_model_network_event_some st0.cs_model msg st1.cs_model;
       assert (step_tls_message
         st0.cs_model
         msg.CL.message_direction
         msg.CL.message_value == Some st1.cs_model);
       lemma_legal_tls_message_stable_client_x25519_key_share_projection st0 msg st1
      | ConnProtectedHandshake step ->
       assert (legal_protected_handshake_step st0.cs_model step);
       assert_norm (
         step_model st0.cs_model (ConnProtectedHandshake step) ==
           step_protected_handshake st0.cs_model step);
       (* A buffering step carries no message, and rewrites only
          [model_record] and the handshake buffers -- so every field the
          key-share projection looks at is preserved. *)
       (if step.protected_handshake_buffering
        then ()
        else
        match step.protected_handshake_message, st0.cs_model.model_control with
        | M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived
        | M.Certificate _, ControlHandshaking HsEncryptedExtensionsReceived
        | M.CertificateVerify _, ControlHandshaking HsCertificateValidated
        | M.Finished _, ControlHandshaking HsCertificateVerifyVerified -> ()
        | _, _ -> assert False);
       let hs0 = st0.cs_model.model_handshake in
       assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
       assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
       assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
       assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
         hs0.hs_keys.ks_shared_secret);
       assert (client_x25519_key_share_projection st1);
       assert (client_x25519_key_share_projection_stable_control
         st1.cs_model.model_control))
  | ControlClosed ->
    (match delta.delta_event with
     | ConnLocalEvent local ->
       assert (delta.delta_event == ConnLocalEvent local);
       assert (step_model st0.cs_model (ConnLocalEvent local) == Some st1.cs_model);
       assert (legal_local_event st0.cs_model local);
       assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
         step_local_event st0.cs_model local);
       assert (step_model st0.cs_model (ConnLocalEvent local) ==
         step_local_event st0.cs_model local);
       lemma_step_model_local_event_some st0.cs_model local st1.cs_model;
       lemma_legal_local_event_stable_client_x25519_key_share_projection st0 local st1
     | ConnNetworkEvent msg ->
       assert (delta.delta_event == ConnNetworkEvent msg);
       assert (step_model st0.cs_model (ConnNetworkEvent msg) == Some st1.cs_model);
       assert (legal_tls_message
         st0.cs_model
         msg.CL.message_direction
         msg.CL.message_value);
       assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
         step_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value);
       assert (step_model st0.cs_model (ConnNetworkEvent msg) ==
         step_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value);
       lemma_step_model_network_event_some st0.cs_model msg st1.cs_model;
       assert (step_tls_message
         st0.cs_model
         msg.CL.message_direction
         msg.CL.message_value == Some st1.cs_model);
       lemma_legal_tls_message_stable_client_x25519_key_share_projection st0 msg st1
      | ConnProtectedHandshake step ->
       assert False)
  | ControlFailed _ ->
    lemma_step_model_from_failed_results_failed
      st0.cs_model
      delta.delta_event
      st1.cs_model
  | _ ->
    assert False

let lemma_legal_connection_delta_stable_server_x25519_key_share_projection
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        stable_server_x25519_key_share_projection st0)
      (ensures stable_server_x25519_key_share_projection st1)
=
  assert (legal_event st0.cs_model delta.delta_event);
  assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
  assert (stable_server_x25519_key_share_projection st0);
  assert (server_x25519_key_share_projection st0);
  assert (server_x25519_key_share_projection_stable_control st0.cs_model.model_control);
  match st0.cs_model.model_control with
  | ControlHandshaking HsServerHelloSent
  | ControlHandshaking HsServerEncryptedFlightSent
  | ControlHandshaking HsServerFinishedSent
  | ControlHandshaking HsClientFinishedReceived
  | ControlHandshaking HsClientFinishedVerified
  | ControlApplicationData
  | ControlClosing ->
    (match delta.delta_event with
     | ConnLocalEvent local ->
       assert (delta.delta_event == ConnLocalEvent local);
       assert (step_model st0.cs_model (ConnLocalEvent local) == Some st1.cs_model);
       assert (legal_local_event st0.cs_model local);
       assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
         step_local_event st0.cs_model local);
       assert (step_model st0.cs_model (ConnLocalEvent local) ==
         step_local_event st0.cs_model local);
       lemma_step_model_local_event_some st0.cs_model local st1.cs_model;
       lemma_legal_local_event_stable_server_x25519_key_share_projection st0 local st1
     | ConnNetworkEvent msg ->
       assert (delta.delta_event == ConnNetworkEvent msg);
       assert (step_model st0.cs_model (ConnNetworkEvent msg) == Some st1.cs_model);
       assert (legal_tls_message
         st0.cs_model
         msg.CL.message_direction
         msg.CL.message_value);
       assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
         step_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value);
       assert (step_model st0.cs_model (ConnNetworkEvent msg) ==
         step_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value);
       lemma_step_model_network_event_some st0.cs_model msg st1.cs_model;
       assert (step_tls_message
         st0.cs_model
         msg.CL.message_direction
         msg.CL.message_value == Some st1.cs_model);
       lemma_legal_tls_message_stable_server_x25519_key_share_projection st0 msg st1
      | ConnProtectedHandshake step ->
       assert False)
  | ControlClosed ->
    (match delta.delta_event with
     | ConnLocalEvent local ->
       assert (delta.delta_event == ConnLocalEvent local);
       assert (step_model st0.cs_model (ConnLocalEvent local) == Some st1.cs_model);
       assert (legal_local_event st0.cs_model local);
       assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
         step_local_event st0.cs_model local);
       assert (step_model st0.cs_model (ConnLocalEvent local) ==
         step_local_event st0.cs_model local);
       lemma_step_model_local_event_some st0.cs_model local st1.cs_model;
       lemma_legal_local_event_stable_server_x25519_key_share_projection st0 local st1
     | ConnNetworkEvent msg ->
       assert (delta.delta_event == ConnNetworkEvent msg);
       assert (step_model st0.cs_model (ConnNetworkEvent msg) == Some st1.cs_model);
       assert (legal_tls_message
         st0.cs_model
         msg.CL.message_direction
         msg.CL.message_value);
       assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
         step_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value);
       assert (step_model st0.cs_model (ConnNetworkEvent msg) ==
         step_tls_message st0.cs_model msg.CL.message_direction msg.CL.message_value);
       lemma_step_model_network_event_some st0.cs_model msg st1.cs_model;
       assert (step_tls_message
         st0.cs_model
         msg.CL.message_direction
         msg.CL.message_value == Some st1.cs_model);
       lemma_legal_tls_message_stable_server_x25519_key_share_projection st0 msg st1
      | ConnProtectedHandshake step ->
       assert False)
  | ControlFailed _ ->
    lemma_step_model_from_failed_results_failed
      st0.cs_model
      delta.delta_event
      st1.cs_model
  | _ ->
    assert False

let lemma_expected_traffic_secret_client_projection
  (hs:handshake_state)
  (epoch:traffic_epoch)
  (dir:traffic_direction)
  : Lemma
      (ensures
        expected_traffic_secret hs epoch dir ==
        expected_traffic_secret_for_role ClientEndpoint hs epoch dir)
=
  ()

let lemma_update_key_schedule_with_install_client_projection
  (keys:key_schedule_state)
  (install:traffic_key_install)
  : Lemma
      (ensures
        update_key_schedule_with_install keys install ==
        update_key_schedule_with_install_for_role ClientEndpoint keys install)
=
  ()

let supported_profile_base_lineage_or_empty
  (keys:key_schedule_state)
  : prop =
  match
    keys.ks_shared_secret,
    keys.ks_early_secret,
    keys.ks_handshake_secret,
    keys.ks_master_secret
  with
  | None, None, None, None ->
    True
  | Some shared, Some early, Some handshake, Some master ->
    Seq.equal early (K.early_secret B.empty) /\
    Seq.equal handshake (K.handshake_secret early shared) /\
    Seq.equal master (K.master_secret handshake)
  | _, _, _, _ ->
    False

let traffic_material_slots_have_base_secret
  (keys:key_schedule_state)
  : prop =
  (Some? keys.ks_client_handshake_traffic ==> Some? keys.ks_handshake_secret) /\
  (Some? keys.ks_server_handshake_traffic ==> Some? keys.ks_handshake_secret) /\
  (Some? keys.ks_client_application_traffic ==> Some? keys.ks_master_secret) /\
  (Some? keys.ks_server_application_traffic ==> Some? keys.ks_master_secret)

let model_supported_profile_key_schedule_reachable_shape
  (model:connection_model)
  : prop =
  let keys = model.model_handshake.hs_keys in
  supported_profile_base_lineage_or_empty keys /\
  traffic_material_slots_have_base_secret keys

let connection_supported_profile_key_schedule_reachable_shape
  (st:connection_state)
  : prop =
  model_supported_profile_key_schedule_reachable_shape st.cs_model

let lemma_same_key_schedule_reachable_shape
  (model:connection_model)
  (model':connection_model)
  : Lemma
      (requires
        model_supported_profile_key_schedule_reachable_shape model /\
        model'.model_handshake.hs_keys == model.model_handshake.hs_keys)
      (ensures model_supported_profile_key_schedule_reachable_shape model')
=
  ()

#restart-solver
let lemma_supported_profile_base_lineage_or_empty_to_lineage
  (keys:key_schedule_state)
  : Lemma
      (requires
        supported_profile_base_lineage_or_empty keys /\
        Some? keys.ks_master_secret)
      (ensures supported_profile_key_schedule_lineage keys)
=
  match
    keys.ks_shared_secret,
    keys.ks_early_secret,
    keys.ks_handshake_secret,
    keys.ks_master_secret
  with
  | Some shared, Some early, Some handshake, Some master ->
    ()
  | _, _, _, _ ->
    assert False

let lemma_application_keys_reachable_shape_supported_profile_key_schedule_lineage
  (role:endpoint_role)
  (model:connection_model)
  : Lemma
      (requires
        model_supported_profile_key_schedule_reachable_shape model /\
        application_record_keys_installed_for_role role model)
      (ensures supported_profile_key_schedule_lineage model.model_handshake.hs_keys)
=
  let keys = model.model_handshake.hs_keys in
  match role with
  | ClientEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
    assert (Some? keys.ks_server_application_traffic);
    assert (Some? keys.ks_master_secret)
  | ServerEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
    assert (Some? keys.ks_client_application_traffic);
    assert (Some? keys.ks_master_secret);
  lemma_supported_profile_base_lineage_or_empty_to_lineage keys

let lemma_traffic_install_matches_key_schedule_base_present_for_role
  (role:endpoint_role)
  (hs:handshake_state)
  (install:traffic_key_install)
  : Lemma
      (requires traffic_install_matches_key_schedule_for_role role hs install)
      (ensures Some? (traffic_secret_base_for_epoch install.install_epoch hs.hs_keys))
=
  match role, install.install_epoch, install.install_direction with
  | ClientEndpoint, TrafficHandshake, TrafficRead
  | ClientEndpoint, TrafficHandshake, TrafficWrite
  | ServerEndpoint, TrafficHandshake, TrafficRead
  | ServerEndpoint, TrafficHandshake, TrafficWrite ->
    (match hs.hs_keys.ks_handshake_secret with
    | Some _ -> ()
    | None -> assert False)
  | ClientEndpoint, TrafficApplication, TrafficRead
  | ClientEndpoint, TrafficApplication, TrafficWrite
  | ServerEndpoint, TrafficApplication, TrafficRead
  | ServerEndpoint, TrafficApplication, TrafficWrite ->
    (match hs.hs_keys.ks_master_secret with
    | Some _ -> ()
    | None -> assert False)

let lemma_traffic_install_matches_key_schedule_base_present
  (hs:handshake_state)
  (install:traffic_key_install)
  : Lemma
      (requires traffic_install_matches_key_schedule hs install)
      (ensures Some? (traffic_secret_base_for_epoch install.install_epoch hs.hs_keys))
=
  lemma_expected_traffic_secret_client_projection
    hs
    install.install_epoch
    install.install_direction;
  lemma_traffic_install_matches_key_schedule_base_present_for_role
    ClientEndpoint
    hs
    install

let lemma_update_key_schedule_with_label_reachable_shape
  (keys:key_schedule_state)
  (epoch:traffic_epoch)
  (label:traffic_label)
  (material:traffic_key_material)
  : Lemma
      (requires
        supported_profile_base_lineage_or_empty keys /\
        traffic_material_slots_have_base_secret keys /\
        Some? (traffic_secret_base_for_epoch epoch keys))
      (ensures
        supported_profile_base_lineage_or_empty
          (update_key_schedule_with_label keys epoch label material) /\
        traffic_material_slots_have_base_secret
          (update_key_schedule_with_label keys epoch label material))
=
  match epoch, label with
  | TrafficHandshake, ClientTraffic
  | TrafficHandshake, ServerTraffic ->
    assert (Some? keys.ks_handshake_secret)
  | TrafficApplication, ClientTraffic
  | TrafficApplication, ServerTraffic ->
    assert (Some? keys.ks_master_secret)

let lemma_update_application_traffic_material_reachable_shape
  (keys:key_schedule_state)
  (label:traffic_label)
  (material:traffic_key_material)
  : Lemma
      (requires
        supported_profile_base_lineage_or_empty keys /\
        traffic_material_slots_have_base_secret keys /\
        Some? (traffic_material_for_label keys TrafficApplication label))
      (ensures
        supported_profile_base_lineage_or_empty
          (update_key_schedule_with_label keys TrafficApplication label material) /\
        traffic_material_slots_have_base_secret
          (update_key_schedule_with_label keys TrafficApplication label material))
=
  match label with
  | ClientTraffic ->
    assert (Some? keys.ks_client_application_traffic);
    assert (Some? keys.ks_master_secret)
  | ServerTraffic ->
    assert (Some? keys.ks_server_application_traffic);
    assert (Some? keys.ks_master_secret);
  lemma_update_key_schedule_with_label_reachable_shape
    keys
    TrafficApplication
    label
    material

let lemma_update_key_schedule_with_install_for_role_reachable_shape
  (role:endpoint_role)
  (keys:key_schedule_state)
  (install:traffic_key_install)
  : Lemma
      (requires
        supported_profile_base_lineage_or_empty keys /\
        traffic_material_slots_have_base_secret keys /\
        Some? (traffic_secret_base_for_epoch install.install_epoch keys))
      (ensures
        supported_profile_base_lineage_or_empty
          (update_key_schedule_with_install_for_role role keys install) /\
        traffic_material_slots_have_base_secret
          (update_key_schedule_with_install_for_role role keys install))
=
  lemma_update_key_schedule_with_label_reachable_shape
    keys
    install.install_epoch
    (traffic_label_for_endpoint_direction role install.install_direction)
    install.install_material

let lemma_update_key_schedule_with_install_reachable_shape
  (keys:key_schedule_state)
  (install:traffic_key_install)
  : Lemma
      (requires
        supported_profile_base_lineage_or_empty keys /\
        traffic_material_slots_have_base_secret keys /\
        Some? (traffic_secret_base_for_epoch install.install_epoch keys))
      (ensures
        supported_profile_base_lineage_or_empty
          (update_key_schedule_with_install keys install) /\
        traffic_material_slots_have_base_secret
          (update_key_schedule_with_install keys install))
=
  lemma_update_key_schedule_with_install_client_projection keys install;
  lemma_update_key_schedule_with_install_for_role_reachable_shape
    ClientEndpoint
    keys
    install

let lemma_derive_shared_secret_model_reachable_shape
  (model:connection_model)
  (hs:handshake_state)
  (shared:C.x25519_shared_secret)
  : Lemma
      (requires traffic_material_slots_have_base_secret hs.hs_keys)
      (ensures
        model_supported_profile_key_schedule_reachable_shape
          (derive_shared_secret_model model hs shared))
=
  let early = K.early_secret B.empty in
  let handshake = K.handshake_secret early shared in
  let master = K.master_secret handshake in
  ()

let lemma_step_handshake_message_supported_profile_key_schedule_reachable_shape
  (model:connection_model)
  (dir:direction)
  (msg:M.handshake_msg)
  (model':connection_model)
  : Lemma
      (requires
        model_supported_profile_key_schedule_reachable_shape model /\
        step_handshake_message model dir msg == Some model')
      (ensures model_supported_profile_key_schedule_reachable_shape model')
=
  match dir, msg, model.model_control with
  | CL.Sent, M.ClientHello _, ControlHandshaking HsStarted
  | CL.Received, M.ClientHello _, ControlHandshaking HsAwaitingClientHello
  | CL.Received, M.ServerHello _, ControlHandshaking HsClientHelloSent
  | CL.Sent, M.ServerHello _, ControlHandshaking HsClientHelloReceived
  | CL.Sent, M.EncryptedExtensions _, ControlHandshaking HsServerHelloSent
  | CL.Sent, M.Certificate _, ControlHandshaking HsServerEncryptedFlightSent
  | CL.Sent, M.CertificateVerify _, ControlHandshaking HsServerEncryptedFlightSent
  | CL.Sent, M.Finished _, ControlHandshaking HsServerEncryptedFlightSent
  | CL.Received, M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived
  | CL.Received, M.Certificate _, ControlHandshaking HsEncryptedExtensionsReceived
  | CL.Received, M.CertificateVerify _, ControlHandshaking HsCertificateValidated
  | CL.Sent, M.Finished _, ControlHandshaking HsServerFinishedVerified
  | CL.Received, M.HelloRetryRequest, ControlHandshaking HsClientHelloSent ->
    assert (model'.model_handshake.hs_keys == model.model_handshake.hs_keys);
    lemma_same_key_schedule_reachable_shape model model'
  | CL.Received, M.Finished _, ControlHandshaking HsCertificateVerifyVerified
  | CL.Received, M.Finished _, ControlHandshaking HsServerFinishedSent ->
    // Fix 1 (atomic Finished delivery): these arms now populate the application
    // traffic slot (server-app for the client delivery, client-app for the server
    // delivery). The base secrets (shared/early/handshake/master) are unchanged so
    // the base lineage is preserved; the new slot is backed by ks_master_secret,
    // which is Some (otherwise the transition would have returned None).
    ()
  | _, _, _ ->
    assert False

let lemma_step_tls_message_supported_profile_key_schedule_reachable_shape
  (model:connection_model)
  (dir:direction)
  (msg:M.tls_message)
  (model':connection_model)
  : Lemma
      (requires
        model_supported_profile_key_schedule_reachable_shape model /\
        legal_tls_message model dir msg /\
        step_tls_message model dir msg == Some model')
      (ensures model_supported_profile_key_schedule_reachable_shape model')
=
  let hs = model.model_handshake in
  let keys = hs.hs_keys in
  match msg, model.model_control with
  | M.TlsHandshake handshake_msg, _ ->
    lemma_step_handshake_message_supported_profile_key_schedule_reachable_shape
      model
      dir
      handshake_msg
      model'
  | M.TlsKeyUpdate req, ControlApplicationData ->
    (* KeyUpdate rotates whichever application-traffic slot the *local role*
       owns in the relevant direction, so the reasoning here is role-generic:
       a received KeyUpdate rotates the read label, a sent one the write label.
       [lemma_update_application_traffic_material_reachable_shape] is already
       stated for an arbitrary [traffic_label], so no case split on the role
       is needed. *)
    let tdir = match dir with
      | CL.Received -> TrafficRead
      | CL.Sent -> TrafficWrite in
    let label =
      traffic_label_for_endpoint_direction model.model_config.config_role tdir in
    (match traffic_material_for_label keys TrafficApplication label with
     | Some old_material ->
       let new_material = updated_traffic_key_material old_material in
       lemma_update_application_traffic_material_reachable_shape
         keys
         label
         new_material;
       assert (model'.model_handshake.hs_keys ==
               update_key_schedule_with_label
                 keys
                 TrafficApplication
                 label
                 new_material);
       assert (model_supported_profile_key_schedule_reachable_shape model')
     | None ->
       assert False)
  | M.TlsApplicationData _, ControlApplicationData
  | M.TlsAlert _, _
  | M.TlsChangeCipherSpec, ControlHandshaking _ ->
    assert (model'.model_handshake.hs_keys == keys);
    lemma_same_key_schedule_reachable_shape model model'
  | M.TlsIgnoredPostHandshake _, ControlApplicationData ->
    (match dir with
     | CL.Received ->
       assert (model'.model_handshake.hs_keys == keys);
       lemma_same_key_schedule_reachable_shape model model'
     | CL.Sent ->
       assert False)
  | _, _ ->
    assert False

let lemma_step_model_supported_profile_key_schedule_reachable_shape
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires
        model_supported_profile_key_schedule_reachable_shape model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures model_supported_profile_key_schedule_reachable_shape model')
=
  let hs = model.model_handshake in
  let keys = hs.hs_keys in
  match ev with
  | ConnLocalEvent local ->
    (match local, model.model_control with
     | LocalDeriveSharedSecret shared, ControlHandshaking HsServerHelloReceived
     | LocalDeriveSharedSecret shared, ControlHandshaking HsClientHelloReceived ->
       lemma_derive_shared_secret_model_reachable_shape model hs shared
     | LocalInstallTrafficKeys install, ControlHandshaking _ ->
       lemma_traffic_install_matches_key_schedule_base_present hs install;
       lemma_update_key_schedule_with_install_reachable_shape keys install
     | LocalInstallTrafficKeysForRole role_install, ControlHandshaking _ ->
       lemma_traffic_install_matches_key_schedule_base_present_for_role
         role_install.install_role
         hs
         role_install.install_payload;
       lemma_update_key_schedule_with_install_for_role_reachable_shape
         role_install.install_role
         keys
         role_install.install_payload
     | _, _ ->
       ())
  | ConnNetworkEvent msg ->
    lemma_step_tls_message_supported_profile_key_schedule_reachable_shape
      model
      msg.CL.message_direction
      msg.CL.message_value
      model'
  | ConnProtectedHandshake step ->
    assert (step_protected_handshake model step == Some model');
    if step.protected_handshake_buffering
    then
      (* A buffering step only moves plaintext into the pending handshake
         buffer and advances the record read state; it never touches the
         key schedule. *)
      lemma_same_key_schedule_reachable_shape model model'
    else
    if protected_handshake_message_supported step.protected_handshake_message
    then
      match
        step_handshake_message
          model
          CL.Received
          step.protected_handshake_message
      with
      | None ->
        assert False
      | Some stepped ->
        lemma_step_handshake_message_supported_profile_key_schedule_reachable_shape
          model
          CL.Received
          step.protected_handshake_message
          stepped;
        assert (model'.model_handshake.hs_keys ==
          stepped.model_handshake.hs_keys);
        lemma_same_key_schedule_reachable_shape stepped model'
    else
      assert False

let lemma_connection_delta_supported_profile_key_schedule_reachable_shape
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        connection_supported_profile_key_schedule_reachable_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures connection_supported_profile_key_schedule_reachable_shape st1)
=
  match st1 with
  | _ ->
    assert (exists delta. legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        connection_delta
        (fun delta -> legal_connection_delta st0 delta st1) in
    let delta : connection_delta = delta_w in
    assert (legal_connection_delta st0 delta st1);
    assert (legal_event st0.cs_model delta.delta_event);
    assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
    lemma_step_model_supported_profile_key_schedule_reachable_shape
      st0.cs_model
      delta.delta_event
      st1.cs_model

let lemma_initial_supported_profile_key_schedule_reachable_shape
  (cfg:connection_config)
  : Lemma
      (ensures
        connection_supported_profile_key_schedule_reachable_shape (initial cfg))
=
  ()

let lemma_connection_state_single_step_supported_profile_key_schedule_reachable_shape
  (u:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (connection_supported_profile_key_schedule_reachable_shape y);
            (connection_state_single_step x y)}
          connection_supported_profile_key_schedule_reachable_shape x /\
          connection_state_single_step x y ==>
          connection_supported_profile_key_schedule_reachable_shape y)
=
  introduce forall x y.
    connection_supported_profile_key_schedule_reachable_shape x /\
    connection_state_single_step x y ==>
    connection_supported_profile_key_schedule_reachable_shape y
  with
    introduce _ ==> _ with
    lemma_connection_delta_supported_profile_key_schedule_reachable_shape x y

let lemma_connection_state_consistent_supported_profile_key_schedule_reachable_shape
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures connection_supported_profile_key_schedule_reachable_shape st)
=
  let p = connection_supported_profile_key_schedule_reachable_shape in
  lemma_initial_supported_profile_key_schedule_reachable_shape st.cs_model.model_config;
  lemma_connection_state_single_step_supported_profile_key_schedule_reachable_shape ();
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)

let lemma_connection_application_keys_supported_profile_key_schedule_lineage
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        application_record_keys_installed_for_role role st.cs_model)
      (ensures connection_supported_profile_key_schedule_lineage st)
=
  lemma_connection_state_consistent_supported_profile_key_schedule_reachable_shape st;
  lemma_application_keys_reachable_shape_supported_profile_key_schedule_lineage
    role
    st.cs_model

let lemma_step_model_preserves_config_for_x25519_reachable_shape
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires step_model model ev == Some model')
      (ensures model'.model_config == model.model_config)
=
  ()

#push-options ""

let client_x25519_reachable_shape
  (st:connection_state)
  : prop =
  st.cs_model.model_config.config_role == ClientEndpoint ==>
  (match st.cs_model.model_handshake.hs_keys.ks_shared_secret with
   | Some _ ->
     stable_client_x25519_key_share_projection st
   | None ->
     (match st.cs_model.model_control with
      | ControlHandshaking HsStarted ->
        (* Every offered group's keypair is consistent, not just X25519's:
           the negotiated group is not known yet, so all of them must be. *)
        (match st.cs_model.model_handshake.hs_start with
         | Some start ->
           handshake_start_key_share_consistent start
         | None ->
           True)
      | ControlHandshaking HsClientHelloSent
      | ControlHandshaking HsServerHelloReceived ->
        client_x25519_pre_shared_secret_projection st
      | _ ->
        True))

let server_selected_client_hello_reachable_shape
  (st:connection_state)
  : prop =
  let hs = st.cs_model.model_handshake in
  match hs.hs_server_selection with
  | Some selection ->
    hs.hs_client_hello == Some selection.server_selected_client_hello /\
    server_selection_key_share_consistent selection
  | None ->
    True

let server_x25519_reachable_shape
  (st:connection_state)
  : prop =
  st.cs_model.model_config.config_role == ServerEndpoint ==>
  (match st.cs_model.model_handshake.hs_keys.ks_shared_secret with
   | Some _ ->
     (match st.cs_model.model_control with
      | ControlHandshaking HsClientHelloReceived ->
        server_x25519_pre_server_hello_projection st
      | ControlFailed _ ->
        server_x25519_pre_server_hello_projection st \/
        server_x25519_key_share_projection st
      | _ ->
        stable_server_x25519_key_share_projection st)
   | None ->
     (match st.cs_model.model_control with
      | ControlNew
      | ControlHandshaking HsAwaitingClientHello ->
        st.cs_model.model_handshake.hs_server_selection == None
      | ControlHandshaking HsClientHelloReceived ->
        server_selected_client_hello_reachable_shape st
      | _ ->
        True))

let lemma_legal_local_event_client_x25519_reachable_shape
  (st0:connection_state)
  (local:local_event)
  (st1:connection_state)
  : Lemma
      (requires
       client_x25519_reachable_shape st0 /\
       st0.cs_model.model_config.config_role == ClientEndpoint /\
       st0.cs_model.model_handshake.hs_keys.ks_shared_secret == None /\
       legal_local_event st0.cs_model local /\
       step_local_event st0.cs_model local == Some st1.cs_model)
      (ensures client_x25519_reachable_shape st1)
=
  let hs0 = st0.cs_model.model_handshake in
  match local, st0.cs_model.model_control with
  | LocalStartHandshake start, ControlNew ->
    (match start.start_client_key_share_private with
     | Some client_sk ->
      assert (C.x25519_public_from_private client_sk ==
        start.start_client_key_share_public)
     | None ->
      ());
    assert (client_x25519_reachable_shape st1)
  | LocalDeriveSharedSecret shared, ControlHandshaking HsServerHelloReceived ->
    assert (client_x25519_pre_shared_secret_projection st0);
    (match hs0.hs_start, hs0.hs_client_hello, hs0.hs_server_hello with
     | Some start, Some ch, Some sh ->
      (* Dispatch on the group the server named, exactly as the transition
         relation does.  Only the negotiated group's private key need exist:
         with P-256 negotiated the X25519 private may legitimately be `None`. *)
      (match server_hello_kex sh with
       | Some (| g, sh_ks |) ->
         assert (client_hello_kex ch g == Some (start_kex_public start g));
         (match start_kex_private start g with
          | Some sk ->
            assert (C.kex_public_from_private g sk == start_kex_public start g);
            assert (C.kex_shared g sk sh_ks == Some shared)
          | None -> assert False)
       | None -> assert False)
     | _, _, _ ->
      assert False);
    assert (stable_client_x25519_key_share_projection st1);
    assert (client_x25519_reachable_shape st1)
  | LocalInstallTrafficKeys install, ControlHandshaking _ ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_reachable_shape st1)
  | LocalInstallTrafficKeysForRole role_install, ControlHandshaking _ ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_start == hs0.hs_start);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_server_hello == hs0.hs_server_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_reachable_shape st1)
  | LocalValidateCertificate peer, ControlHandshaking HsCertificateReceived ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_reachable_shape st1)
  | LocalVerifyCertificateSignature cv, ControlHandshaking HsCertificateVerifyReceived ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_reachable_shape st1)
  | LocalVerifyFinished fin, ControlHandshaking HsServerFinishedReceived ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (client_x25519_reachable_shape st1)
  | LocalDeliverApplicationData bytes, ControlApplicationData ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake == hs0);
    assert (client_x25519_reachable_shape st1)
  | LocalFail err, _ ->
    assert (st1.cs_model == fail_model st0.cs_model err);
    assert (client_x25519_reachable_shape st1)
  | _, _ ->
    assert False

let lemma_legal_local_event_server_x25519_reachable_shape
  (st0:connection_state)
  (local:local_event)
  (st1:connection_state)
  : Lemma
      (requires
        server_x25519_reachable_shape st0 /\
        st0.cs_model.model_config.config_role == ServerEndpoint /\
        st0.cs_model.model_handshake.hs_keys.ks_shared_secret == None /\
        legal_local_event st0.cs_model local /\
        step_local_event st0.cs_model local == Some st1.cs_model)
      (ensures server_x25519_reachable_shape st1)
=
  let hs0 = st0.cs_model.model_handshake in
  match local, st0.cs_model.model_control with
  | LocalStartServer, ControlNew ->
    assert (st1.cs_model.model_handshake.hs_server_selection == None);
    assert (server_x25519_reachable_shape st1)
  | LocalSelectServerParameters selection, ControlHandshaking HsClientHelloReceived ->
    assert (hs0.hs_keys.ks_shared_secret == None);
    assert (hs0.hs_client_hello == Some selection.server_selected_client_hello);
    (match selection.server_key_share_private with
     | Some server_sk ->
       assert (C.x25519_public_from_private server_sk ==
         selection.server_key_share_public)
     | None ->
       ());
    assert (server_x25519_reachable_shape st1)
  | LocalDeriveSharedSecret shared, ControlHandshaking HsClientHelloReceived ->
    assert (server_selected_client_hello_reachable_shape st0);
    (match hs0.hs_server_selection with
     | Some selection ->
       (* The group comes from the selection, which names it; the legal_event arm
          and server_x25519_pre_server_hello_projection agree on that reading. *)
       let g = server_selected_kex_group selection in
       (match server_kex_private selection g with
        | Some server_sk ->
          assert (hs0.hs_client_hello ==
            Some selection.server_selected_client_hello);
          lemma_server_kex_public_from_private selection g;
          assert (C.kex_public_from_private g server_sk ==
            server_kex_public selection g);
          (match client_hello_kex selection.server_selected_client_hello g with
           | Some ch_ks ->
             assert (C.kex_shared g server_sk ch_ks == Some shared)
           | None -> assert False)
        | None ->
          assert False)
     | None ->
       assert False);
    assert (server_x25519_reachable_shape st1)
  | LocalInstallTrafficKeys install, ControlHandshaking _ ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_reachable_shape st1)
  | LocalInstallTrafficKeysForRole role_install, ControlHandshaking _ ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake.hs_server_selection == hs0.hs_server_selection);
    assert (st1.cs_model.model_handshake.hs_client_hello == hs0.hs_client_hello);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_reachable_shape st1)
  | LocalSignCertificateVerify cv, ControlHandshaking HsServerEncryptedFlightSent ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_reachable_shape st1)
  | LocalVerifyClientFinished fin, ControlHandshaking HsClientFinishedReceived ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret ==
      hs0.hs_keys.ks_shared_secret);
    assert (server_x25519_reachable_shape st1)
  | LocalDeliverApplicationData bytes, ControlApplicationData ->
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    assert (st1.cs_model.model_control == st0.cs_model.model_control);
    assert (st1.cs_model.model_handshake == hs0);
    assert (server_x25519_reachable_shape st1)
  | LocalFail err, _ ->
    assert (st1.cs_model == fail_model st0.cs_model err);
    assert (server_x25519_reachable_shape st1)
  | _, _ ->
    assert False

(* The ClientHello now carries two KeyShareEntry values (X25519 and secp256r1),
   so the `kse_list_find_x25519` walk needs one more unfolding than before. *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 60"
let lemma_connection_delta_client_x25519_reachable_shape
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        client_x25519_reachable_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures client_x25519_reachable_shape st1)
=
  assert (exists delta. legal_connection_delta st0 delta st1);
  let delta_w =
    ID.indefinite_description_ghost
      connection_delta
      (fun delta -> legal_connection_delta st0 delta st1) in
  let delta : connection_delta = delta_w in
  assert (legal_connection_delta st0 delta st1);
  assert (legal_event st0.cs_model delta.delta_event);
  assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
  lemma_step_model_preserves_config_for_x25519_reachable_shape
    st0.cs_model
    delta.delta_event
    st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  if st0.cs_model.model_config.config_role == ClientEndpoint then
    match st0.cs_model.model_handshake.hs_keys.ks_shared_secret with
    | Some _ ->
      lemma_legal_connection_delta_stable_client_x25519_key_share_projection
        st0
        delta
        st1;
      assert (client_x25519_reachable_shape st1)
    | None ->
      (match delta.delta_event with
       | ConnLocalEvent local ->
         assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
           step_local_event st0.cs_model local);
         assert (step_model st0.cs_model (ConnLocalEvent local) == Some st1.cs_model);
         (match local, st0.cs_model.model_control with
          | LocalStartHandshake start, ControlNew ->
            assert (legal_local_event st0.cs_model local);
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            (match start.start_client_key_share_private with
             | Some client_sk ->
               assert (C.x25519_public_from_private client_sk ==
                 start.start_client_key_share_public)
             | None ->
               ());
            assert (client_x25519_reachable_shape st1)
          | LocalDeriveSharedSecret shared, ControlHandshaking HsServerHelloReceived ->
            assert (client_x25519_pre_shared_secret_projection st0);
            assert (legal_local_event st0.cs_model local);
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            (match
              st0.cs_model.model_handshake.hs_start,
              st0.cs_model.model_handshake.hs_client_hello,
              st0.cs_model.model_handshake.hs_server_hello
            with
            | Some start, Some ch, Some sh ->
              (* Only the negotiated group's private key need exist. *)
              (match server_hello_kex sh with
               | Some (| g, sh_ks |) ->
                 assert (client_hello_kex ch g == Some (start_kex_public start g));
                 (match start_kex_private start g with
                  | Some sk ->
                    assert (C.kex_public_from_private g sk == start_kex_public start g);
                    assert (C.kex_shared g sk sh_ks == Some shared)
                  | None -> assert False)
               | None -> assert False)
            | _, _, _ ->
              assert False);
            assert (stable_client_x25519_key_share_projection st1);
            assert (client_x25519_reachable_shape st1)
          | _, _ ->
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            lemma_legal_local_event_client_x25519_reachable_shape st0 local st1)
       | ConnNetworkEvent msg ->
         assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
           step_tls_message
             st0.cs_model
             msg.CL.message_direction
             msg.CL.message_value);
         assert (step_model st0.cs_model (ConnNetworkEvent msg) == Some st1.cs_model);
         (match msg.CL.message_direction, msg.CL.message_value, st0.cs_model.model_control with
          | CL.Sent, M.TlsHandshake (M.ClientHello ch), ControlHandshaking HsStarted ->
            assert (legal_tls_message
              st0.cs_model
              msg.CL.message_direction
              msg.CL.message_value);
            assert (step_tls_message
              st0.cs_model
              msg.CL.message_direction
              msg.CL.message_value == Some st1.cs_model);
            assert (client_x25519_reachable_shape st0);
            (match st0.cs_model.model_handshake.hs_start with
            | Some start ->
              assert (client_hello_key_share ch ==
                Some start.start_client_key_share_public);
              assert (client_hello_p256_key_share ch ==
                Some start.start_client_p256_public);
              introduce forall (g:C.kex_group).
                client_hello_kex ch g == Some (start_kex_public start g) /\
                (match start_kex_private start g with
                 | Some sk -> C.kex_public_from_private g sk == start_kex_public start g
                 | None -> True)
              with (match g with | C.KexX25519 -> () | C.KexP256 -> ())
            | None ->
             assert False);
            assert (client_x25519_reachable_shape st1)
          | CL.Received, M.TlsHandshake (M.ServerHello _), ControlHandshaking HsClientHelloSent ->
            assert (client_x25519_pre_shared_secret_projection st0);
            assert (legal_tls_message
              st0.cs_model
              msg.CL.message_direction
              msg.CL.message_value);
            assert (step_tls_message
              st0.cs_model
              msg.CL.message_direction
              msg.CL.message_value == Some st1.cs_model);
            assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret == None);
            assert (client_x25519_reachable_shape st1)
          | _, M.TlsChangeCipherSpec, ControlHandshaking _ ->
            assert (step_tls_message
              st0.cs_model
              msg.CL.message_direction
              msg.CL.message_value == Some st1.cs_model);
            assert (st1.cs_model == st0.cs_model);
            assert (client_x25519_reachable_shape st1)
          | _, _, _ ->
            (match msg.CL.message_value, msg.CL.message_direction, st0.cs_model.model_control with
             | M.TlsHandshake (M.ClientHello _), CL.Sent, ControlHandshaking HsStarted
             | M.TlsHandshake (M.ClientHello _), CL.Received, ControlHandshaking HsAwaitingClientHello
             | M.TlsHandshake (M.ServerHello _), CL.Received, ControlHandshaking HsClientHelloSent
             | M.TlsHandshake (M.ServerHello _), CL.Sent, ControlHandshaking HsClientHelloReceived
             | M.TlsHandshake (M.EncryptedExtensions _), CL.Sent, ControlHandshaking HsServerHelloSent
             | M.TlsHandshake (M.Certificate _), CL.Sent, ControlHandshaking HsServerEncryptedFlightSent
             | M.TlsHandshake (M.CertificateVerify _), CL.Sent, ControlHandshaking HsServerEncryptedFlightSent
             | M.TlsHandshake (M.Finished _), CL.Sent, ControlHandshaking HsServerEncryptedFlightSent
             | M.TlsHandshake (M.EncryptedExtensions _), CL.Received, ControlHandshaking HsServerHelloReceived
             | M.TlsHandshake (M.Certificate _), CL.Received, ControlHandshaking HsEncryptedExtensionsReceived
             | M.TlsHandshake (M.CertificateVerify _), CL.Received, ControlHandshaking HsCertificateValidated
             | M.TlsHandshake (M.Finished _), CL.Received, ControlHandshaking HsCertificateVerifyVerified
             | M.TlsHandshake (M.Finished _), CL.Received, ControlHandshaking HsServerFinishedSent
             | M.TlsHandshake (M.Finished _), CL.Sent, ControlHandshaking HsServerFinishedVerified
             | M.TlsHandshake M.HelloRetryRequest, CL.Received, ControlHandshaking HsClientHelloSent
             | M.TlsApplicationData _, _, ControlApplicationData
             | M.TlsIgnoredPostHandshake _, CL.Received, ControlApplicationData
             | M.TlsKeyUpdate _, _, ControlApplicationData
             | M.TlsAlert T.Close_notify, CL.Sent, ControlApplicationData
             | M.TlsAlert T.Close_notify, CL.Received, ControlApplicationData
             | M.TlsAlert T.Close_notify, CL.Received, ControlClosing
             | M.TlsAlert _, _, _
             | M.TlsChangeCipherSpec, _, ControlHandshaking _ ->
               assert (step_tls_message
                 st0.cs_model
                 msg.CL.message_direction
                 msg.CL.message_value == Some st1.cs_model);
               assert (client_x25519_reachable_shape st1)
             | _, _, _ ->
               assert False))
       | ConnProtectedHandshake step ->
         assert (legal_protected_handshake_step st0.cs_model step);
         assert_norm (
           step_model st0.cs_model (ConnProtectedHandshake step) ==
             step_protected_handshake st0.cs_model step);
         assert (step_protected_handshake st0.cs_model step == Some st1.cs_model);
         if step.protected_handshake_buffering
         then
           (* Buffering leaves the control state and key schedule untouched. *)
           assert (client_x25519_reachable_shape st1)
         else begin
         (match step.protected_handshake_message, st0.cs_model.model_control with
           | M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived ->
             assert (st1.cs_model.model_control ==
             ControlHandshaking HsEncryptedExtensionsReceived)
           | M.Certificate _, ControlHandshaking HsEncryptedExtensionsReceived ->
             assert (st1.cs_model.model_control ==
             ControlHandshaking HsCertificateReceived)
           | M.CertificateVerify _, ControlHandshaking HsCertificateValidated ->
             assert (st1.cs_model.model_control ==
             ControlHandshaking HsCertificateVerifyReceived)
           | M.Finished _, ControlHandshaking HsCertificateVerifyVerified ->
             assert (st1.cs_model.model_control ==
             ControlHandshaking HsServerFinishedVerified)
           | _, _ -> assert False);
         assert (st1.cs_model.model_handshake.hs_keys.ks_shared_secret == None);
         assert (client_x25519_reachable_shape st1) end)
#pop-options

#restart-solver
let lemma_connection_delta_server_x25519_reachable_shape
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        server_x25519_reachable_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures server_x25519_reachable_shape st1)
=
  assert (exists delta. legal_connection_delta st0 delta st1);
  let delta_w =
    ID.indefinite_description_ghost
      connection_delta
      (fun delta -> legal_connection_delta st0 delta st1) in
  let delta : connection_delta = delta_w in
  assert (legal_connection_delta st0 delta st1);
  assert (legal_event st0.cs_model delta.delta_event);
  assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
  lemma_step_model_preserves_config_for_x25519_reachable_shape
    st0.cs_model
    delta.delta_event
    st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  if st0.cs_model.model_config.config_role == ServerEndpoint then
    match st0.cs_model.model_handshake.hs_keys.ks_shared_secret with
    | Some _ ->
      (match st0.cs_model.model_control with
       | ControlHandshaking HsClientHelloReceived ->
         (match delta.delta_event with
          | ConnNetworkEvent msg ->
            assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
              step_tls_message
                st0.cs_model
                msg.CL.message_direction
                msg.CL.message_value);
            assert (step_model st0.cs_model (ConnNetworkEvent msg) == Some st1.cs_model);
            (match msg.CL.message_direction, msg.CL.message_value with
             | CL.Sent, M.TlsHandshake (M.ServerHello sh) ->
               assert (server_x25519_pre_server_hello_projection st0);
               assert (legal_tls_message
                 st0.cs_model
                 msg.CL.message_direction
                 msg.CL.message_value);
               assert (step_tls_message
                 st0.cs_model
                 msg.CL.message_direction
                 msg.CL.message_value == Some st1.cs_model);
               (match
                 st0.cs_model.model_handshake.hs_server_selection,
                 st0.cs_model.model_handshake.hs_client_hello,
                 st0.cs_model.model_handshake.hs_keys.ks_shared_secret
               with
               | Some selection, Some ch, Some shared ->
                 // The group comes from the selection, which names it; the
                 // ServerHello just sent carries that group's share.
                 let g = server_selected_kex_group selection in
                 (match server_kex_private selection g with
                  | Some server_sk ->
                    assert (server_hello_kex sh ==
                      Some (| g, server_kex_public selection g |));
                    lemma_server_kex_public_from_private selection g;
                    assert (C.kex_public_from_private g server_sk ==
                      server_kex_public selection g);
                    (match client_hello_kex ch g with
                     | Some ch_ks ->
                       assert (C.kex_shared g server_sk ch_ks == Some shared)
                     | None -> assert False)
                  | None ->
                    assert False)
               | _, _, _ ->
                 assert False);
               assert (stable_server_x25519_key_share_projection st1);
               assert (server_x25519_reachable_shape st1)
             | _, _ ->
               assert (step_tls_message
                 st0.cs_model
                 msg.CL.message_direction
                 msg.CL.message_value == Some st1.cs_model);
               assert (server_x25519_reachable_shape st1))
          | ConnLocalEvent local ->
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_model st0.cs_model (ConnLocalEvent local) == Some st1.cs_model);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            assert (server_x25519_reachable_shape st1)
          | ConnProtectedHandshake step ->
            assert False)
       | ControlFailed _ ->
         lemma_step_model_from_failed_results_failed
           st0.cs_model
           delta.delta_event
           st1.cs_model;
        // A step from a failed state lands in `fail_model`, which preserves the
        // handshake state; hence the server x25519 key-share projections (which
        // depend only on the handshake state) are transported from st0 to st1.
        (match delta.delta_event with
         | ConnLocalEvent local ->
           (match local with
            | LocalFail err ->
              assert (st1.cs_model == fail_model st0.cs_model err)
            | _ -> assert False)
         | ConnNetworkEvent msg ->
           (match msg.CL.message_value with
            | M.TlsAlert alert ->
              assert (st1.cs_model == fail_model st0.cs_model (T.AlertError alert))
            | _ -> assert False)
         | ConnProtectedHandshake step ->
           assert False);
        assert (st1.cs_model.model_handshake == st0.cs_model.model_handshake);
        assert (server_x25519_reachable_shape st1)
       | _ ->
         lemma_legal_connection_delta_stable_server_x25519_key_share_projection
           st0
           delta
           st1;
         assert (server_x25519_reachable_shape st1))
    | None ->
      (match delta.delta_event with
       | ConnLocalEvent local ->
         assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
           step_local_event st0.cs_model local);
         assert (step_model st0.cs_model (ConnLocalEvent local) == Some st1.cs_model);
         (match local, st0.cs_model.model_control with
          | LocalStartServer, ControlNew ->
            assert (legal_local_event st0.cs_model local);
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            assert (server_x25519_reachable_shape st1)
          | LocalSelectServerParameters selection, ControlHandshaking HsClientHelloReceived ->
            assert (legal_local_event st0.cs_model local);
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            assert (st0.cs_model.model_handshake.hs_keys.ks_shared_secret == None);
            assert (server_x25519_reachable_shape st1)
          | LocalDeriveSharedSecret shared, ControlHandshaking HsClientHelloReceived ->
            assert (server_selected_client_hello_reachable_shape st0);
            assert (legal_local_event st0.cs_model local);
            assert_norm (step_model st0.cs_model (ConnLocalEvent local) ==
              step_local_event st0.cs_model local);
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            (match st0.cs_model.model_handshake.hs_server_selection with
            | Some selection ->
              let g = server_selected_kex_group selection in
              (match server_kex_private selection g with
               | Some server_sk ->
                 assert (st0.cs_model.model_handshake.hs_client_hello ==
                   Some selection.server_selected_client_hello);
                 lemma_server_kex_public_from_private selection g;
                 assert (C.kex_public_from_private g server_sk ==
                   server_kex_public selection g);
                 (match client_hello_kex selection.server_selected_client_hello g with
                  | Some ch_ks ->
                    assert (C.kex_shared g server_sk ch_ks == Some shared)
                  | None -> assert False)
               | None ->
                 assert False)
            | None ->
              assert False);
            assert (server_x25519_reachable_shape st1)
          | _, _ ->
            assert (step_local_event st0.cs_model local == Some st1.cs_model);
            lemma_legal_local_event_server_x25519_reachable_shape st0 local st1)
       | ConnNetworkEvent msg ->
         assert_norm (step_model st0.cs_model (ConnNetworkEvent msg) ==
           step_tls_message
             st0.cs_model
             msg.CL.message_direction
             msg.CL.message_value);
         assert (step_model st0.cs_model (ConnNetworkEvent msg) == Some st1.cs_model);
         (match msg.CL.message_direction, msg.CL.message_value, st0.cs_model.model_control with
          | CL.Received, M.TlsHandshake (M.ClientHello _), ControlHandshaking HsAwaitingClientHello ->
            assert (step_tls_message
              st0.cs_model
              msg.CL.message_direction
              msg.CL.message_value == Some st1.cs_model);
            assert (st0.cs_model.model_handshake.hs_server_selection == None);
            assert (server_x25519_reachable_shape st1)
          | _, M.TlsChangeCipherSpec, ControlHandshaking _ ->
            assert (step_tls_message
              st0.cs_model
              msg.CL.message_direction
              msg.CL.message_value == Some st1.cs_model);
            assert (st1.cs_model == st0.cs_model);
            assert (server_x25519_reachable_shape st1)
          | _, _, _ ->
            (match msg.CL.message_value, msg.CL.message_direction, st0.cs_model.model_control with
             | M.TlsHandshake (M.ClientHello _), CL.Sent, ControlHandshaking HsStarted
             | M.TlsHandshake (M.ClientHello _), CL.Received, ControlHandshaking HsAwaitingClientHello
             | M.TlsHandshake (M.ServerHello _), CL.Received, ControlHandshaking HsClientHelloSent
             | M.TlsHandshake (M.ServerHello _), CL.Sent, ControlHandshaking HsClientHelloReceived
             | M.TlsHandshake (M.EncryptedExtensions _), CL.Sent, ControlHandshaking HsServerHelloSent
             | M.TlsHandshake (M.Certificate _), CL.Sent, ControlHandshaking HsServerEncryptedFlightSent
             | M.TlsHandshake (M.CertificateVerify _), CL.Sent, ControlHandshaking HsServerEncryptedFlightSent
             | M.TlsHandshake (M.Finished _), CL.Sent, ControlHandshaking HsServerEncryptedFlightSent
             | M.TlsHandshake (M.EncryptedExtensions _), CL.Received, ControlHandshaking HsServerHelloReceived
             | M.TlsHandshake (M.Certificate _), CL.Received, ControlHandshaking HsEncryptedExtensionsReceived
             | M.TlsHandshake (M.CertificateVerify _), CL.Received, ControlHandshaking HsCertificateValidated
             | M.TlsHandshake (M.Finished _), CL.Received, ControlHandshaking HsCertificateVerifyVerified
             | M.TlsHandshake (M.Finished _), CL.Received, ControlHandshaking HsServerFinishedSent
             | M.TlsHandshake (M.Finished _), CL.Sent, ControlHandshaking HsServerFinishedVerified
             | M.TlsHandshake M.HelloRetryRequest, CL.Received, ControlHandshaking HsClientHelloSent
             | M.TlsApplicationData _, _, ControlApplicationData
             | M.TlsIgnoredPostHandshake _, CL.Received, ControlApplicationData
             | M.TlsKeyUpdate _, _, ControlApplicationData
             | M.TlsAlert T.Close_notify, CL.Sent, ControlApplicationData
             | M.TlsAlert T.Close_notify, CL.Received, ControlApplicationData
             | M.TlsAlert T.Close_notify, CL.Received, ControlClosing
             | M.TlsAlert _, _, _
             | M.TlsChangeCipherSpec, _, ControlHandshaking _ ->
               assert (step_tls_message
                 st0.cs_model
                 msg.CL.message_direction
                 msg.CL.message_value == Some st1.cs_model);
               assert (server_x25519_reachable_shape st1)
             | _, _, _ ->
               assert False))
       | ConnProtectedHandshake step ->
         assert False)

let lemma_initial_client_x25519_reachable_shape
  (cfg:connection_config)
  : Lemma
      (ensures client_x25519_reachable_shape (initial cfg))
=
  ()

let lemma_initial_server_x25519_reachable_shape
  (cfg:connection_config)
  : Lemma
      (ensures server_x25519_reachable_shape (initial cfg))
=
  ()

let lemma_connection_state_single_step_client_x25519_reachable_shape
  (u:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (client_x25519_reachable_shape y);
            (connection_state_single_step x y)}
          client_x25519_reachable_shape x /\
          connection_state_single_step x y ==>
          client_x25519_reachable_shape y)
=
  introduce forall x y.
    client_x25519_reachable_shape x /\
    connection_state_single_step x y ==>
    client_x25519_reachable_shape y
  with
    introduce _ ==> _ with
    lemma_connection_delta_client_x25519_reachable_shape x y

let lemma_connection_state_single_step_server_x25519_reachable_shape
  (u:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (server_x25519_reachable_shape y);
            (connection_state_single_step x y)}
          server_x25519_reachable_shape x /\
          connection_state_single_step x y ==>
          server_x25519_reachable_shape y)
=
  introduce forall x y.
    server_x25519_reachable_shape x /\
    connection_state_single_step x y ==>
    server_x25519_reachable_shape y
  with
    introduce _ ==> _ with
    lemma_connection_delta_server_x25519_reachable_shape x y

let lemma_connection_state_consistent_client_x25519_reachable_shape
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures client_x25519_reachable_shape st)
=
  let p = client_x25519_reachable_shape in
  lemma_initial_client_x25519_reachable_shape st.cs_model.model_config;
  lemma_connection_state_single_step_client_x25519_reachable_shape ();
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)

let lemma_connection_state_consistent_server_x25519_reachable_shape
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures server_x25519_reachable_shape st)
=
  let p = server_x25519_reachable_shape in
  lemma_initial_server_x25519_reachable_shape st.cs_model.model_config;
  lemma_connection_state_single_step_server_x25519_reachable_shape ();
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)

let lemma_connection_state_consistent_server_selection_private_shape
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlHandshaking HsClientHelloReceived /\
        st.cs_model.model_handshake.hs_keys.ks_shared_secret == None /\
        Some? st.cs_model.model_handshake.hs_server_selection)
      (ensures
        (match st.cs_model.model_handshake.hs_server_selection with
         | Some selection ->
           server_selection_key_share_consistent selection /\
           st.cs_model.model_handshake.hs_client_hello ==
             Some selection.server_selected_client_hello
         | None -> False))
=
  lemma_connection_state_consistent_server_x25519_reachable_shape st;
  assert (server_x25519_reachable_shape st);
  assert (st.cs_model.model_config.config_role == ServerEndpoint);
  assert (st.cs_model.model_handshake.hs_keys.ks_shared_secret == None);
  assert (server_selected_client_hello_reachable_shape st);
  match st.cs_model.model_handshake.hs_server_selection with
  | Some selection ->
    assert (st.cs_model.model_handshake.hs_client_hello ==
      Some selection.server_selected_client_hello);
    (match selection.server_key_share_private with
     | Some server_sk ->
       assert (C.x25519_public_from_private server_sk ==
         selection.server_key_share_public)
     | None -> ())
  | None -> assert False

let lemma_connection_state_consistent_server_pre_server_hello_shape
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlHandshaking HsClientHelloReceived /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret)
      (ensures
        (match st.cs_model.model_handshake.hs_server_selection with
         | Some selection ->
           server_selection_key_share_consistent selection /\
           Some? selection.server_key_share_private /\
           (* G2 stage S6.8d: the selection was made from the stored
              ClientHello.  Needed by the ServerHello writer, which reads the
              negotiated group off the stored ClientHello's metadata and has to
              match it against the group the selection names. *)
           st.cs_model.model_handshake.hs_client_hello ==
             Some selection.server_selected_client_hello
         | None -> False))
=
  lemma_connection_state_consistent_server_x25519_reachable_shape st;
  assert (server_x25519_reachable_shape st);
  assert (server_x25519_pre_server_hello_projection st);
  match st.cs_model.model_handshake.hs_server_selection with
  | Some selection ->
    (match selection.server_key_share_private with
     | Some server_sk ->
       assert (C.x25519_public_from_private server_sk ==
         selection.server_key_share_public)
     | None -> assert False)
  | None -> assert False

let server_handshake_write_key_shape_control
  (control:connection_control_state)
  : bool =
  match control with
  | ControlNew
  | ControlHandshaking HsAwaitingClientHello
  | ControlHandshaking HsClientHelloReceived
  | ControlHandshaking HsServerHelloSent
  | ControlHandshaking HsServerEncryptedFlightSent ->
    true
  | _ ->
    false

let server_handshake_write_key_reachable_shape
  (model:connection_model)
  : prop =
  model.model_config.config_role == ServerEndpoint ==>
  server_handshake_write_key_shape_control model.model_control == true ==>
  Some? model.model_handshake.hs_keys.ks_server_handshake_traffic ==>
  traffic_material_option_matches_record_direction
    model.model_handshake.hs_keys.ks_server_handshake_traffic
    model.model_record.record_write

let lemma_traffic_material_option_matches_record_direction_next_seq
  (material:option traffic_key_material)
  (st:R.direction_state)
  : Lemma
      (requires traffic_material_option_matches_record_direction material st)
      (ensures traffic_material_option_matches_record_direction material (R.next_seq st))
=
  match material with
  | Some _ -> ()
  | None -> assert False

let lemma_server_handshake_write_key_shape_unchanged
  (model:connection_model)
  (model':connection_model)
  : Lemma
      (requires
        server_handshake_write_key_reachable_shape model /\
        model'.model_config == model.model_config /\
        model'.model_control == model.model_control /\
        model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
          model.model_handshake.hs_keys.ks_server_handshake_traffic /\
        model'.model_record.record_write == model.model_record.record_write)
      (ensures server_handshake_write_key_reachable_shape model')
=
  ()

let lemma_server_handshake_write_key_shape_control_advance
  (model:connection_model)
  (model':connection_model)
  : Lemma
      (requires
        server_handshake_write_key_reachable_shape model /\
        model'.model_config == model.model_config /\
        model.model_config.config_role == ServerEndpoint /\
        server_handshake_write_key_shape_control model.model_control == true /\
        server_handshake_write_key_shape_control model'.model_control == true /\
        model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
          model.model_handshake.hs_keys.ks_server_handshake_traffic /\
        model'.model_record.record_write == model.model_record.record_write)
      (ensures server_handshake_write_key_reachable_shape model')
=
  if Some? model'.model_handshake.hs_keys.ks_server_handshake_traffic then begin
    assert (Some? model.model_handshake.hs_keys.ks_server_handshake_traffic);
    assert (traffic_material_option_matches_record_direction
      model.model_handshake.hs_keys.ks_server_handshake_traffic
      model.model_record.record_write)
  end

let lemma_server_handshake_write_key_shape_next_seq
  (model:connection_model)
  (model':connection_model)
  : Lemma
      (requires
        server_handshake_write_key_reachable_shape model /\
        model'.model_config == model.model_config /\
        model.model_config.config_role == ServerEndpoint /\
        server_handshake_write_key_shape_control model.model_control == true /\
        server_handshake_write_key_shape_control model'.model_control == true /\
        model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
          model.model_handshake.hs_keys.ks_server_handshake_traffic /\
        model'.model_record.record_write == R.next_seq model.model_record.record_write)
      (ensures server_handshake_write_key_reachable_shape model')
=
  if model'.model_config.config_role == ServerEndpoint then begin
    assert (model.model_config.config_role == ServerEndpoint);
    if server_handshake_write_key_shape_control model'.model_control then begin
      if Some? model'.model_handshake.hs_keys.ks_server_handshake_traffic then begin
        assert (Some? model.model_handshake.hs_keys.ks_server_handshake_traffic);
        assert (traffic_material_option_matches_record_direction
          model.model_handshake.hs_keys.ks_server_handshake_traffic
          model.model_record.record_write);
        lemma_traffic_material_option_matches_record_direction_next_seq
          model.model_handshake.hs_keys.ks_server_handshake_traffic
          model.model_record.record_write
      end
    end
  end

let lemma_step_model_server_handshake_write_key_reachable_shape
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires
        server_handshake_write_key_reachable_shape model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures server_handshake_write_key_reachable_shape model')
=
  lemma_step_model_preserves_config_for_x25519_reachable_shape model ev model';
  assert (model'.model_config == model.model_config);
  if model'.model_config.config_role == ServerEndpoint then begin
    assert (model.model_config.config_role == ServerEndpoint);
    match ev with
    | ConnLocalEvent local ->
      assert (legal_local_event model local);
      assert (step_local_event model local == Some model');
      (match local with
      | LocalStartServer ->
        (match model.model_control with
        | ControlNew ->
          assert (model'.model_control == ControlHandshaking HsAwaitingClientHello);
          assert (model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
            model.model_handshake.hs_keys.ks_server_handshake_traffic);
          assert (model'.model_record.record_write == model.model_record.record_write);
          lemma_server_handshake_write_key_shape_control_advance model model'
        | _ -> assert False)
      | LocalSelectServerParameters _ ->
        (match model.model_control with
        | ControlHandshaking HsClientHelloReceived ->
          assert (model'.model_control == model.model_control);
          assert (model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
            model.model_handshake.hs_keys.ks_server_handshake_traffic);
          assert (model'.model_record.record_write == model.model_record.record_write);
          lemma_server_handshake_write_key_shape_unchanged model model'
        | _ -> assert False)
      | LocalDeriveSharedSecret _ ->
        (match model.model_control with
        | ControlHandshaking HsClientHelloReceived ->
          assert (model'.model_control == model.model_control);
          assert (model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
            model.model_handshake.hs_keys.ks_server_handshake_traffic);
          assert (model'.model_record.record_write == model.model_record.record_write);
          lemma_server_handshake_write_key_shape_unchanged model model'
        | ControlHandshaking HsServerHelloReceived ->
          assert False
        | _ -> assert False)
      | LocalInstallTrafficKeys _ ->
        assert False
      | LocalInstallTrafficKeysForRole role_install ->
        (match model.model_control with
        | ControlHandshaking stage ->
          assert (role_install.install_role == ServerEndpoint);
          let install = role_install.install_payload in
          assert (traffic_install_allowed_at_stage_for_role
            ServerEndpoint
            stage
            install);
          (match install.install_epoch, install.install_direction with
          | TrafficHandshake, TrafficWrite ->
            assert (stage == HsServerHelloSent);
            assert (model'.model_control == model.model_control);
            assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
            assert (model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
              Some install.install_material);
            assert (model'.model_record.record_write ==
              R.install_keys
                model.model_record.record_write
                R.Handshake
                install.install_material.traffic_alg install.install_material.traffic_key
                install.install_material.traffic_iv);
            assert (traffic_material_option_matches_record_direction
              model'.model_handshake.hs_keys.ks_server_handshake_traffic
              model'.model_record.record_write)
          | TrafficHandshake, TrafficRead ->
            assert (stage == HsServerHelloSent);
            assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
            assert (model'.model_control == model.model_control);
            assert (model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
              model.model_handshake.hs_keys.ks_server_handshake_traffic);
            assert (model'.model_record.record_write == model.model_record.record_write);
            lemma_server_handshake_write_key_shape_unchanged model model'
          | TrafficApplication, TrafficWrite ->
            assert (stage == HsServerFinishedSent)
          | TrafficApplication, TrafficRead ->
            assert (stage == HsClientFinishedReceived))
        | _ -> assert False)
      | LocalSignCertificateVerify _ ->
        (match model.model_control with
        | ControlHandshaking HsServerEncryptedFlightSent ->
          assert (model'.model_control == model.model_control);
          assert (model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
            model.model_handshake.hs_keys.ks_server_handshake_traffic);
          assert (model'.model_record.record_write == model.model_record.record_write);
          lemma_server_handshake_write_key_shape_unchanged model model'
        | _ -> assert False)
      | LocalVerifyClientFinished _ ->
        (match model.model_control with
        | ControlHandshaking HsClientFinishedReceived -> ()
        | _ -> assert False)
      | LocalDeliverApplicationData _ ->
        (match model.model_control with
        | ControlApplicationData -> ()
        | _ -> assert False)
      | LocalFail _ ->
        ()
      | _ ->
        assert False)
    | ConnNetworkEvent msg ->
      assert (legal_tls_message
        model
        msg.CL.message_direction
        msg.CL.message_value);
      assert (step_tls_message
        model
        msg.CL.message_direction
        msg.CL.message_value == Some model');
      (match msg.CL.message_value, msg.CL.message_direction, model.model_control with
      | M.TlsHandshake (M.ClientHello _), CL.Received,
        ControlHandshaking HsAwaitingClientHello ->
        assert (model'.model_control == ControlHandshaking HsClientHelloReceived);
        assert (model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
          model.model_handshake.hs_keys.ks_server_handshake_traffic);
        assert (model'.model_record.record_write == model.model_record.record_write);
        lemma_server_handshake_write_key_shape_control_advance model model'
      | M.TlsHandshake (M.ServerHello _), CL.Sent,
        ControlHandshaking HsClientHelloReceived ->
        assert (model'.model_control == ControlHandshaking HsServerHelloSent);
        assert (model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
          model.model_handshake.hs_keys.ks_server_handshake_traffic);
        assert (model'.model_record.record_write == model.model_record.record_write);
        lemma_server_handshake_write_key_shape_control_advance model model'
      | M.TlsHandshake (M.EncryptedExtensions _), CL.Sent,
        ControlHandshaking HsServerHelloSent
      | M.TlsHandshake (M.Certificate _), CL.Sent,
        ControlHandshaking HsServerEncryptedFlightSent
      | M.TlsHandshake (M.CertificateVerify _), CL.Sent,
        ControlHandshaking HsServerEncryptedFlightSent ->
        assert (model'.model_control == ControlHandshaking HsServerEncryptedFlightSent);
        assert (model'.model_handshake.hs_keys.ks_server_handshake_traffic ==
          model.model_handshake.hs_keys.ks_server_handshake_traffic);
        assert (model'.model_record.record_write == R.next_seq model.model_record.record_write);
        lemma_server_handshake_write_key_shape_next_seq model model'
      | M.TlsHandshake (M.Finished _), CL.Sent,
        ControlHandshaking HsServerEncryptedFlightSent ->
        assert (model'.model_control == ControlHandshaking HsServerFinishedSent)
      | M.TlsHandshake (M.Finished _), CL.Received,
        ControlHandshaking HsServerFinishedSent ->
        // Model-Fix-1: the server processes the client Finished atomically and lands
        // directly at ControlApplicationData (installing the client's application READ
        // keys on record_read; record_write and ks_server_handshake_traffic unchanged).
        // server_handshake_write_key_shape_control ControlApplicationData == false, so
        // the write-key reachable-shape ensures is vacuous at the new landing stage.
        assert (model'.model_control == ControlApplicationData)
      | M.TlsApplicationData _, _, ControlApplicationData
      | M.TlsIgnoredPostHandshake _, _, ControlApplicationData
      | M.TlsKeyUpdate _, _, ControlApplicationData
      | M.TlsAlert T.Close_notify, _, ControlApplicationData
      | M.TlsAlert T.Close_notify, _, ControlClosing ->
        ()
      | M.TlsAlert _, _,
        _ ->
        ()
      | M.TlsChangeCipherSpec, _,
        ControlHandshaking _ ->
        assert (model' == model);
        lemma_server_handshake_write_key_shape_unchanged model model'
      | _ ->
        assert False)
    | ConnProtectedHandshake step ->
      assert False
  end

let lemma_connection_delta_server_handshake_write_key_reachable_shape
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        server_handshake_write_key_reachable_shape st0.cs_model /\
        connection_state_single_step st0 st1)
      (ensures server_handshake_write_key_reachable_shape st1.cs_model)
=
  match st1 with
  | _ ->
    assert (exists delta. legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        connection_delta
        (fun delta -> legal_connection_delta st0 delta st1) in
    let delta : connection_delta = delta_w in
    assert (legal_connection_delta st0 delta st1);
    assert (legal_event st0.cs_model delta.delta_event);
    assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
    lemma_step_model_server_handshake_write_key_reachable_shape
      st0.cs_model
      delta.delta_event
      st1.cs_model

let lemma_initial_server_handshake_write_key_reachable_shape
  (cfg:connection_config)
  : Lemma
      (ensures server_handshake_write_key_reachable_shape (initial_model cfg))
=
  ()

let lemma_connection_state_single_step_server_handshake_write_key_reachable_shape
  ()
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern (server_handshake_write_key_reachable_shape y.cs_model);
                     (connection_state_single_step x y)}
          server_handshake_write_key_reachable_shape x.cs_model /\
          connection_state_single_step x y ==>
          server_handshake_write_key_reachable_shape y.cs_model)
=
  introduce forall x y.
    server_handshake_write_key_reachable_shape x.cs_model /\
    connection_state_single_step x y ==>
    server_handshake_write_key_reachable_shape y.cs_model
  with
    introduce _ ==> _ with
    lemma_connection_delta_server_handshake_write_key_reachable_shape x y

let lemma_connection_state_consistent_server_handshake_write_key_reachable_shape
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures server_handshake_write_key_reachable_shape st.cs_model)
=
  let p (st:connection_state) =
    server_handshake_write_key_reachable_shape st.cs_model in
  lemma_initial_server_handshake_write_key_reachable_shape st.cs_model.model_config;
  lemma_connection_state_single_step_server_handshake_write_key_reachable_shape ();
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)

let lemma_server_handshake_write_record_has_keys
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        (st.cs_model.model_control == ControlHandshaking HsServerHelloSent \/
         st.cs_model.model_control == ControlHandshaking HsServerEncryptedFlightSent) /\
        Some? st.cs_model.model_handshake.hs_keys.ks_server_handshake_traffic)
      (ensures
        (match
          st.cs_model.model_record.record_write.R.key,
          st.cs_model.model_record.record_write.R.static_iv
        with
        | Some _, Some _ -> True
        | _, _ -> False))
=
  lemma_connection_state_consistent_server_handshake_write_key_reachable_shape st;
  assert (server_handshake_write_key_reachable_shape st.cs_model);
  assert (server_handshake_write_key_shape_control st.cs_model.model_control == true);
  assert (traffic_material_option_matches_record_direction
    st.cs_model.model_handshake.hs_keys.ks_server_handshake_traffic
    st.cs_model.model_record.record_write);
  match st.cs_model.model_handshake.hs_keys.ks_server_handshake_traffic with
  | Some _ -> ()
  | None -> assert False

let no_application_traffic_keys
  (keys:key_schedule_state)
  : prop =
  keys.ks_client_application_traffic == None /\
  keys.ks_server_application_traffic == None

let client_application_record_read_epoch_link
  (model:connection_model)
  : prop =
  Some? model.model_handshake.hs_keys.ks_server_application_traffic ==>
    model.model_record.record_read.R.epoch == R.Application

let client_application_record_write_epoch_link
  (model:connection_model)
  : prop =
  Some? model.model_handshake.hs_keys.ks_client_application_traffic ==>
    model.model_record.record_write.R.epoch == R.Application

let client_application_record_epoch_link
  (model:connection_model)
  : prop =
  client_application_record_read_epoch_link model /\
  client_application_record_write_epoch_link model

let server_application_record_read_epoch_link
  (model:connection_model)
  : prop =
  Some? model.model_handshake.hs_keys.ks_client_application_traffic ==>
    model.model_record.record_read.R.epoch == R.Application

let server_application_record_write_epoch_link
  (model:connection_model)
  : prop =
  Some? model.model_handshake.hs_keys.ks_server_application_traffic ==>
    model.model_record.record_write.R.epoch == R.Application

let server_application_record_epoch_link
  (model:connection_model)
  : prop =
  server_application_record_read_epoch_link model /\
  server_application_record_write_epoch_link model

let client_application_record_epoch_reachable_shape
  (model:connection_model)
  : prop =
  let keys = model.model_handshake.hs_keys in
  match model.model_control with
  | ControlNew
  | ControlHandshaking HsStarted
  | ControlHandshaking HsClientHelloSent
  | ControlHandshaking HsServerHelloReceived
  | ControlHandshaking HsEncryptedExtensionsReceived
  | ControlHandshaking HsCertificateReceived
  | ControlHandshaking HsCertificateValidated
  | ControlHandshaking HsCertificateVerifyReceived
  | ControlHandshaking HsCertificateVerifyVerified
  | ControlHandshaking HsServerFinishedReceived ->
    keys.ks_server_application_traffic == None /\
    // STAGE (b): the client installs its application WRITE key only at the
    // Finished send (HsServerFinishedVerified -> ControlApplicationData); the
    // legal local (TrafficApplication, TrafficWrite) install is a NO-OP on
    // record_write for a client (install_record_keys, StateMachine.fst:399), so
    // record_write stays at the Handshake epoch throughout the handshake.  This
    // pins app_wseq to 0 at the Finished send, discharging the record-seq pairing.
    model.model_record.record_write.R.epoch =!= R.Application
  | ControlHandshaking HsServerFinishedVerified ->
    client_application_record_read_epoch_link model /\
    (match keys.ks_server_application_traffic with
     | Some m -> traffic_material_matches_record_direction m model.model_record.record_read
     | None -> True) /\
    // STAGE (b): see the grouped handshaking arm above — record_write is still at
    // the Handshake epoch at the instant the Finished send installs the client
    // application write key.
    model.model_record.record_write.R.epoch =!= R.Application
  | ControlApplicationData ->
    application_record_keys_installed_for_role ClientEndpoint model /\
    client_application_record_epoch_link model
  | ControlClosing
  | ControlClosed ->
    // Strengthened (mirrors the CAD arm): the graceful-close controls are entered
    // ONLY from ControlApplicationData (Close_notify send/recv) or ControlClosing
    // (Close_notify recv), all of which already carry the both-direction key
    // installation; Close_notify's `next_seq` bumps only the record seq, leaving
    // key/iv (hence `application_record_keys_installed_for_role`) intact.  Carrying
    // it here lets a `consistent + Closing/Closed` endpoint recover the Application
    // read/write epochs WITHOUT the caller supplying keys-installed.
    application_record_keys_installed_for_role ClientEndpoint model /\
    client_application_record_epoch_link model
  | ControlFailed _ ->
    True
  | _ ->
    True

#restart-solver
let server_application_record_epoch_reachable_shape
  (model:connection_model)
  : prop =
  let keys = model.model_handshake.hs_keys in
  match model.model_control with
  | ControlNew
  | ControlHandshaking HsAwaitingClientHello
  | ControlHandshaking HsClientHelloReceived
  | ControlHandshaking HsServerHelloSent
  | ControlHandshaking HsServerEncryptedFlightSent ->
    no_application_traffic_keys keys /\
    // STAGE (b), server mirror: the server installs its application WRITE key only
    // at HsServerFinishedSent (LocalInstallServerApplicationTrafficKeys), which is
    // strictly AFTER every server handshake SEND (ServerHello .. Finished, all at
    // HsServerHelloSent/HsServerEncryptedFlightSent).  So record_write stays off
    // the Application epoch throughout the server's sending stages, pinning
    // app_wseq to 0 there — exactly the guard the send-delta lemma needs at a
    // server handshake send.
    model.model_record.record_write.R.epoch =!= R.Application
  | ControlHandshaking HsServerFinishedSent ->
    keys.ks_client_application_traffic == None /\
    server_application_record_write_epoch_link model /\
    (match keys.ks_server_application_traffic with
     | Some m -> traffic_material_matches_record_direction m model.model_record.record_write
     | None -> True)
  | ControlHandshaking HsClientFinishedReceived ->
    server_application_record_epoch_link model
  | ControlApplicationData ->
    application_record_keys_installed_for_role ServerEndpoint model /\
    server_application_record_epoch_link model
  | ControlClosing
  | ControlClosed ->
    // Strengthened, server mirror of the client Closing/Closed arm above.
    application_record_keys_installed_for_role ServerEndpoint model /\
    server_application_record_epoch_link model
  | ControlFailed _ ->
    True
  | _ ->
    True

let model_application_record_epoch_reachable_shape_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  match role with
  | ClientEndpoint ->
    model.model_config.config_role == ClientEndpoint ==>
      client_application_record_epoch_reachable_shape model
  | ServerEndpoint ->
    model.model_config.config_role == ServerEndpoint ==>
      server_application_record_epoch_reachable_shape model

let connection_application_record_epoch_reachable_shape_for_role
  (role:endpoint_role)
  (st:connection_state)
  : prop =
  model_application_record_epoch_reachable_shape_for_role role st.cs_model

let lemma_initial_application_record_epoch_reachable_shape_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma
      (ensures
        connection_application_record_epoch_reachable_shape_for_role
          role
          (initial cfg))
=
  ()

let rec lemma_advance_direction_records_preserves_epoch
  (st:R.direction_state)
  (n:nat)
  : Lemma
      (ensures (advance_direction_records st n).R.epoch == st.R.epoch)
      (decreases n)
=
  if n = 0 then ()
  else lemma_advance_direction_records_preserves_epoch st (n - 1)

let rec lemma_advance_direction_records_preserves_key_iv
  (st:R.direction_state)
  (n:nat)
  : Lemma
      (ensures
        (advance_direction_records st n).R.alg == st.R.alg /\
        (advance_direction_records st n).R.key == st.R.key /\
        (advance_direction_records st n).R.static_iv == st.R.static_iv)
      (decreases n)
=
  if n = 0 then ()
  else lemma_advance_direction_records_preserves_key_iv st (n - 1)

#push-options "--z3rlimit 200"
let lemma_step_model_application_record_epoch_reachable_shape_for_role
  (role:endpoint_role)
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires
        model_application_record_epoch_reachable_shape_for_role role model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures
        model_application_record_epoch_reachable_shape_for_role role model')
=
  lemma_step_model_preserves_config_for_x25519_reachable_shape model ev model';
  assert (model'.model_config == model.model_config);
  match role with
  | ClientEndpoint ->
    if model'.model_config.config_role == ClientEndpoint then begin
      assert (model.model_config.config_role == ClientEndpoint);
      assert (client_application_record_epoch_reachable_shape model);
      (match ev with
       | ConnLocalEvent local ->
         assert (legal_local_event model local);
         assert (step_local_event model local == Some model');
         (match local with
          | LocalStartHandshake _ ->
            (match model.model_control with
             | ControlNew ->
               assert (model.model_handshake.hs_keys.ks_server_application_traffic == None);
               assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None)
             | _ ->
               assert False)
          | LocalDeriveSharedSecret _ ->
            (match model.model_control with
             | ControlHandshaking HsServerHelloReceived ->
               assert (model.model_handshake.hs_keys.ks_server_application_traffic == None);
               assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None)
             | _ ->
               assert False)
          | LocalInstallTrafficKeys install ->
            (match model.model_control with
             | ControlHandshaking stage ->
               assert (traffic_install_allowed_at_stage stage install);
               (match install.install_epoch, install.install_direction with
                | TrafficHandshake, _ ->
                  assert (stage == HsServerHelloReceived);
                  assert (model.model_handshake.hs_keys.ks_server_application_traffic == None);
                  assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None)
                | TrafficApplication, TrafficRead ->
                  assert (stage == HsServerFinishedVerified);
                  assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
                  assert (model'.model_record.record_read.R.epoch == R.Application);
                  // establishes the HsServerFinishedVerified read-material match clause.
                  assert (model'.model_handshake.hs_keys.ks_server_application_traffic ==
                          Some install.install_material);
                  assert (traffic_material_matches_record_direction
                            install.install_material model'.model_record.record_read)
                | TrafficApplication, TrafficWrite ->
                  assert (stage == HsServerFinishedVerified);
                  assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
                  assert (model'.model_handshake.hs_keys.ks_server_application_traffic ==
                          model.model_handshake.hs_keys.ks_server_application_traffic);
                  assert (model'.model_record.record_read ==
                          model.model_record.record_read);
                  assert (client_application_record_read_epoch_link model);
                  assert (client_application_record_read_epoch_link model');
                  // the read-material clause is preserved: neither ks_server_application_traffic
                  // nor record_read is touched by installing the client write key.
                  (match model.model_handshake.hs_keys.ks_server_application_traffic with
                   | Some rm ->
                     assert (traffic_material_matches_record_direction rm model'.model_record.record_read)
                   | None -> ()))
             | _ ->
               assert False)
          | LocalInstallTrafficKeysForRole role_install ->
            (match model.model_control with
             | ControlHandshaking stage ->
               assert (role_install.install_role == ClientEndpoint);
               let install = role_install.install_payload in
               assert (traffic_install_allowed_at_stage_for_role
                 ClientEndpoint stage install);
               (match install.install_epoch, install.install_direction with
                | TrafficHandshake, _ ->
                  assert (stage == HsServerHelloReceived);
                  assert (model.model_handshake.hs_keys.ks_server_application_traffic == None);
                  assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None)
                | TrafficApplication, TrafficRead ->
                  assert (stage == HsServerFinishedVerified);
                  assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
                  assert (model'.model_record.record_read.R.epoch == R.Application);
                  // establishes the HsServerFinishedVerified read-material match clause.
                  assert (model'.model_handshake.hs_keys.ks_server_application_traffic ==
                          Some install.install_material);
                  assert (traffic_material_matches_record_direction
                            install.install_material model'.model_record.record_read)
                | TrafficApplication, TrafficWrite ->
                  assert (stage == HsServerFinishedVerified);
                  assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
                  assert (model'.model_handshake.hs_keys.ks_server_application_traffic ==
                          model.model_handshake.hs_keys.ks_server_application_traffic);
                  assert (model'.model_record.record_read ==
                          model.model_record.record_read);
                  assert (client_application_record_read_epoch_link model);
                  assert (client_application_record_read_epoch_link model');
                  // the read-material clause is preserved: neither ks_server_application_traffic
                  // nor record_read is touched by installing the client write key.
                  (match model.model_handshake.hs_keys.ks_server_application_traffic with
                   | Some rm ->
                     assert (traffic_material_matches_record_direction rm model'.model_record.record_read)
                   | None -> ()))
             | _ ->
               assert False)
          | LocalValidateCertificate _ ->
            (match model.model_control with
             | ControlHandshaking HsCertificateReceived ->
               assert (model.model_handshake.hs_keys.ks_server_application_traffic == None);
               assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None)
             | _ ->
               assert False)
          | LocalVerifyCertificateSignature _ ->
            (match model.model_control with
             | ControlHandshaking HsCertificateVerifyReceived ->
               assert (model.model_handshake.hs_keys.ks_server_application_traffic == None);
               assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None)
             | _ ->
               assert False)
          | LocalVerifyFinished _ ->
            (match model.model_control with
             | ControlHandshaking HsServerFinishedReceived ->
               assert (model.model_handshake.hs_keys.ks_server_application_traffic == None);
               assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None)
             | _ ->
               assert False)
          | LocalDeliverApplicationData _ ->
            (match model.model_control with
             | ControlApplicationData ->
               assert (client_application_record_epoch_link model);
               assert (model'.model_handshake.hs_keys == model.model_handshake.hs_keys);
               assert (model'.model_record == model.model_record);
               assert (client_application_record_epoch_link model')
             | _ ->
               assert False)
          | LocalFail _ ->
            ()
          | _ ->
            assert False)
       | ConnNetworkEvent msg ->
         assert (legal_tls_message
           model
           msg.CL.message_direction
           msg.CL.message_value);
         assert (step_tls_message
           model
           msg.CL.message_direction
           msg.CL.message_value == Some model');
         (match msg.CL.message_value, msg.CL.message_direction, model.model_control with
          | M.TlsHandshake (M.ClientHello _), CL.Sent,
            ControlHandshaking HsStarted
          | M.TlsHandshake (M.ServerHello _), CL.Received,
            ControlHandshaking HsClientHelloSent
          | M.TlsHandshake (M.EncryptedExtensions _), CL.Received,
            ControlHandshaking HsServerHelloReceived
          | M.TlsHandshake (M.Certificate _), CL.Received,
            ControlHandshaking HsEncryptedExtensionsReceived
          | M.TlsHandshake (M.CertificateVerify _), CL.Received,
            ControlHandshaking HsCertificateValidated ->
            assert (model.model_handshake.hs_keys.ks_server_application_traffic == None);
            assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None)
          | M.TlsHandshake (M.Finished _), CL.Received,
            ControlHandshaking HsCertificateVerifyVerified ->
            // Model-Fix-1: atomic delivery installs the server's application READ keys
            // (record_read epoch -> Application) and populates ks_server_application_traffic,
            // landing directly at HsServerFinishedVerified; prove the read-epoch link.
            assert (model'.model_record.record_read.R.epoch == R.Application);
            assert (client_application_record_read_epoch_link model');
            // establishes the HsServerFinishedVerified read-material match clause:
            // record_read is installed from the freshly derived server application
            // read material, which is also stored into ks_server_application_traffic.
            (match model'.model_handshake.hs_keys.ks_server_application_traffic with
             | Some rm ->
               assert (traffic_material_matches_record_direction rm model'.model_record.record_read)
             | None -> ())
          | M.TlsHandshake (M.Finished _), CL.Sent,
            ControlHandshaking HsServerFinishedVerified ->
            assert (Some? model.model_handshake.hs_keys.ks_server_application_traffic);
            assert (Some? model.model_handshake.hs_keys.ks_client_application_traffic);
            assert (client_application_record_read_epoch_link model);
            assert (model.model_record.record_read.R.epoch == R.Application);
            assert (model'.model_record.record_read.R.epoch == R.Application);
            assert (model'.model_record.record_write.R.epoch == R.Application);
            assert (client_application_record_epoch_link model');
            // keys-installed at ControlApplicationData: the client READ material
            // (server application traffic) is carried unchanged from the
            // HsServerFinishedVerified shape, and the client WRITE material (client
            // application traffic) is installed into record_write here by
            // install_client_application_write_after_finished.
            assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
            assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
            assert (model'.model_record.record_read == model.model_record.record_read);
            (match model.model_handshake.hs_keys.ks_server_application_traffic with
             | Some rm ->
               assert (traffic_material_matches_record_direction rm model.model_record.record_read);
               assert (traffic_material_matches_record_direction rm model'.model_record.record_read));
            (match model.model_handshake.hs_keys.ks_client_application_traffic with
             | Some wm ->
               assert (traffic_material_matches_record_direction wm model'.model_record.record_write));
            assert (application_record_keys_installed_for_role ClientEndpoint model')
          | M.TlsHandshake M.HelloRetryRequest, CL.Received,
            ControlHandshaking HsClientHelloSent ->
            ()
          | M.TlsApplicationData bytes, CL.Sent, ControlApplicationData ->
            assert (client_application_record_epoch_link model);
            lemma_advance_direction_records_preserves_epoch
              model.model_record.record_write
              (S.application_data_record_count bytes);
            lemma_advance_direction_records_preserves_key_iv
              model.model_record.record_write
              (S.application_data_record_count bytes);
            assert (client_application_record_epoch_link model');
            assert (application_record_keys_installed_for_role ClientEndpoint model')
          | M.TlsApplicationData _, CL.Received, ControlApplicationData
          | M.TlsIgnoredPostHandshake _, CL.Received, ControlApplicationData ->
            assert (client_application_record_epoch_link model);
            assert (client_application_record_epoch_link model');
            assert (application_record_keys_installed_for_role ClientEndpoint model')
          | M.TlsKeyUpdate _, CL.Received, ControlApplicationData ->
            assert (client_application_record_epoch_link model);
            assert (model'.model_record.record_read.R.epoch == R.Application);
            assert (model'.model_record.record_write ==
                    model.model_record.record_write);
            assert (client_application_record_epoch_link model');
            assert (application_record_keys_installed_for_role ClientEndpoint model')
          | M.TlsKeyUpdate _, CL.Sent,
            ControlApplicationData ->
            assert (client_application_record_epoch_link model);
            assert (model'.model_record.record_read ==
                    model.model_record.record_read);
            assert (model'.model_record.record_write.R.epoch == R.Application);
            assert (client_application_record_epoch_link model');
            assert (application_record_keys_installed_for_role ClientEndpoint model')
          | M.TlsAlert T.Close_notify, CL.Sent, ControlApplicationData ->
            assert (client_application_record_epoch_link model);
            assert (model'.model_record.record_read ==
                    model.model_record.record_read);
            assert (model'.model_record.record_write.R.epoch ==
                    (R.next_seq model.model_record.record_write).R.epoch);
            assert (client_application_record_epoch_link model');
            // strengthened Closing arm: keys-installed carried from the CAD
            // pre-state; record_read unchanged, record_write only bumps seq
            // (next_seq preserves key/iv), so both direction materials still match.
            assert (application_record_keys_installed_for_role ClientEndpoint model);
            assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
            assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
            (match model.model_handshake.hs_keys.ks_server_application_traffic with
             | Some rm ->
               assert (traffic_material_matches_record_direction rm model'.model_record.record_read));
            (match model.model_handshake.hs_keys.ks_client_application_traffic with
             | Some wm ->
               assert (traffic_material_matches_record_direction wm model.model_record.record_write);
               assert (traffic_material_matches_record_direction wm model'.model_record.record_write));
            assert (application_record_keys_installed_for_role ClientEndpoint model')
          | M.TlsAlert T.Close_notify, CL.Received, ControlApplicationData
          | M.TlsAlert T.Close_notify, CL.Received, ControlClosing ->
            assert (client_application_record_epoch_link model);
            assert (model'.model_record.record_write ==
                    model.model_record.record_write);
            assert (model'.model_record.record_read.R.epoch ==
                    (R.next_seq model.model_record.record_read).R.epoch);
            assert (client_application_record_epoch_link model');
            // strengthened Closed arm: keys-installed carried from the pre-state
            // (CAD arm, or the strengthened Closing arm); record_write unchanged,
            // record_read only bumps seq (next_seq preserves key/iv).
            assert (application_record_keys_installed_for_role ClientEndpoint model);
            assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
            assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
            (match model.model_handshake.hs_keys.ks_server_application_traffic with
             | Some rm ->
               assert (traffic_material_matches_record_direction rm model.model_record.record_read);
               assert (traffic_material_matches_record_direction rm model'.model_record.record_read));
            (match model.model_handshake.hs_keys.ks_client_application_traffic with
             | Some wm ->
               assert (traffic_material_matches_record_direction wm model'.model_record.record_write));
            assert (application_record_keys_installed_for_role ClientEndpoint model')
          | M.TlsAlert _, _, _ ->
            ()
          | M.TlsChangeCipherSpec, _, ControlHandshaking _ ->
            assert (model' == model)
          | _, _, _ ->
            assert False)
      | ConnProtectedHandshake step ->
        assert (legal_protected_handshake_step model step);
        assert (step_protected_handshake model step == Some model');
        if step.protected_handshake_buffering
        then begin
          (* Buffering keeps the control state and key schedule fixed and
             only bumps the read sequence, which [next_seq] does without
             changing the epoch or its material. *)
          assert (model'.model_control == model.model_control);
          assert (model'.model_handshake.hs_keys == model.model_handshake.hs_keys);
          assert (model'.model_record.record_write == model.model_record.record_write);
          assert (model'.model_record.record_read.R.epoch ==
                  (R.next_seq model.model_record.record_read).R.epoch)
        end
        else
        (match step.protected_handshake_message, model.model_control with
         | M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived
         | M.Certificate _, ControlHandshaking HsEncryptedExtensionsReceived
         | M.CertificateVerify _, ControlHandshaking HsCertificateValidated ->
           assert (model.model_handshake.hs_keys.ks_server_application_traffic == None);
           assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None)
         | M.Finished _, ControlHandshaking HsCertificateVerifyVerified ->
           assert (model'.model_record.record_read.R.epoch == R.Application);
           assert (client_application_record_read_epoch_link model')
         | _, _ ->
           assert False));
      assert (client_application_record_epoch_reachable_shape model')
    end;
    assert (model_application_record_epoch_reachable_shape_for_role
      ClientEndpoint
      model')
  | ServerEndpoint ->
    if model'.model_config.config_role == ServerEndpoint then begin
      assert (model.model_config.config_role == ServerEndpoint);
      assert (server_application_record_epoch_reachable_shape model);
      (match ev with
       | ConnLocalEvent local ->
         assert (legal_local_event model local);
         assert (step_local_event model local == Some model');
         (match local with
          | LocalStartServer ->
            (match model.model_control with
             | ControlNew ->
               assert (no_application_traffic_keys model.model_handshake.hs_keys);
               assert (no_application_traffic_keys model'.model_handshake.hs_keys);
               assert (model'.model_record.record_write.R.epoch =!= R.Application)
             | _ ->
               assert False)
          | LocalSelectServerParameters _ ->
            (match model.model_control with
             | ControlHandshaking HsClientHelloReceived ->
               assert (no_application_traffic_keys model.model_handshake.hs_keys);
               assert (no_application_traffic_keys model'.model_handshake.hs_keys);
               assert (model'.model_record.record_write.R.epoch =!= R.Application)
             | _ ->
               assert False)
          | LocalDeriveSharedSecret _ ->
            (match model.model_control with
             | ControlHandshaking HsClientHelloReceived ->
               assert (no_application_traffic_keys model.model_handshake.hs_keys);
               assert (no_application_traffic_keys model'.model_handshake.hs_keys);
               assert (model'.model_record.record_write.R.epoch =!= R.Application)
             | _ ->
               assert False)
          | LocalInstallTrafficKeysForRole role_install ->
            (match model.model_control with
             | ControlHandshaking stage ->
               assert (role_install.install_role == ServerEndpoint);
               let install = role_install.install_payload in
               assert (traffic_install_allowed_at_stage_for_role
                 ServerEndpoint stage install);
               (match install.install_epoch, install.install_direction with
                | TrafficHandshake, _ ->
                  assert (stage == HsServerHelloSent);
                  assert (no_application_traffic_keys model.model_handshake.hs_keys);
                  assert (no_application_traffic_keys model'.model_handshake.hs_keys);
                  // handshake write-key install lands record_write at the Handshake
                  // epoch, never Application.
                  assert (model'.model_record.record_write.R.epoch =!= R.Application)
                | TrafficApplication, TrafficWrite ->
                  assert (stage == HsServerFinishedSent);
                  assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
                  assert (model'.model_handshake.hs_keys.ks_client_application_traffic ==
                          model.model_handshake.hs_keys.ks_client_application_traffic);
                  assert (model.model_handshake.hs_keys.ks_client_application_traffic == None);
                  assert (model'.model_handshake.hs_keys.ks_client_application_traffic == None);
                  assert (model'.model_record.record_write.R.epoch == R.Application);
                  assert (server_application_record_write_epoch_link model');
                  // establishes the HsServerFinishedSent write-material match clause:
                  // the server application write material is installed into record_write.
                  assert (model'.model_handshake.hs_keys.ks_server_application_traffic ==
                          Some install.install_material);
                  assert (traffic_material_matches_record_direction
                            install.install_material
                            model'.model_record.record_write)
                | TrafficApplication, TrafficRead ->
                  assert (stage == HsClientFinishedReceived);
                  assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
                  assert (model'.model_record.record_read.R.epoch == R.Application);
                  assert (model'.model_handshake.hs_keys.ks_server_application_traffic ==
                          model.model_handshake.hs_keys.ks_server_application_traffic);
                  assert (model'.model_record.record_write ==
                          model.model_record.record_write);
                  assert (server_application_record_write_epoch_link model);
                  assert (server_application_record_epoch_link model'))
             | _ ->
               assert False)
          | LocalSignCertificateVerify _ ->
            (match model.model_control with
             | ControlHandshaking HsServerEncryptedFlightSent ->
               assert (no_application_traffic_keys model.model_handshake.hs_keys);
               assert (no_application_traffic_keys model'.model_handshake.hs_keys);
               assert (model'.model_record.record_write.R.epoch =!= R.Application)
             | _ ->
               assert False)
          | LocalVerifyClientFinished _ ->
            (match model.model_control with
             | ControlHandshaking HsClientFinishedReceived ->
               assert (application_record_keys_installed_for_role
                 ServerEndpoint model);
               assert (Some? model.model_handshake.hs_keys.ks_client_application_traffic);
               assert (Some? model.model_handshake.hs_keys.ks_server_application_traffic);
               assert (server_application_record_epoch_link model);
               assert (model'.model_record == model.model_record);
               assert (model'.model_handshake.hs_keys == model.model_handshake.hs_keys);
               assert (server_application_record_epoch_link model')
             | _ ->
               assert False)
          | LocalDeliverApplicationData _ ->
            (match model.model_control with
             | ControlApplicationData ->
               assert (server_application_record_epoch_link model);
               assert (model'.model_handshake.hs_keys == model.model_handshake.hs_keys);
               assert (model'.model_record == model.model_record);
               assert (server_application_record_epoch_link model')
             | _ ->
               assert False)
          | LocalFail _ ->
            ()
          | LocalInstallTrafficKeys _ ->
            assert False
          | _ ->
            assert False)
       | ConnNetworkEvent msg ->
         assert (legal_tls_message
           model
           msg.CL.message_direction
           msg.CL.message_value);
         assert (step_tls_message
           model
           msg.CL.message_direction
           msg.CL.message_value == Some model');
         (match msg.CL.message_value, msg.CL.message_direction, model.model_control with
          | M.TlsHandshake (M.ClientHello _), CL.Received,
            ControlHandshaking HsAwaitingClientHello
          | M.TlsHandshake (M.ServerHello _), CL.Sent,
            ControlHandshaking HsClientHelloReceived
          | M.TlsHandshake (M.EncryptedExtensions _), CL.Sent,
            ControlHandshaking HsServerHelloSent
          | M.TlsHandshake (M.Certificate _), CL.Sent,
            ControlHandshaking HsServerEncryptedFlightSent
          | M.TlsHandshake (M.CertificateVerify _), CL.Sent,
            ControlHandshaking HsServerEncryptedFlightSent ->
            assert (no_application_traffic_keys model.model_handshake.hs_keys);
            assert (no_application_traffic_keys model'.model_handshake.hs_keys);
            // These arms either leave record_write untouched (received ClientHello)
            // or advance it by `next_seq` (server handshake sends), both of which
            // PRESERVE the write epoch; the strengthened pre-shape gives it off
            // Application, so it stays off Application.
            assert (model'.model_record.record_write.R.epoch =!= R.Application)
          | M.TlsHandshake (M.Finished _), CL.Sent,
            ControlHandshaking HsServerEncryptedFlightSent ->
            assert (no_application_traffic_keys model.model_handshake.hs_keys);
            assert (model'.model_handshake.hs_keys.ks_client_application_traffic == None);
            assert (model'.model_handshake.hs_keys.ks_server_application_traffic == None);
            assert (server_application_record_write_epoch_link model')
          | M.TlsHandshake (M.Finished _), CL.Received,
            ControlHandshaking HsServerFinishedSent ->
            // Model-Fix-1: atomic delivery installs the client's application READ keys
            // (record_read epoch -> Application) and populates ks_client_application_traffic,
            // landing directly at ControlApplicationData; record_write and
            // ks_server_application_traffic are unchanged.
            assert (server_application_record_write_epoch_link model);
            assert (model'.model_record.record_write ==
                    model.model_record.record_write);
            assert (model'.model_handshake.hs_keys.ks_server_application_traffic ==
                    model.model_handshake.hs_keys.ks_server_application_traffic);
            assert (model'.model_record.record_read.R.epoch == R.Application);
            assert (server_application_record_read_epoch_link model');
            assert (server_application_record_write_epoch_link model');
            assert (server_application_record_epoch_link model');
            // keys-installed at ControlApplicationData: the server READ material
            // (client application traffic) is installed into record_read here; the server
            // WRITE material (server application traffic) is carried unchanged from the
            // HsServerFinishedSent shape and is forced present by the strengthened
            // CF-receive legality (Some? ks_server_application_traffic).
            assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
            assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
            assert (Some? model.model_handshake.hs_keys.ks_server_application_traffic);
            (match model'.model_handshake.hs_keys.ks_client_application_traffic with
             | Some rm ->
               assert (traffic_material_matches_record_direction rm model'.model_record.record_read));
            (match model.model_handshake.hs_keys.ks_server_application_traffic with
             | Some wm ->
               assert (traffic_material_matches_record_direction wm model.model_record.record_write);
               assert (traffic_material_matches_record_direction wm model'.model_record.record_write));
            assert (application_record_keys_installed_for_role ServerEndpoint model')
          | M.TlsApplicationData bytes, CL.Sent, ControlApplicationData ->
            assert (server_application_record_epoch_link model);
            lemma_advance_direction_records_preserves_epoch
              model.model_record.record_write
              (S.application_data_record_count bytes);
            lemma_advance_direction_records_preserves_key_iv
              model.model_record.record_write
              (S.application_data_record_count bytes);
            assert (server_application_record_epoch_link model');
            assert (application_record_keys_installed_for_role ServerEndpoint model')
          | M.TlsApplicationData _, CL.Received, ControlApplicationData ->
            assert (server_application_record_epoch_link model);
            assert (model'.model_record.record_write ==
                    model.model_record.record_write);
            assert (model'.model_record.record_read.R.epoch ==
                    (R.next_seq model.model_record.record_read).R.epoch);
            assert (server_application_record_epoch_link model');
            assert (application_record_keys_installed_for_role ServerEndpoint model')
          | M.TlsKeyUpdate _, CL.Received, ControlApplicationData ->
            (* Server-side receive rotates the *client* application traffic
               slot and reinstalls the read keys at the Application epoch. *)
            assert (server_application_record_epoch_link model);
            assert (model'.model_record.record_read.R.epoch == R.Application);
            assert (model'.model_record.record_write ==
                    model.model_record.record_write);
            assert (server_application_record_epoch_link model');
            assert (application_record_keys_installed_for_role ServerEndpoint model')
          | M.TlsKeyUpdate _, CL.Sent, ControlApplicationData ->
            (* Server-side send rotates the *server* application traffic slot
               and reinstalls the write keys at the Application epoch. *)
            assert (server_application_record_epoch_link model);
            assert (model'.model_record.record_read ==
                    model.model_record.record_read);
            assert (model'.model_record.record_write.R.epoch == R.Application);
            assert (server_application_record_epoch_link model');
            assert (application_record_keys_installed_for_role ServerEndpoint model')
          | M.TlsAlert T.Close_notify, CL.Sent, ControlApplicationData ->
            assert (server_application_record_epoch_link model);
            assert (model'.model_record.record_read ==
                    model.model_record.record_read);
            assert (model'.model_record.record_write.R.epoch ==
                    (R.next_seq model.model_record.record_write).R.epoch);
            assert (server_application_record_epoch_link model');
            // strengthened Closing arm (server mirror): keys-installed carried
            // from the CAD pre-state; record_read unchanged, record_write only
            // bumps seq (next_seq preserves key/iv).
            assert (application_record_keys_installed_for_role ServerEndpoint model);
            assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
            assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
            (match model.model_handshake.hs_keys.ks_client_application_traffic with
             | Some rm ->
               assert (traffic_material_matches_record_direction rm model'.model_record.record_read));
            (match model.model_handshake.hs_keys.ks_server_application_traffic with
             | Some wm ->
               assert (traffic_material_matches_record_direction wm model.model_record.record_write);
               assert (traffic_material_matches_record_direction wm model'.model_record.record_write));
            assert (application_record_keys_installed_for_role ServerEndpoint model')
          | M.TlsAlert T.Close_notify, CL.Received, ControlApplicationData
          | M.TlsAlert T.Close_notify, CL.Received, ControlClosing ->
            assert (server_application_record_epoch_link model);
            assert (model'.model_record.record_write ==
                    model.model_record.record_write);
            assert (model'.model_record.record_read.R.epoch ==
                    (R.next_seq model.model_record.record_read).R.epoch);
            assert (server_application_record_epoch_link model');
            // strengthened Closed arm (server mirror): keys-installed carried from
            // the pre-state (CAD arm, or the strengthened Closing arm); record_write
            // unchanged, record_read only bumps seq (next_seq preserves key/iv).
            assert (application_record_keys_installed_for_role ServerEndpoint model);
            assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
            assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
            (match model.model_handshake.hs_keys.ks_client_application_traffic with
             | Some rm ->
               assert (traffic_material_matches_record_direction rm model.model_record.record_read);
               assert (traffic_material_matches_record_direction rm model'.model_record.record_read));
            (match model.model_handshake.hs_keys.ks_server_application_traffic with
             | Some wm ->
               assert (traffic_material_matches_record_direction wm model'.model_record.record_write));
            assert (application_record_keys_installed_for_role ServerEndpoint model')
          | M.TlsAlert _, _, _ ->
            ()
          | M.TlsChangeCipherSpec, _, ControlHandshaking _ ->
            assert (model' == model)
          | _, _, _ ->
            assert False)
       | ConnProtectedHandshake step ->
         assert False);
      assert (server_application_record_epoch_reachable_shape model')
    end;
    assert (model_application_record_epoch_reachable_shape_for_role
      ServerEndpoint
      model')

#pop-options
let lemma_connection_delta_application_record_epoch_reachable_shape_for_role
  (role:endpoint_role)
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        connection_application_record_epoch_reachable_shape_for_role role st0 /\
        connection_state_single_step st0 st1)
      (ensures
        connection_application_record_epoch_reachable_shape_for_role role st1)
=
  match st1 with
  | _ ->
    assert (exists delta. legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        connection_delta
        (fun delta -> legal_connection_delta st0 delta st1) in
    let delta : connection_delta = delta_w in
    assert (legal_connection_delta st0 delta st1);
    assert (legal_event st0.cs_model delta.delta_event);
    assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
    lemma_step_model_application_record_epoch_reachable_shape_for_role
      role
      st0.cs_model
      delta.delta_event
      st1.cs_model

let lemma_connection_state_single_step_application_record_epoch_reachable_shape_for_role
  (role:endpoint_role)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (connection_application_record_epoch_reachable_shape_for_role role y);
            (connection_state_single_step x y)}
          connection_application_record_epoch_reachable_shape_for_role role x /\
          connection_state_single_step x y ==>
          connection_application_record_epoch_reachable_shape_for_role role y)
=
  introduce forall x y.
    connection_application_record_epoch_reachable_shape_for_role role x /\
    connection_state_single_step x y ==>
    connection_application_record_epoch_reachable_shape_for_role role y
  with
    introduce _ ==> _ with
    lemma_connection_delta_application_record_epoch_reachable_shape_for_role
      role
      x
      y

let lemma_connection_application_ready_record_epochs_installed
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == role /\
        st.cs_model.model_control == ControlApplicationData /\
        application_record_keys_installed_for_role role st.cs_model)
      (ensures application_record_epochs_installed_for_role role st.cs_model)
=
  let p = connection_application_record_epoch_reachable_shape_for_role role in
  lemma_initial_application_record_epoch_reachable_shape_for_role
    role
    st.cs_model.model_config;
  lemma_connection_state_single_step_application_record_epoch_reachable_shape_for_role
    role;
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st);
  match role with
  | ClientEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_server_application_traffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_client_application_traffic);
    assert (client_application_record_epoch_reachable_shape st.cs_model);
    assert (client_application_record_epoch_link st.cs_model);
    assert (st.cs_model.model_record.record_read.R.epoch == R.Application);
    assert (st.cs_model.model_record.record_write.R.epoch == R.Application)
  | ServerEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_client_application_traffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_server_application_traffic);
    assert (server_application_record_epoch_reachable_shape st.cs_model);
    assert (server_application_record_epoch_link st.cs_model);
    assert (st.cs_model.model_record.record_read.R.epoch == R.Application);
    assert (st.cs_model.model_record.record_write.R.epoch == R.Application)

(** Sub-goal (a) BRIDGE: at any reachable (consistent) endpoint sitting at
    `ControlApplicationData`, the strengthened application-record-epoch reachable
    shape yields the full both-direction key installation for the endpoint's own
    role.  This is the missing ingredient over `client_e2e`/`server_e2e` needed to
    conclude `client_driver_application_ready`/`server_driver_application_ready`.
    The shape itself is established here purely from reachability (RTC closure over
    single steps from the initial state), so NO new `tls_system_inv` conjunct is
    required — the existing `connection_state_consistent` conjunct suffices. **)
let lemma_connection_appdata_keys_installed_for_role
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == role /\
        st.cs_model.model_control == ControlApplicationData)
      (ensures application_record_keys_installed_for_role role st.cs_model)
=
  let p = connection_application_record_epoch_reachable_shape_for_role role in
  lemma_initial_application_record_epoch_reachable_shape_for_role
    role
    st.cs_model.model_config;
  lemma_connection_state_single_step_application_record_epoch_reachable_shape_for_role
    role;
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st);
  match role with
  | ClientEndpoint ->
    assert (client_application_record_epoch_reachable_shape st.cs_model)
  | ServerEndpoint ->
    assert (server_application_record_epoch_reachable_shape st.cs_model)

(** Graceful-close analogue of [lemma_connection_application_ready_record_epochs_installed].
    At any reachable (consistent) endpoint sitting at `ControlClosing` or
    `ControlClosed`, BOTH record directions are at the `Application` epoch.  The
    strengthened Closing/Closed reachable-shape arm carries the both-direction key
    installation (inherited from the CAD pre-state through Close_notify's seq-only
    `next_seq` bump), and the epoch link then pins both epochs to `Application`.
    This is what excludes the graceful-close controls from a `Handshake?`-epoch
    guard: a consistent endpoint at a Handshake read/write epoch is necessarily
    NOT in `{Closing, Closed}` (nor `ControlApplicationData`).  Established purely
    from reachability, so NO new `tls_system_inv` conjunct is required. **)
let lemma_connection_closing_closed_record_epochs_installed
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == role /\
        (ControlClosing? st.cs_model.model_control \/
         ControlClosed? st.cs_model.model_control))
      (ensures application_record_epochs_installed_for_role role st.cs_model)
=
  let p = connection_application_record_epoch_reachable_shape_for_role role in
  lemma_initial_application_record_epoch_reachable_shape_for_role
    role
    st.cs_model.model_config;
  lemma_connection_state_single_step_application_record_epoch_reachable_shape_for_role
    role;
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st);
  match role with
  | ClientEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
    assert (client_application_record_epoch_reachable_shape st.cs_model);
    assert (application_record_keys_installed_for_role ClientEndpoint st.cs_model);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_server_application_traffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_client_application_traffic);
    assert (client_application_record_epoch_link st.cs_model);
    assert (st.cs_model.model_record.record_read.R.epoch == R.Application);
    assert (st.cs_model.model_record.record_write.R.epoch == R.Application)
  | ServerEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
    assert (server_application_record_epoch_reachable_shape st.cs_model);
    assert (application_record_keys_installed_for_role ServerEndpoint st.cs_model);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_client_application_traffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_server_application_traffic);
    assert (server_application_record_epoch_link st.cs_model);
    assert (st.cs_model.model_record.record_read.R.epoch == R.Application);
    assert (st.cs_model.model_record.record_write.R.epoch == R.Application)


(** Model-Fix-1 corollary: a reachable SERVER endpoint at `HsServerFinishedSent`
    has NOT yet installed the client application (read) traffic secret — that
    install is legal only at `HsClientFinishedReceived` (or is performed atomically
    by the recv-Finished step that lands `ControlApplicationData`), both strictly
    after `HsServerFinishedSent`.  Extracted from the (reachable) server
    application-record-epoch shape, whose `HsServerFinishedSent` arm records exactly
    `ks_client_application_traffic == None`.  Used by the System-level FACT-4
    wire-receive establishment to pin the server pre-verify progress at 13. **)
let lemma_server_finished_sent_no_client_application_traffic
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlHandshaking HsServerFinishedSent)
      (ensures
        st.cs_model.model_handshake.hs_keys.ks_client_application_traffic == None)
=
  let p = connection_application_record_epoch_reachable_shape_for_role ServerEndpoint in
  lemma_initial_application_record_epoch_reachable_shape_for_role
    ServerEndpoint
    st.cs_model.model_config;
  lemma_connection_state_single_step_application_record_epoch_reachable_shape_for_role
    ServerEndpoint;
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st);
  assert (server_application_record_epoch_reachable_shape st.cs_model)

(** STAGE (b): a reachable CLIENT endpoint at `HsServerFinishedVerified` has not
    yet installed its application WRITE key — record_write is still at the
    Handshake epoch.  The client's application write key is installed only by the
    Finished send (`install_client_application_write_after_finished`), which moves
    control to `ControlApplicationData`; the legal local (TrafficApplication,
    TrafficWrite) install is a no-op on record_write for a client
    (`install_record_keys`, StateMachine.fst:399).  Hence app_wseq is 0 at the
    Finished send, which is what makes the application record-seq pairing hold
    across that step. **)
let lemma_client_finished_verified_write_epoch_not_application
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        st.cs_model.model_control == ControlHandshaking HsServerFinishedVerified)
      (ensures
        st.cs_model.model_record.record_write.R.epoch =!= R.Application)
=
  let p = connection_application_record_epoch_reachable_shape_for_role ClientEndpoint in
  lemma_initial_application_record_epoch_reachable_shape_for_role
    ClientEndpoint
    st.cs_model.model_config;
  lemma_connection_state_single_step_application_record_epoch_reachable_shape_for_role
    ClientEndpoint;
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st);
  assert (client_application_record_epoch_reachable_shape st.cs_model)

(** STAGE (b), message-keyed form: whenever a reachable CLIENT endpoint legally
    *sends* a handshake message, its record_write is still at the Handshake epoch
    (not Application).  This packages the two client Sent-handshake sites uniformly:
    by `legal_handshake_message` (StateMachine.fst:1300) the only `CL.Sent` arms
    with `config_role == ClientEndpoint` are `ClientHello @ HsStarted` and
    `Finished @ HsServerFinishedVerified` — every other Sent arm requires
    `ServerEndpoint` or falls through to `False`.  Both of those stages sit in the
    strengthened `client_application_record_epoch_reachable_shape`, which pins
    record_write off the Application epoch throughout the client handshake.  This
    is the guard the application record-seq delta lemma needs at a client send. **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_client_handshake_send_write_epoch_not_application
  (st st':connection_state)
  (hm:M.handshake_msg)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        legal_tls_message st.cs_model CL.Sent (M.TlsHandshake hm) /\
        step_tls_message st.cs_model CL.Sent (M.TlsHandshake hm) == Some st'.cs_model)
      (ensures
        st.cs_model.model_record.record_write.R.epoch =!= R.Application)
=
  let p = connection_application_record_epoch_reachable_shape_for_role ClientEndpoint in
  lemma_initial_application_record_epoch_reachable_shape_for_role
    ClientEndpoint
    st.cs_model.model_config;
  lemma_connection_state_single_step_application_record_epoch_reachable_shape_for_role
    ClientEndpoint;
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st);
  assert (client_application_record_epoch_reachable_shape st.cs_model);
  // Client handshaking stages: the strengthened shape gives record_write off the
  // Application epoch directly.  Everything else is unreachable for a legal client
  // Sent handshake (legal_handshake_message has no ClientEndpoint Sent arm there).
  match st.cs_model.model_control with
  | ControlHandshaking HsStarted
  | ControlHandshaking HsClientHelloSent
  | ControlHandshaking HsServerHelloReceived
  | ControlHandshaking HsEncryptedExtensionsReceived
  | ControlHandshaking HsCertificateReceived
  | ControlHandshaking HsCertificateValidated
  | ControlHandshaking HsCertificateVerifyReceived
  | ControlHandshaking HsCertificateVerifyVerified
  | ControlHandshaking HsServerFinishedReceived
  | ControlHandshaking HsServerFinishedVerified -> ()
  | _ ->
    assert False
#pop-options

(** STAGE (b), server mirror of the message-keyed extraction: any legal SERVER
    *send* of a handshake message happens with record_write off the Application
    epoch.  The only server Sent-handshake sites are ServerHello @
    HsClientHelloReceived, EncryptedExtensions @ HsServerHelloSent, and
    Certificate/CertificateVerify/Finished @ HsServerEncryptedFlightSent — all in
    the strengthened grouped arm of `server_application_record_epoch_reachable_shape`,
    which pins record_write off Application throughout the server's sending
    stages (the server app write key installs only later, at HsServerFinishedSent). **)
#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_server_handshake_send_write_epoch_not_application
  (st st':connection_state)
  (hm:M.handshake_msg)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        legal_tls_message st.cs_model CL.Sent (M.TlsHandshake hm) /\
        step_tls_message st.cs_model CL.Sent (M.TlsHandshake hm) == Some st'.cs_model)
      (ensures
        st.cs_model.model_record.record_write.R.epoch =!= R.Application)
=
  let p = connection_application_record_epoch_reachable_shape_for_role ServerEndpoint in
  lemma_initial_application_record_epoch_reachable_shape_for_role
    ServerEndpoint
    st.cs_model.model_config;
  lemma_connection_state_single_step_application_record_epoch_reachable_shape_for_role
    ServerEndpoint;
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st);
  assert (server_application_record_epoch_reachable_shape st.cs_model);
  match st.cs_model.model_control with
  | ControlNew
  | ControlHandshaking HsAwaitingClientHello
  | ControlHandshaking HsClientHelloReceived
  | ControlHandshaking HsServerHelloSent
  | ControlHandshaking HsServerEncryptedFlightSent -> ()
  | _ ->
    assert False
#pop-options

(** ─────────────────────────────────────────────────────────────────────────
    STAGE (b), READ side — the handshaking read-seq shape.

    During the handshake the epoch-collapsing READ projection is 0.  This is the
    read-side analogue of the write strengthening above and is what the LOCAL
    families need: the only local events that touch `record_read` are key
    installs, which `R.install_keys` resets to seq 0 (checked the EFFECT function,
    Record.Spec.fst:25) — so the post-install projection is 0, and this shape
    supplies that the PRE-install projection was 0 too, giving preservation.

    The shape is STRONG (`record_read.epoch =!= Application`) at every handshaking
    stage EXCEPT the two where the app-read key is already installed while control
    is still handshaking: the client's `HsServerFinishedVerified` (app-read key
    installed atomically on receiving the server Finished, StateMachine.fst:753)
    and the server's `HsClientFinishedReceived` (app-read installable by the
    role-keyed local install, legality StateMachine.fst:1181).  There the epoch may
    be `Application` but `record_read.seq` is still 0 — no application record can be
    received before `ControlApplicationData`, and every `R.next_seq`-on-read arm of
    `step_handshake_message` (StateMachine.fst:693/703/724) runs at read epoch
    `Handshake`, never `Application` (verified against the effect functions). **)
let handshaking_read_epoch_shape (model:connection_model) : prop =
  match model.model_control with
  | ControlHandshaking HsServerFinishedVerified
  | ControlHandshaking HsClientFinishedReceived ->
    model.model_record.record_read.R.epoch =!= R.Application \/
    model.model_record.record_read.R.seq == 0
  | ControlNew
  | ControlHandshaking _ ->
    model.model_record.record_read.R.epoch =!= R.Application
  | _ -> True

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_step_model_handshaking_read_epoch_shape
  (model:connection_model) (ev:conn_event) (model':connection_model)
  : Lemma
      (requires
        handshaking_read_epoch_shape model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures handshaking_read_epoch_shape model')
  = ()
#pop-options

let conn_handshaking_read_epoch_shape (st:connection_state) : prop =
  handshaking_read_epoch_shape st.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_handshaking_read_epoch_shape (st0 st1:connection_state)
  : Lemma
      (requires
        conn_handshaking_read_epoch_shape st0 /\ connection_state_single_step st0 st1)
      (ensures conn_handshaking_read_epoch_shape st1)
  = assert (exists delta. legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        connection_delta
        (fun delta -> legal_connection_delta st0 delta st1) in
    let delta : connection_delta = delta_w in
    assert (legal_connection_delta st0 delta st1);
    lemma_step_model_handshaking_read_epoch_shape
      st0.cs_model delta.delta_event st1.cs_model
#pop-options

let lemma_single_step_handshaking_read_epoch_shape (_:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern (conn_handshaking_read_epoch_shape y); (connection_state_single_step x y)}
          conn_handshaking_read_epoch_shape x /\ connection_state_single_step x y ==>
          conn_handshaking_read_epoch_shape y)
  = introduce forall x y.
      conn_handshaking_read_epoch_shape x /\ connection_state_single_step x y ==>
      conn_handshaking_read_epoch_shape y
    with introduce _ ==> _ with
      lemma_delta_handshaking_read_epoch_shape x y

let lemma_initial_handshaking_read_epoch_shape (cfg:connection_config)
  : Lemma (ensures conn_handshaking_read_epoch_shape (initial cfg))
  = ()

(** STAGE (b), READ side, consumed form: at any reachable handshaking state the
    epoch-collapsing read projection is 0 (`record_read` is off the Application
    epoch, or its seq is still 0).  This is the pre-state fact the LOCAL-family
    `app_seq_pairing` preservation needs to rule out an install RESETTING an
    already-advanced application read seq. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_handshaking_read_app_seq_zero (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        ControlHandshaking? st.cs_model.model_control)
      (ensures
        st.cs_model.model_record.record_read.R.epoch =!= R.Application \/
        st.cs_model.model_record.record_read.R.seq == 0)
  = lemma_initial_handshaking_read_epoch_shape st.cs_model.model_config;
    lemma_single_step_handshaking_read_epoch_shape ();
    let p = conn_handshaking_read_epoch_shape in
    let stable :
      squash (forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure connection_state_single_step p stable;
    assert (p (initial st.cs_model.model_config));
    assert (connection_state_evolves (initial st.cs_model.model_config) st);
    assert (p st)
#pop-options

(** STAGE (b), READ side, STRONG form: at any reachable handshaking state OTHER
    than client `HsServerFinishedVerified` / server `HsClientFinishedReceived`, the
    record read epoch is strictly off `Application`.  Same read-epoch reachable
    shape as `lemma_handshaking_read_app_seq_zero`, but reading its strong
    (non-`seq==0`) arm; used by the client delivery family to rule out a cleartext
    `ServerHello`/`HelloRetryRequest` receive (legal only at `HsClientHelloSent`)
    when the client's read epoch is `Application`.  See the `.fsti` for the full
    rationale. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_handshaking_nonfinal_read_not_application (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        ControlHandshaking? st.cs_model.model_control /\
        st.cs_model.model_control =!= ControlHandshaking HsServerFinishedVerified /\
        st.cs_model.model_control =!= ControlHandshaking HsClientFinishedReceived)
      (ensures
        st.cs_model.model_record.record_read.R.epoch =!= R.Application)
  = lemma_initial_handshaking_read_epoch_shape st.cs_model.model_config;
    lemma_single_step_handshaking_read_epoch_shape ();
    let p = conn_handshaking_read_epoch_shape in
    let stable :
      squash (forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure connection_state_single_step p stable;
    assert (p (initial st.cs_model.model_config));
    assert (connection_state_evolves (initial st.cs_model.model_config) st);
    assert (p st)
#pop-options

(** STAGE (b), WRITE side.  Mirror of `handshaking_read_epoch_shape` for the
    write projection.  The shape is STRONG (`record_write.epoch =!= Application`)
    at every handshaking stage EXCEPT the two where an app-write key can already be
    installed while control is still handshaking: the server's `HsServerFinishedSent`
    (app-write key installed by `LocalInstallServerApplicationTrafficKeys`) and its
    `HsClientFinishedReceived`.  There the epoch may be `Application` but
    `record_write.seq` is still 0 — no application record is written before
    `ControlApplicationData`, and every `R.next_seq`-on-write arm of
    `step_handshake_message` runs at write epoch `Handshake`, never `Application`
    (verified against the effect functions, not the legality predicates).  The
    client side is subsumed: a client's only legal app-write install is a no-op on
    `record_write` (`install_record_keys`'s `TrafficApplication, TrafficWrite`
    arm), so a client stays off the Application write epoch at every handshaking
    stage; the two weak-stage arms just do not fire for it. **)
let handshaking_write_epoch_shape (model:connection_model) : prop =
  match model.model_control with
  | ControlHandshaking HsServerFinishedSent
  | ControlHandshaking HsClientFinishedReceived ->
    model.model_record.record_write.R.epoch =!= R.Application \/
    model.model_record.record_write.R.seq == 0
  | ControlNew
  | ControlHandshaking _ ->
    model.model_record.record_write.R.epoch =!= R.Application
  | _ -> True

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_step_model_handshaking_write_epoch_shape
  (model:connection_model) (ev:conn_event) (model':connection_model)
  : Lemma
      (requires
        handshaking_write_epoch_shape model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures handshaking_write_epoch_shape model')
  = ()
#pop-options

let conn_handshaking_write_epoch_shape (st:connection_state) : prop =
  handshaking_write_epoch_shape st.cs_model

#push-options "--fuel 2 --ifuel 4 --z3rlimit 40"
let lemma_delta_handshaking_write_epoch_shape (st0 st1:connection_state)
  : Lemma
      (requires
        conn_handshaking_write_epoch_shape st0 /\ connection_state_single_step st0 st1)
      (ensures conn_handshaking_write_epoch_shape st1)
  = assert (exists delta. legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        connection_delta
        (fun delta -> legal_connection_delta st0 delta st1) in
    let delta : connection_delta = delta_w in
    assert (legal_connection_delta st0 delta st1);
    lemma_step_model_handshaking_write_epoch_shape
      st0.cs_model delta.delta_event st1.cs_model
#pop-options

let lemma_single_step_handshaking_write_epoch_shape (_:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern (conn_handshaking_write_epoch_shape y); (connection_state_single_step x y)}
          conn_handshaking_write_epoch_shape x /\ connection_state_single_step x y ==>
          conn_handshaking_write_epoch_shape y)
  = introduce forall x y.
      conn_handshaking_write_epoch_shape x /\ connection_state_single_step x y ==>
      conn_handshaking_write_epoch_shape y
    with introduce _ ==> _ with
      lemma_delta_handshaking_write_epoch_shape x y

let lemma_initial_handshaking_write_epoch_shape (cfg:connection_config)
  : Lemma (ensures conn_handshaking_write_epoch_shape (initial cfg))
  = ()

(** STAGE (b), WRITE side, consumed form: at any reachable handshaking state the
    epoch-collapsing write projection is 0.  This is the pre-state fact the
    LOCAL-family `app_seq_pairing` preservation needs to rule out an install
    RESETTING an already-advanced application write seq. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_handshaking_write_app_seq_zero (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        ControlHandshaking? st.cs_model.model_control)
      (ensures
        st.cs_model.model_record.record_write.R.epoch =!= R.Application \/
        st.cs_model.model_record.record_write.R.seq == 0)
  = lemma_initial_handshaking_write_epoch_shape st.cs_model.model_config;
    lemma_single_step_handshaking_write_epoch_shape ();
    let p = conn_handshaking_write_epoch_shape in
    let stable :
      squash (forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
    RTC.stable_on_closure connection_state_single_step p stable;
    assert (p (initial st.cs_model.model_config));
    assert (connection_state_evolves (initial st.cs_model.model_config) st);
    assert (p st)
#pop-options

let lemma_client_application_ready_stable_x25519_key_share_projection
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        st.cs_model.model_control == ControlApplicationData /\
        application_record_keys_installed_for_role ClientEndpoint st.cs_model)
      (ensures stable_client_x25519_key_share_projection st)
=
  lemma_connection_state_consistent_client_x25519_reachable_shape st;
  lemma_connection_application_keys_supported_profile_key_schedule_lineage
    ClientEndpoint
    st;
  match st.cs_model.model_handshake.hs_keys.ks_shared_secret with
  | Some _ ->
    ()
  | None ->
    assert False

let lemma_server_application_ready_stable_x25519_key_share_projection
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlApplicationData /\
        application_record_keys_installed_for_role ServerEndpoint st.cs_model)
      (ensures stable_server_x25519_key_share_projection st)
=
  lemma_connection_state_consistent_server_x25519_reachable_shape st;
  lemma_connection_application_keys_supported_profile_key_schedule_lineage
    ServerEndpoint
    st;
  match st.cs_model.model_handshake.hs_keys.ks_shared_secret with
  | Some _ ->
    ()
  | None ->
    assert False

#pop-options

let lemma_record_read_key_schedule_projection_client_projection
  (model:connection_model)
  : Lemma
      (ensures
        record_read_key_schedule_projection model ==
        record_read_key_schedule_projection_for_role ClientEndpoint model)
=
  ()

let lemma_record_write_key_schedule_projection_client_projection
  (model:connection_model)
  : Lemma
      (ensures
        record_write_key_schedule_projection model ==
        record_write_key_schedule_projection_for_role ClientEndpoint model)
=
  ()

let lemma_expected_traffic_secret_for_state_agrees
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires traffic_secret_inputs_agree traffic_id client server)
      (ensures
        (match
          expected_traffic_secret_for_state traffic_id client,
          expected_traffic_secret_for_state traffic_id server
        with
        | Some client_secret, Some server_secret -> Seq.equal client_secret server_secret
        | _, _ -> False))
=
  let base_id =
    match traffic_id.traffic_id_epoch with
    | TrafficHandshake -> HandshakeSecret
    | TrafficApplication -> MasterSecret in
  let checkpoint = key_checkpoint_for_epoch traffic_id.traffic_id_epoch in
  match
    base_secret_material base_id client.cs_model.model_handshake.hs_keys,
    base_secret_material base_id server.cs_model.model_handshake.hs_keys,
    transcript_bytes_for_key_checkpoint checkpoint client,
    transcript_bytes_for_key_checkpoint checkpoint server
  with
  | Some client_base, Some server_base, Some client_transcript, Some server_transcript ->
    assert (Seq.equal client_base server_base);
    assert (Seq.equal client_transcript server_transcript);
    Seq.lemma_eq_elim client_base server_base;
    Seq.lemma_eq_elim client_transcript server_transcript;
    assert (expected_traffic_secret_for_state traffic_id client ==
            expected_traffic_secret_for_state traffic_id server)
  | _, _, _, _ ->
    assert False

let lemma_paired_endpoints_derived_key_agrees
  (key_id:derived_key_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        first_milestone_derived_key_id key_id /\
        derivation_inputs_agree key_id client server)
      (ensures peer_derived_key_material_agrees key_id client server)
=
  match key_id with
  | BaseSecret base_id ->
    (match
      base_secret_material base_id client.cs_model.model_handshake.hs_keys,
      base_secret_material base_id server.cs_model.model_handshake.hs_keys
     with
     | Some client_secret, Some server_secret ->
       assert (Seq.equal client_secret server_secret)
     | _, _ -> assert False)
  | TrafficSecret traffic_id ->
    lemma_expected_traffic_secret_for_state_agrees traffic_id client server
  | TrafficKey traffic_id ->
    lemma_expected_traffic_secret_for_state_agrees traffic_id client server;
    (match
      expected_traffic_secret_for_state traffic_id client,
      expected_traffic_secret_for_state traffic_id server
     with
     | Some client_secret, Some server_secret ->
       assert (Seq.equal client_secret server_secret);
       Seq.lemma_eq_elim client_secret server_secret
     | _, _ -> assert False)
  | TrafficIV traffic_id ->
    lemma_expected_traffic_secret_for_state_agrees traffic_id client server;
    (match
      expected_traffic_secret_for_state traffic_id client,
      expected_traffic_secret_for_state traffic_id server
     with
     | Some client_secret, Some server_secret ->
       assert (Seq.equal client_secret server_secret);
       Seq.lemma_eq_elim client_secret server_secret
     | _, _ -> assert False)
  | FinishedKey label ->
    let traffic_id = { traffic_id_epoch = TrafficHandshake; traffic_id_label = label } in
    lemma_expected_traffic_secret_for_state_agrees traffic_id client server;
    (match
      expected_traffic_secret_for_state traffic_id client,
      expected_traffic_secret_for_state traffic_id server
     with
     | Some client_secret, Some server_secret ->
       assert (Seq.equal client_secret server_secret);
       Seq.lemma_eq_elim client_secret server_secret
     | _, _ -> assert False)
  | TrafficUpdateSecret _
  | ExporterMasterSecret
  | ResumptionMasterSecret ->
    assert False

let lemma_paired_x25519_key_shares_shared_secret_agree
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires paired_x25519_key_shares client server)
      (ensures shared_secret_material_agrees client server)
=
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_start,
    client_hs.hs_server_hello,
    server_hs.hs_server_selection,
    server_hs.hs_client_hello
  with
  | Some start, Some sh, Some selection, Some ch ->
    (* The group comes off the client's ServerHello, and Diffie-Hellman
       agreement is C.lemma_kex_shared_agreement, which dispatches to the
       X25519 or the secp256r1 axiom. *)
    (match server_hello_kex sh with
     | Some (| g, sh_ks |) ->
      (match
        start_kex_private start g,
        server_kex_private selection g,
        client_hs.hs_keys.ks_shared_secret,
        server_hs.hs_keys.ks_shared_secret
       with
       | Some client_sk, Some server_sk, Some client_shared, Some server_shared ->
         C.lemma_kex_shared_agreement
           g
           client_sk
           server_sk
           (start_kex_public start g)
           (server_kex_public selection g);
         (match client_hello_kex ch g with
          | Some ch_ks ->
            assert (ch_ks == start_kex_public start g);
            assert (sh_ks == server_kex_public selection g);
            assert (C.kex_shared g client_sk sh_ks == Some client_shared);
            assert (C.kex_shared g server_sk ch_ks == Some server_shared);
            assert (C.kex_shared g client_sk sh_ks ==
                    C.kex_shared g server_sk ch_ks);
            assert (Some client_shared == Some server_shared);
            assert (client_shared == server_shared);
            Seq.lemma_eq_intro client_shared server_shared
          | None -> assert False)
       | _, _, _, _ -> assert False)
     | None -> assert False)
  | _, _, _, _ -> assert False

#restart-solver
let lemma_shared_secret_lineage_base_secret_agree
  (base_id:base_secret_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        shared_secret_material_agrees client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server)
      (ensures base_secret_inputs_agree base_id client server)
=
  let client_keys = client.cs_model.model_handshake.hs_keys in
  let server_keys = server.cs_model.model_handshake.hs_keys in
  match
    client_keys.ks_shared_secret,
    server_keys.ks_shared_secret,
    client_keys.ks_early_secret,
    server_keys.ks_early_secret,
    client_keys.ks_handshake_secret,
    server_keys.ks_handshake_secret,
    client_keys.ks_master_secret,
    server_keys.ks_master_secret
  with
  | Some client_shared, Some server_shared,
    Some client_early, Some server_early,
    Some client_handshake, Some server_handshake,
    Some client_master, Some server_master ->
    assert (Seq.equal client_shared server_shared);
    assert (Seq.equal client_early (K.early_secret B.empty));
    assert (Seq.equal server_early (K.early_secret B.empty));
    Seq.lemma_eq_elim client_shared server_shared;
    Seq.lemma_eq_elim client_early (K.early_secret B.empty);
    Seq.lemma_eq_elim server_early (K.early_secret B.empty);
    assert (Seq.equal client_early server_early);
    assert (Seq.equal client_handshake (K.handshake_secret client_early client_shared));
    assert (Seq.equal server_handshake (K.handshake_secret server_early server_shared));
    Seq.lemma_eq_elim client_handshake (K.handshake_secret client_early client_shared);
    Seq.lemma_eq_elim server_handshake (K.handshake_secret server_early server_shared);
    assert (Seq.equal client_handshake server_handshake);
    assert (Seq.equal client_master (K.master_secret client_handshake));
    assert (Seq.equal server_master (K.master_secret server_handshake));
    Seq.lemma_eq_elim client_handshake server_handshake;
    Seq.lemma_eq_elim client_master (K.master_secret client_handshake);
    Seq.lemma_eq_elim server_master (K.master_secret server_handshake);
    assert (Seq.equal client_master server_master);
    (match base_id with
     | EarlySecret -> assert (Seq.equal client_early server_early)
     | HandshakeSecret -> assert (Seq.equal client_handshake server_handshake)
     | MasterSecret -> assert (Seq.equal client_master server_master))
  | _, _, _, _, _, _, _, _ ->
    assert False

let lemma_paired_x25519_key_shares_base_secret_agree
  (base_id:base_secret_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        paired_x25519_key_shares client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server)
      (ensures base_secret_inputs_agree base_id client server)
=
  lemma_paired_x25519_key_shares_shared_secret_agree client server;
  lemma_shared_secret_lineage_base_secret_agree base_id client server

let lemma_paired_x25519_key_shares_derived_key_agrees
  (key_id:derived_key_id)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        first_milestone_derived_key_id key_id /\
        paired_x25519_key_shares client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server /\
        derivation_checkpoint_inputs_agree key_id client server)
      (ensures peer_derived_key_material_agrees key_id client server)
=
  (match key_id with
   | BaseSecret base_id ->
     lemma_paired_x25519_key_shares_base_secret_agree base_id client server;
     assert (derivation_inputs_agree key_id client server)
   | TrafficSecret traffic_id
   | TrafficKey traffic_id
   | TrafficIV traffic_id ->
     let base_id =
       match traffic_id.traffic_id_epoch with
       | TrafficHandshake -> HandshakeSecret
       | TrafficApplication -> MasterSecret in
     lemma_paired_x25519_key_shares_base_secret_agree base_id client server;
     assert (traffic_secret_inputs_agree traffic_id client server);
     assert (derivation_inputs_agree key_id client server)
   | FinishedKey label ->
     lemma_paired_x25519_key_shares_base_secret_agree HandshakeSecret client server;
     assert (traffic_secret_inputs_agree
       { traffic_id_epoch = TrafficHandshake; traffic_id_label = label }
       client
       server);
     assert (derivation_inputs_agree key_id client server)
   | TrafficUpdateSecret _
   | ExporterMasterSecret
   | ResumptionMasterSecret ->
     assert False);
  lemma_paired_endpoints_derived_key_agrees key_id client server

let lemma_paired_handshake_events_same_transcript_checkpoint
  (checkpoint:transcript_checkpoint)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires paired_handshake_events client server)
      (ensures same_transcript_checkpoint checkpoint client server)
=
  match checkpoint with
  | TH_CH -> ()
  | TH_SH -> ()
  | TH_before_CV -> ()
  | TH_before_SF -> ()
  | TH_SF -> ()
  | TH_CF -> ()

let lemma_paired_handshake_events_same_key_derivation_checkpoint
  (checkpoint:key_derivation_checkpoint)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        paired_handshake_events client server /\
        (checkpoint == DeriveHandshakeTraffic \/
         checkpoint == DeriveApplicationTraffic))
      (ensures same_key_derivation_checkpoint checkpoint client server)
=
  match checkpoint with
  | DeriveHandshakeTraffic ->
    lemma_paired_handshake_events_same_transcript_checkpoint TH_SH client server
  | DeriveApplicationTraffic ->
    lemma_paired_handshake_events_same_transcript_checkpoint TH_SF client server
  | DeriveTrafficUpdate _ ->
    assert False

let lemma_paired_supported_profile_all_derived_key_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        paired_x25519_key_shares client server /\
        connection_supported_profile_key_schedule_lineage client /\
        connection_supported_profile_key_schedule_lineage server /\
        paired_key_derivation_checkpoints client server)
      (ensures
        supported_profile_all_derived_key_material_agrees client server)
=
  assert (same_key_derivation_checkpoint DeriveHandshakeTraffic client server);
  assert (same_key_derivation_checkpoint DeriveApplicationTraffic client server);
  lemma_paired_x25519_key_shares_derived_key_agrees
    (BaseSecret EarlySecret) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (BaseSecret HandshakeSecret) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (BaseSecret MasterSecret) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficSecret (traffic_id TrafficHandshake ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficSecret (traffic_id TrafficHandshake ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficSecret (traffic_id TrafficApplication ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficSecret (traffic_id TrafficApplication ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficKey (traffic_id TrafficHandshake ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficKey (traffic_id TrafficHandshake ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficKey (traffic_id TrafficApplication ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficKey (traffic_id TrafficApplication ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficIV (traffic_id TrafficHandshake ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficIV (traffic_id TrafficHandshake ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficIV (traffic_id TrafficApplication ClientTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (TrafficIV (traffic_id TrafficApplication ServerTraffic)) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (FinishedKey ClientTraffic) client server;
  lemma_paired_x25519_key_shares_derived_key_agrees
    (FinishedKey ServerTraffic) client server

let lemma_key_schedule_traffic_record_material_agrees_from_expected
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        peer_derived_key_material_agrees (TrafficKey traffic_id) client server /\
        peer_derived_key_material_agrees (TrafficIV traffic_id) client server /\
        traffic_material_matches_expected_derived_material traffic_id client /\
        traffic_material_matches_expected_derived_material traffic_id server)
      (ensures
        key_schedule_traffic_record_material_agrees traffic_id client server)
=
  match
    traffic_material_for_label
      client.cs_model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label,
    expected_derived_key_material (TrafficKey traffic_id) client,
    expected_derived_key_material (TrafficIV traffic_id) client,
    traffic_material_for_label
      server.cs_model.model_handshake.hs_keys
      traffic_id.traffic_id_epoch
      traffic_id.traffic_id_label,
    expected_derived_key_material (TrafficKey traffic_id) server,
    expected_derived_key_material (TrafficIV traffic_id) server
  with
  | Some client_material, Some client_key, Some client_iv,
    Some server_material, Some server_key, Some server_iv ->
    assert (Seq.equal client_material.traffic_key client_key);
    assert (Seq.equal client_material.traffic_iv client_iv);
    assert (Seq.equal server_material.traffic_key server_key);
    assert (Seq.equal server_material.traffic_iv server_iv);
    assert (Seq.equal client_key server_key);
    assert (Seq.equal client_iv server_iv);
    Seq.lemma_eq_elim client_material.traffic_key client_key;
    Seq.lemma_eq_elim server_material.traffic_key server_key;
    Seq.lemma_eq_elim client_key server_key;
    Seq.lemma_eq_elim client_material.traffic_iv client_iv;
    Seq.lemma_eq_elim server_material.traffic_iv server_iv;
    Seq.lemma_eq_elim client_iv server_iv;
    assert (Seq.equal client_material.traffic_key server_material.traffic_key);
    assert (Seq.equal client_material.traffic_iv server_material.traffic_iv)
  | _, _, _, _, _, _ ->
    assert False

let lemma_application_record_direction_material_matches_key_schedule_for_role
  (role:endpoint_role)
  (dir:traffic_direction)
  (model:connection_model)
  : Lemma
      (requires
        application_record_keys_installed_for_role role model /\
        application_record_epochs_installed_for_role role model)
      (ensures
        record_direction_material_matches_key_schedule_for_role
          role
          dir
          (traffic_id
            TrafficApplication
            (traffic_label_for_endpoint_direction role dir))
          model)
=
  let keys = model.model_handshake.hs_keys in
  match role, dir with
  | ClientEndpoint, TrafficRead ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
    assert (model.model_record.record_read.R.epoch == R.Application);
    (match
      traffic_material_for_label keys TrafficApplication ServerTraffic,
      record_direction_material model.model_record.record_read
     with
     | Some material, Some record_material ->
       assert (traffic_material_matches_record_direction material model.model_record.record_read);
       assert (model.model_record.record_read.R.key == Some material.traffic_key);
       assert (model.model_record.record_read.R.static_iv == Some material.traffic_iv);
       assert (Seq.equal material.traffic_key record_material.record_material_key);
       assert (Seq.equal material.traffic_iv record_material.record_material_iv)
     | _, _ ->
       assert False)
  | ClientEndpoint, TrafficWrite ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
    assert (model.model_record.record_write.R.epoch == R.Application);
    (match
      traffic_material_for_label keys TrafficApplication ClientTraffic,
      record_direction_material model.model_record.record_write
     with
     | Some material, Some record_material ->
       assert (traffic_material_matches_record_direction material model.model_record.record_write);
       assert (model.model_record.record_write.R.key == Some material.traffic_key);
       assert (model.model_record.record_write.R.static_iv == Some material.traffic_iv);
       assert (Seq.equal material.traffic_key record_material.record_material_key);
       assert (Seq.equal material.traffic_iv record_material.record_material_iv)
     | _, _ ->
       assert False)
  | ServerEndpoint, TrafficRead ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
    assert (model.model_record.record_read.R.epoch == R.Application);
    (match
      traffic_material_for_label keys TrafficApplication ClientTraffic,
      record_direction_material model.model_record.record_read
     with
     | Some material, Some record_material ->
       assert (traffic_material_matches_record_direction material model.model_record.record_read);
       assert (model.model_record.record_read.R.key == Some material.traffic_key);
       assert (model.model_record.record_read.R.static_iv == Some material.traffic_iv);
       assert (Seq.equal material.traffic_key record_material.record_material_key);
       assert (Seq.equal material.traffic_iv record_material.record_material_iv)
     | _, _ ->
       assert False)
  | ServerEndpoint, TrafficWrite ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
    assert (model.model_record.record_write.R.epoch == R.Application);
    (match
      traffic_material_for_label keys TrafficApplication ServerTraffic,
      record_direction_material model.model_record.record_write
     with
     | Some material, Some record_material ->
       assert (traffic_material_matches_record_direction material model.model_record.record_write);
       assert (model.model_record.record_write.R.key == Some material.traffic_key);
       assert (model.model_record.record_write.R.static_iv == Some material.traffic_iv);
       assert (Seq.equal material.traffic_key record_material.record_material_key);
       assert (Seq.equal material.traffic_iv record_material.record_material_iv)
     | _, _ ->
       assert False)

let lemma_peer_record_material_agrees
  (traffic_id:labeled_traffic_epoch)
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires peer_record_material_inputs_agree traffic_id client server)
      (ensures peer_record_material_agrees traffic_id client server)
=
  match traffic_id.traffic_id_label with
  | ClientTraffic ->
    let client_st = client.cs_model.model_record.record_write in
    let server_st = server.cs_model.model_record.record_read in
    (match
      traffic_material_for_label
        client.cs_model.model_handshake.hs_keys
        traffic_id.traffic_id_epoch
        ClientTraffic,
      traffic_material_for_label
        server.cs_model.model_handshake.hs_keys
        traffic_id.traffic_id_epoch
        ClientTraffic,
      record_direction_material client_st,
      record_direction_material server_st
     with
     | Some client_material, Some server_material,
       Some client_record, Some server_record ->
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material client_material)
         (record_material_of_traffic_material server_material));
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material client_material)
         client_record);
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material server_material)
         server_record);
       assert (Seq.equal client_material.traffic_key server_material.traffic_key);
       assert (Seq.equal client_material.traffic_iv server_material.traffic_iv);
       assert (Seq.equal client_material.traffic_key client_record.record_material_key);
       assert (Seq.equal client_material.traffic_iv client_record.record_material_iv);
       assert (Seq.equal server_material.traffic_key server_record.record_material_key);
       assert (Seq.equal server_material.traffic_iv server_record.record_material_iv);
       Seq.lemma_eq_elim client_material.traffic_key client_record.record_material_key;
       Seq.lemma_eq_elim client_material.traffic_iv client_record.record_material_iv;
       Seq.lemma_eq_elim client_material.traffic_key server_material.traffic_key;
       Seq.lemma_eq_elim client_material.traffic_iv server_material.traffic_iv;
       Seq.lemma_eq_elim server_material.traffic_key server_record.record_material_key;
       Seq.lemma_eq_elim server_material.traffic_iv server_record.record_material_iv;
       assert (Seq.equal client_record.record_material_key server_record.record_material_key);
       assert (Seq.equal client_record.record_material_iv server_record.record_material_iv)
     | _, _, _, _ ->
       assert False)
  | ServerTraffic ->
    let server_st = server.cs_model.model_record.record_write in
    let client_st = client.cs_model.model_record.record_read in
    (match
      traffic_material_for_label
        client.cs_model.model_handshake.hs_keys
        traffic_id.traffic_id_epoch
        ServerTraffic,
      traffic_material_for_label
        server.cs_model.model_handshake.hs_keys
        traffic_id.traffic_id_epoch
        ServerTraffic,
      record_direction_material client_st,
      record_direction_material server_st
     with
     | Some client_material, Some server_material,
       Some client_record, Some server_record ->
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material client_material)
         (record_material_of_traffic_material server_material));
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material client_material)
         client_record);
       assert (record_key_iv_material_agrees
         (record_material_of_traffic_material server_material)
         server_record);
       assert (Seq.equal client_material.traffic_key server_material.traffic_key);
       assert (Seq.equal client_material.traffic_iv server_material.traffic_iv);
       assert (Seq.equal client_material.traffic_key client_record.record_material_key);
       assert (Seq.equal client_material.traffic_iv client_record.record_material_iv);
       assert (Seq.equal server_material.traffic_key server_record.record_material_key);
       assert (Seq.equal server_material.traffic_iv server_record.record_material_iv);
       Seq.lemma_eq_elim client_material.traffic_key client_record.record_material_key;
       Seq.lemma_eq_elim client_material.traffic_iv client_record.record_material_iv;
       Seq.lemma_eq_elim client_material.traffic_key server_material.traffic_key;
       Seq.lemma_eq_elim client_material.traffic_iv server_material.traffic_iv;
       Seq.lemma_eq_elim server_material.traffic_key server_record.record_material_key;
       Seq.lemma_eq_elim server_material.traffic_iv server_record.record_material_iv;
       assert (Seq.equal server_record.record_material_key client_record.record_material_key);
       assert (Seq.equal server_record.record_material_iv client_record.record_material_iv)
     | _, _, _, _ ->
       assert False)

let lemma_paired_supported_profile_all_record_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
     (requires
       supported_profile_all_record_material_inputs_agree client server)
     (ensures
       supported_profile_all_record_material_agrees client server)
=
  lemma_peer_record_material_agrees
    (traffic_id TrafficHandshake ClientTraffic) client server;
  lemma_peer_record_material_agrees
    (traffic_id TrafficHandshake ServerTraffic) client server;
  lemma_peer_record_material_agrees
    (traffic_id TrafficApplication ClientTraffic) client server;
  lemma_peer_record_material_agrees
    (traffic_id TrafficApplication ServerTraffic) client server

let lemma_paired_supported_profile_application_record_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
     (requires
       supported_profile_application_record_material_inputs_agree client server)
     (ensures
       supported_profile_application_record_material_agrees client server)
=
  lemma_peer_record_material_agrees
    (traffic_id TrafficApplication ClientTraffic) client server;
  lemma_peer_record_material_agrees
    (traffic_id TrafficApplication ServerTraffic) client server

let lemma_supported_profile_application_record_material_inputs_agree_from_expected
  (client:connection_state)
  (server:connection_state)
  : Lemma
      (requires
        supported_profile_all_derived_key_material_agrees client server /\
        supported_profile_application_traffic_material_matches_expected client /\
        supported_profile_application_traffic_material_matches_expected server /\
        application_record_keys_installed_for_role
          ClientEndpoint
          client.cs_model /\
        application_record_epochs_installed_for_role
          ClientEndpoint
          client.cs_model /\
        application_record_keys_installed_for_role
          ServerEndpoint
          server.cs_model /\
        application_record_epochs_installed_for_role
          ServerEndpoint
          server.cs_model)
      (ensures
        supported_profile_application_record_material_inputs_agree client server)
=
  let client_app = traffic_id TrafficApplication ClientTraffic in
  let server_app = traffic_id TrafficApplication ServerTraffic in
  assert (peer_derived_key_material_agrees (TrafficKey client_app) client server);
  assert (peer_derived_key_material_agrees (TrafficIV client_app) client server);
  assert (peer_derived_key_material_agrees (TrafficKey server_app) client server);
  assert (peer_derived_key_material_agrees (TrafficIV server_app) client server);
  assert (traffic_material_matches_expected_derived_material client_app client);
  assert (traffic_material_matches_expected_derived_material client_app server);
  assert (traffic_material_matches_expected_derived_material server_app client);
  assert (traffic_material_matches_expected_derived_material server_app server);
  lemma_key_schedule_traffic_record_material_agrees_from_expected
    client_app
    client
    server;
  lemma_key_schedule_traffic_record_material_agrees_from_expected
    server_app
    client
    server;
  lemma_application_record_direction_material_matches_key_schedule_for_role
    ClientEndpoint
    TrafficWrite
    client.cs_model;
  lemma_application_record_direction_material_matches_key_schedule_for_role
    ServerEndpoint
    TrafficRead
    server.cs_model;
  lemma_application_record_direction_material_matches_key_schedule_for_role
    ServerEndpoint
    TrafficWrite
    server.cs_model;
  lemma_application_record_direction_material_matches_key_schedule_for_role
    ClientEndpoint
    TrafficRead
    client.cs_model;
  assert (peer_record_material_inputs_agree client_app client server);
  assert (peer_record_material_inputs_agree server_app client server)

let lemma_no_key_update_application_traffic_material_matches_expected
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        first_epoch_application_traffic_material_no_key_update_invariant st /\
        st.cs_model.model_config.config_role == role /\
        st.cs_model.model_control == ControlApplicationData /\
        application_record_keys_installed_for_role role st.cs_model)
      (ensures supported_profile_application_traffic_material_matches_expected st)
=
  match role with
  | ClientEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_server_application_traffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_client_application_traffic)
  | ServerEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_client_application_traffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_server_application_traffic)

let lemma_supported_profile_client_server_key_material_agrees
  (client:connection_state)
  (server:connection_state)
  : Lemma
     (requires
       supported_profile_client_server_key_material_inputs_agree client server)
     (ensures
       supported_profile_client_server_key_material_agrees client server)
=
  lemma_paired_supported_profile_all_derived_key_material_agrees client server;
  lemma_paired_supported_profile_application_record_material_agrees client server

let lemma_step_role_install_record_keys_consistent_for_role
  (role:endpoint_role)
  (model0:connection_model)
  (install:traffic_key_install)
  (model1:connection_model)
  : Lemma
      (requires
        model_record_keys_consistent_for_role role model0 /\
        traffic_install_allowed_at_stage_for_role
          role
          (match model0.model_control with
           | ControlHandshaking stage -> stage
           | _ -> HsNotStarted)
          install /\
        traffic_install_matches_key_schedule_for_role
          role
          model0.model_handshake
          install /\
        step_local_event
          model0
          (LocalInstallTrafficKeysForRole
            { install_role = role; install_payload = install }) == Some model1)
      (ensures model_record_keys_consistent_for_role role model1)
=
  ()

let lemma_initial_record_keys_consistent_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma (connection_state_record_keys_consistent_for_role role (initial cfg))
=
  ()

let lemma_initial_layered_log_consistent_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma (connection_state_layered_log_consistent_for_role role (initial cfg))
=
  ()

let lemma_model_record_keys_consistent_record_read_key_schedule_projection
  (model:connection_model)
  : Lemma
      (requires model_record_keys_consistent model)
      (ensures record_read_key_schedule_projection model)
=
  match model.model_control with
  | ControlFailed _ -> ()
  | _ ->
    let keys = model.model_handshake.hs_keys in
    let st = model.model_record.record_read in
    assert (record_read_keys_match_key_schedule keys st);
    (match st.R.epoch with
     | R.Initial -> ()
     | R.Handshake ->
       assert (traffic_material_option_matches_record_direction
         keys.ks_server_handshake_traffic
         st);
       (match keys.ks_server_handshake_traffic with
        | Some material ->
          assert (traffic_material_matches_record_direction material st);
          assert (exists material'.
            keys.ks_server_handshake_traffic == Some material' /\
            traffic_material_matches_record_direction material' st)
        | None -> assert False)
     | R.Application ->
       assert (traffic_material_option_matches_record_direction
         keys.ks_server_application_traffic
         st);
       (match keys.ks_server_application_traffic with
        | Some material ->
          assert (traffic_material_matches_record_direction material st);
          assert (exists material'.
            keys.ks_server_application_traffic == Some material' /\
            traffic_material_matches_record_direction material' st)
        | None -> assert False))

let lemma_model_record_keys_consistent_record_write_key_schedule_projection
  (model:connection_model)
  : Lemma
      (requires model_record_keys_consistent model)
      (ensures record_write_key_schedule_projection model)
=
  match model.model_control with
  | ControlFailed _ -> ()
  | _ ->
    let keys = model.model_handshake.hs_keys in
    let st = model.model_record.record_write in
    assert (record_write_keys_match_key_schedule model.model_control keys st);
    (match st.R.epoch with
     | R.Initial -> ()
     | R.Handshake ->
       assert (traffic_material_option_matches_record_direction
         keys.ks_client_handshake_traffic
         st);
       (match keys.ks_client_handshake_traffic with
        | Some material ->
          assert (traffic_material_matches_record_direction material st);
          assert (exists material'.
            keys.ks_client_handshake_traffic == Some material' /\
            traffic_material_matches_record_direction material' st)
        | None -> assert False)
     | R.Application ->
       (match model.model_control with
        | ControlHandshaking _ -> ()
        | _ ->
          assert (traffic_material_option_matches_record_direction
            keys.ks_client_application_traffic
            st);
          (match keys.ks_client_application_traffic with
           | Some material ->
             assert (traffic_material_matches_record_direction material st);
             assert (exists material'.
               keys.ks_client_application_traffic == Some material' /\
               traffic_material_matches_record_direction material' st)
           | None ->            assert False)))

let lemma_record_read_keys_next_seq
  (keys:key_schedule_state)
  (st:R.direction_state)
  : Lemma
      (requires record_read_keys_match_key_schedule keys st)
      (ensures record_read_keys_match_key_schedule keys (R.next_seq st))
=
  ()

let lemma_record_write_keys_next_seq
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  : Lemma
      (requires record_write_keys_match_key_schedule control keys st)
      (ensures record_write_keys_match_key_schedule control keys (R.next_seq st))
=
  ()

let lemma_record_keys_next_seq_for_role
  (role:endpoint_role)
  (dir:traffic_direction)
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  : Lemma
      (requires record_keys_match_key_schedule_for_role role dir control keys st)
      (ensures record_keys_match_key_schedule_for_role role dir control keys (R.next_seq st))
=
  ()

let rec lemma_record_write_keys_advance
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  (n:nat)
  : Lemma
      (requires record_write_keys_match_key_schedule control keys st)
      (ensures
        record_write_keys_match_key_schedule
          control
          keys
          (advance_direction_records st n))
      (decreases n)
=
  if n = 0 then ()
  else lemma_record_write_keys_advance control keys st (n - 1)

let rec lemma_record_keys_advance_for_role
  (role:endpoint_role)
  (dir:traffic_direction)
  (control:connection_control_state)
  (keys:key_schedule_state)
  (st:R.direction_state)
  (n:nat)
  : Lemma
      (requires record_keys_match_key_schedule_for_role role dir control keys st)
      (ensures
        record_keys_match_key_schedule_for_role
          role
          dir
          control
          keys
          (advance_direction_records st n))
      (decreases n)
=
  if n = 0 then ()
  else lemma_record_keys_advance_for_role role dir control keys st (n - 1)

let lemma_initial_app_log_consistent
  (cfg:connection_config)
  : Lemma (connection_state_app_log_consistent (initial cfg))
=
  ()

let lemma_initial_pending_application_consistent
  (cfg:connection_config)
  : Lemma (connection_state_pending_application_consistent (initial cfg))
=
  ()

let lemma_initial_transcript_consistent
  (cfg:connection_config)
  : Lemma (connection_state_transcript_consistent (initial cfg))
=
  ()

let lemma_initial_event_log_consistent
  (cfg:connection_config)
  : Lemma
      (connection_state_event_log_consistent_with cfg (initial cfg) /\
       connection_state_event_log_consistent (initial cfg))
=
  ()

let lemma_initial_key_update_pending_consistent
  (cfg:connection_config)
  : Lemma (connection_state_key_update_pending_consistent (initial cfg))
=
  ()

let lemma_initial_record_layer_consistent
  (cfg:connection_config)
  : Lemma (connection_state_record_layer_consistent (initial cfg))
=
  ()

let lemma_initial_record_keys_consistent
  (cfg:connection_config)
  : Lemma
      (requires cfg.config_role == ClientEndpoint)
      (ensures connection_state_record_keys_consistent (initial cfg))
=
  ()

let lemma_initial_layered_log_consistent
  (cfg:connection_config)
  : Lemma
      (requires cfg.config_role == ClientEndpoint)
      (ensures connection_state_layered_log_consistent (initial cfg))
=
  lemma_initial_layered_log_consistent_for_role ClientEndpoint cfg

let rec lemma_app_sent_messages_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        app_sent_messages (events @ [ev]) ==
          app_sent_messages events @ conn_event_app_sent_delta ev)
      (decreases events)
=
  match events with
  | [] -> ()
  | hd :: tl ->
    lemma_app_sent_messages_snoc tl ev;
    append_assoc
      (conn_event_app_sent_delta hd)
      (app_sent_messages tl)
      (conn_event_app_sent_delta ev)

let rec lemma_app_received_messages_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        app_received_messages (events @ [ev]) ==
          app_received_messages events @ conn_event_app_received_delta ev)
      (decreases events)
=
  match events with
  | [] -> ()
  | hd :: tl ->
    lemma_app_received_messages_snoc tl ev;
    append_assoc
      (conn_event_app_received_delta hd)
      (app_received_messages tl)
      (conn_event_app_received_delta ev)

#restart-solver
let rec lemma_transcript_bytes_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        B.append
          (transcript_bytes_of_conn_events events)
          (conn_event_transcript_delta ev) ==
        transcript_bytes_of_conn_events (events @ [ev]))
      (decreases events)
=
  match events with
  | [] ->
    CL.lemma_append_empty_left (conn_event_transcript_delta ev);
    CL.lemma_append_empty_right (conn_event_transcript_delta ev)
  | hd :: tl ->
    lemma_transcript_bytes_snoc tl ev;
    Seq.append_assoc
      (conn_event_transcript_delta hd)
      (transcript_bytes_of_conn_events tl)
      (conn_event_transcript_delta ev)

let rec lemma_key_update_response_pending_after_events_snoc
  (pending:bool)
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        key_update_response_pending_after_events_from pending (events @ [ev]) ==
          key_update_response_pending_step
            (key_update_response_pending_after_events_from pending events)
            ev)
      (decreases events)
=
  match events with
  | [] -> ()
  | hd :: tl ->
    lemma_key_update_response_pending_after_events_snoc
      (key_update_response_pending_step pending hd)
      tl
      ev

let lemma_key_update_response_pending_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        key_update_response_pending_of_conn_events (events @ [ev]) ==
          key_update_response_pending_step
            (key_update_response_pending_of_conn_events events)
            ev)
=
  lemma_key_update_response_pending_after_events_snoc false events ev

let rec lemma_projected_record_layer_after_events_snoc_for_role
  (role:endpoint_role)
  (record:projected_record_layer_state)
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        projected_record_layer_after_events_from_for_role role record (events @ [ev]) ==
          projected_record_layer_step_for_role
            role
            (projected_record_layer_after_events_from_for_role role record events)
            ev)
      (decreases events)
=
  match events with
  | [] -> ()
  | hd :: tl ->
    lemma_projected_record_layer_after_events_snoc_for_role
      role
      (projected_record_layer_step_for_role role record hd)
      tl
      ev

let lemma_projected_record_layer_after_events_snoc
  (record:projected_record_layer_state)
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        projected_record_layer_after_events_from record (events @ [ev]) ==
          projected_record_layer_step
            (projected_record_layer_after_events_from record events)
            ev)
=
  lemma_projected_record_layer_after_events_snoc_for_role
    ClientEndpoint
    record
    events
    ev

let lemma_projected_record_layer_snoc_for_role
  (role:endpoint_role)
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        projected_record_layer_of_conn_events_for_role role (events @ [ev]) ==
          projected_record_layer_step_for_role
            role
            (projected_record_layer_of_conn_events_for_role role events)
            ev)
=
  lemma_projected_record_layer_after_events_snoc_for_role
    role
    initial_projected_record_layer_state
    events
    ev

let lemma_projected_record_layer_snoc
  (events:list conn_event)
  (ev:conn_event)
  : Lemma
      (ensures
        projected_record_layer_of_conn_events (events @ [ev]) ==
          projected_record_layer_step
            (projected_record_layer_of_conn_events events)
            ev)
=
  lemma_projected_record_layer_snoc_for_role ClientEndpoint events ev

let rec lemma_projected_advance_records_of_record
  (st:R.direction_state)
  (n:nat)
  : Lemma
      (ensures
        projected_direction_state_of_record (advance_direction_records st n) ==
          projected_advance_records (projected_direction_state_of_record st) n)
      (decreases n)
=
  if n = 0 then ()
  else lemma_projected_advance_records_of_record st (n - 1)

let lemma_projected_next_seq_of_record
  (st:R.direction_state)
  : Lemma
      (projected_direction_state_of_record (R.next_seq st) ==
        projected_next_seq (projected_direction_state_of_record st))
=
  ()

let lemma_projected_install_keys_of_record
  (st:R.direction_state)
  (epoch:R.epoch)
  (alg:C.aead_alg)
  (key:C.aead_key_any)
  (iv:C.aead_nonce)
  : Lemma
      (projected_direction_state_of_record (R.install_keys st epoch alg key iv) ==
        projected_install_keys epoch)
=
  ()

let lemma_projected_install_record_keys_of_record
  (record:record_layer_state)
  (install:traffic_key_install)
  : Lemma
      (projected_record_layer_state_of_record (install_record_keys record install) ==
        projected_install_record_keys
          (projected_record_layer_state_of_record record)
          install)
=
  match install.install_epoch, install.install_direction with
  | TrafficApplication, TrafficWrite -> ()
  | _, TrafficWrite ->
    lemma_projected_install_keys_of_record
      record.record_write
      (traffic_record_epoch install.install_epoch)
      install.install_material.traffic_alg
      install.install_material.traffic_key
      install.install_material.traffic_iv
  | _, TrafficRead ->
    lemma_projected_install_keys_of_record
      record.record_read
      (traffic_record_epoch install.install_epoch)
      install.install_material.traffic_alg
      install.install_material.traffic_key
      install.install_material.traffic_iv

let lemma_projected_install_record_keys_of_record_for_role
  (role:endpoint_role)
  (record:record_layer_state)
  (install:traffic_key_install)
  : Lemma
      (projected_record_layer_state_of_record
        (install_record_keys_for_role role record install) ==
       projected_install_record_keys_for_role
        role
        (projected_record_layer_state_of_record record)
        install)
=
  match role, install.install_epoch, install.install_direction with
  | ServerEndpoint, TrafficApplication, TrafficWrite ->
    lemma_projected_install_keys_of_record
      record.record_write
      R.Application
      install.install_material.traffic_alg
      install.install_material.traffic_key
      install.install_material.traffic_iv
  | _, _, _ ->
    lemma_projected_install_record_keys_of_record record install

let lemma_projected_client_application_write_after_finished
  (record:record_layer_state)
  (keys:key_schedule_state)
  : Lemma
      (requires Some? keys.ks_client_application_traffic)
      (ensures
        projected_record_layer_state_of_record
          (install_client_application_write_after_finished record keys) ==
        projected_client_application_write_after_finished
          (projected_record_layer_state_of_record record))
=
  match keys.ks_client_application_traffic with
  | Some material ->
    lemma_projected_install_keys_of_record
      (R.next_seq record.record_write)
      R.Application
      material.traffic_alg
      material.traffic_key
      material.traffic_iv
  | None -> assert False

let lemma_projected_record_next_read
  (record:record_layer_state)
  : Lemma
      (ensures
       projected_record_layer_state_of_record
         { record with record_read = R.next_seq record.record_read } ==
       { projected_record_layer_state_of_record record with
           projected_read =
             projected_next_seq
               (projected_record_layer_state_of_record record).projected_read })
=
  lemma_projected_next_seq_of_record record.record_read

let lemma_projected_record_next_write
  (record:record_layer_state)
  : Lemma
      (ensures
       projected_record_layer_state_of_record
         { record with record_write = R.next_seq record.record_write } ==
       { projected_record_layer_state_of_record record with
           projected_write =
             projected_next_seq
               (projected_record_layer_state_of_record record).projected_write })
=
  lemma_projected_next_seq_of_record record.record_write

let lemma_projected_record_advance_write
  (record:record_layer_state)
  (n:nat)
  : Lemma
      (ensures
       projected_record_layer_state_of_record
         { record with record_write = advance_direction_records record.record_write n } ==
       { projected_record_layer_state_of_record record with
           projected_write =
             projected_advance_records
               (projected_record_layer_state_of_record record).projected_write
               n })
=
  lemma_projected_advance_records_of_record record.record_write n

let rec lemma_step_model_many_snoc
  (model0:connection_model)
  (events:list conn_event)
  (ev:conn_event)
  (model1:connection_model)
  (model2:connection_model)
  : Lemma
      (requires
        step_model_many model0 events == Some model1 /\
        step_model model1 ev == Some model2)
      (ensures
        step_model_many model0 (events @ [ev]) == Some model2)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev0 :: rest ->
    (match step_model model0 ev0 with
     | Some mid -> lemma_step_model_many_snoc mid rest ev model1 model2
     | None -> assert False)

let rec lemma_step_model_many_append
  (model0:connection_model)
  (prefix:list conn_event)
  (suffix:list conn_event)
  (mid:connection_model)
  (final:connection_model)
  : Lemma
      (requires
        step_model_many model0 prefix == Some mid /\
        step_model_many mid suffix == Some final)
      (ensures
        step_model_many model0 (FStar.List.Tot.append prefix suffix) ==
        Some final)
      (decreases prefix)
=
  match prefix with
  | [] -> ()
  | ev :: rest ->
    (match step_model model0 ev with
     | Some model1 ->
       lemma_step_model_many_append model1 rest suffix mid final
     | None ->
       assert False)

let rec lemma_step_model_many_append_split
  (model0:connection_model)
  (prefix:list conn_event)
  (suffix:list conn_event)
  (final:connection_model)
  : Lemma
      (requires
        step_model_many model0 (FStar.List.Tot.append prefix suffix) ==
        Some final)
      (ensures
        exists mid.
          step_model_many model0 prefix == Some mid /\
          step_model_many mid suffix == Some final)
      (decreases prefix)
=
  match prefix with
  | [] ->
    introduce exists (mid:connection_model).
      step_model_many model0 [] == Some mid /\
      step_model_many mid suffix == Some final
    with model0 and ()
  | ev :: rest ->
    (match step_model model0 ev with
     | Some model1 ->
       lemma_step_model_many_append_split model1 rest suffix final;
       eliminate exists (mid:connection_model).
         step_model_many model1 rest == Some mid /\
         step_model_many mid suffix == Some final
       with
       ( assert (step_model_many model0 (ev :: rest) == Some mid);
         introduce exists (mid':connection_model).
           step_model_many model0 (ev :: rest) == Some mid' /\
           step_model_many mid' suffix == Some final
         with mid and () )
     | None ->
       assert False)

let lemma_step_model_preserves_config
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires step_model model ev == Some model')
      (ensures model'.model_config == model.model_config)
=
  ()

#push-options "--z3rlimit 10"

let state_of_model_for_first_epoch_application_material
  (model:connection_model)
  : connection_state =
  {
    cs_model = model;
    cs_wire_log = empty_wire_log;
    cs_event_log = [];
  }

let first_epoch_application_traffic_material_slots_match_expected_model
  (model:connection_model)
  : prop =
  first_epoch_application_traffic_material_slots_match_expected
    (state_of_model_for_first_epoch_application_material model)

let application_traffic_key_slot_stage_shape_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  let keys = model.model_handshake.hs_keys in
  match role, model.model_control with
  | ClientEndpoint, ControlNew
  | ClientEndpoint, ControlHandshaking HsStarted
  | ClientEndpoint, ControlHandshaking HsClientHelloSent
  | ClientEndpoint, ControlHandshaking HsServerHelloReceived
  | ClientEndpoint, ControlHandshaking HsEncryptedExtensionsReceived
  | ClientEndpoint, ControlHandshaking HsCertificateReceived
  | ClientEndpoint, ControlHandshaking HsCertificateValidated
  | ClientEndpoint, ControlHandshaking HsCertificateVerifyReceived
  | ClientEndpoint, ControlHandshaking HsCertificateVerifyVerified
  | ClientEndpoint, ControlHandshaking HsServerFinishedReceived ->
    no_application_traffic_keys keys
  | ServerEndpoint, ControlNew
  | ServerEndpoint, ControlHandshaking HsAwaitingClientHello
  | ServerEndpoint, ControlHandshaking HsClientHelloReceived
  | ServerEndpoint, ControlHandshaking HsServerHelloSent
  | ServerEndpoint, ControlHandshaking HsServerEncryptedFlightSent ->
    no_application_traffic_keys keys
  | ServerEndpoint, ControlHandshaking HsServerFinishedSent ->
    keys.ks_client_application_traffic == None
  | _, _ ->
    True

(* [legal_event]'s server LocalDeriveSharedSecret arm is group-indexed since G2
   stage S4/S5, which enlarges every VC that carries [legal_event].  This proof
   is a pure case analysis over the event, so splitting the query keeps each
   case's context small rather than raising the rlimit. *)
#push-options "--z3rlimit 40"
let lemma_step_model_preserves_application_traffic_key_slot_stage_shape_for_role
  (role:endpoint_role)
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires
        model.model_config.config_role == role /\
        application_traffic_key_slot_stage_shape_for_role role model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures
        application_traffic_key_slot_stage_shape_for_role role model')
=
  (* Split by hand rather than leaving it to Z3: only the [ConnLocalEvent] case
     carries the group-indexed [legal_event] arm, so the other two cases get a
     small context. *)
  match ev with
  | ConnNetworkEvent _ -> ()
  | ConnProtectedHandshake _ -> ()
  | ConnLocalEvent _ -> ()
#pop-options

let transcript_after_encrypted_extensions_bytes
  (hs:handshake_state)
  : GTot (option B.bytes) =
  match
    hs.hs_client_hello,
    hs.hs_server_hello,
    hs.hs_encrypted_extensions
  with
  | Some ch, Some sh, Some ee ->
    let th_ch = W.serialize_handshake (M.ClientHello ch) in
    let th_sh = append_handshake_bytes th_ch (M.ServerHello sh) in
    Some (append_handshake_bytes th_sh (M.EncryptedExtensions ee))
  | _, _, _ ->
    None

let no_handshake_message_slots_after_start
  (hs:handshake_state)
  : prop =
  hs.hs_client_hello == None /\
  hs.hs_server_hello == None /\
  hs.hs_encrypted_extensions == None /\
  hs.hs_certificate == None /\
  hs.hs_certificate_verify == None /\
  hs.hs_certificate_verify_verified == false /\
  hs.hs_server_finished == None /\
  hs.hs_server_finished_verified == false /\
  hs.hs_client_finished == None

let no_handshake_message_slots_after_client_hello
  (hs:handshake_state)
  : prop =
  Some? hs.hs_client_hello /\
  hs.hs_server_hello == None /\
  hs.hs_encrypted_extensions == None /\
  hs.hs_certificate == None /\
  hs.hs_certificate_verify == None /\
  hs.hs_certificate_verify_verified == false /\
  hs.hs_server_finished == None /\
  hs.hs_server_finished_verified == false /\
  hs.hs_client_finished == None

let no_handshake_message_slots_after_server_hello
  (hs:handshake_state)
  : prop =
  Some? hs.hs_client_hello /\
  Some? hs.hs_server_hello /\
  hs.hs_encrypted_extensions == None /\
  hs.hs_certificate == None /\
  hs.hs_certificate_verify == None /\
  hs.hs_certificate_verify_verified == false /\
  hs.hs_server_finished == None /\
  hs.hs_server_finished_verified == false /\
  hs.hs_client_finished == None

let no_handshake_message_slots_after_encrypted_extensions
  (hs:handshake_state)
  : prop =
  Some? hs.hs_client_hello /\
  Some? hs.hs_server_hello /\
  Some? hs.hs_encrypted_extensions /\
  hs.hs_certificate == None /\
  hs.hs_certificate_verify == None /\
  hs.hs_certificate_verify_verified == false /\
  hs.hs_server_finished == None /\
  hs.hs_server_finished_verified == false /\
  hs.hs_client_finished == None

let no_handshake_message_slots_after_certificate
  (hs:handshake_state)
  : prop =
  Some? hs.hs_client_hello /\
  Some? hs.hs_server_hello /\
  Some? hs.hs_encrypted_extensions /\
  Some? hs.hs_certificate /\
  hs.hs_certificate_verify_verified == false /\
  hs.hs_server_finished == None /\
  hs.hs_server_finished_verified == false /\
  hs.hs_client_finished == None

let no_handshake_message_slots_after_certificate_verify
  (hs:handshake_state)
  : prop =
  Some? hs.hs_client_hello /\
  Some? hs.hs_server_hello /\
  Some? hs.hs_encrypted_extensions /\
  Some? hs.hs_certificate /\
  Some? hs.hs_certificate_verify /\
  hs.hs_server_finished == None /\
  hs.hs_server_finished_verified == false /\
  hs.hs_client_finished == None

let no_handshake_message_slots_after_server_finished_received
  (hs:handshake_state)
  : prop =
  Some? hs.hs_client_hello /\
  Some? hs.hs_server_hello /\
  Some? hs.hs_encrypted_extensions /\
  Some? hs.hs_certificate /\
  Some? hs.hs_certificate_verify /\
  Some? hs.hs_server_finished /\
  hs.hs_server_finished_verified == false /\
  hs.hs_client_finished == None

let no_handshake_message_slots_after_server_finished
  (hs:handshake_state)
  : prop =
  Some? hs.hs_client_hello /\
  Some? hs.hs_server_hello /\
  Some? hs.hs_encrypted_extensions /\
  Some? hs.hs_certificate /\
  Some? hs.hs_certificate_verify /\
  Some? hs.hs_server_finished /\
  hs.hs_client_finished == None

let no_handshake_message_slots_after_client_finished_received
  (hs:handshake_state)
  : prop =
  Some? hs.hs_client_hello /\
  Some? hs.hs_server_hello /\
  Some? hs.hs_encrypted_extensions /\
  Some? hs.hs_certificate /\
  Some? hs.hs_certificate_verify /\
  Some? hs.hs_server_finished /\
  Some? hs.hs_client_finished

let application_traffic_install_checkpoint_ready_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  let hs = model.model_handshake in
  match role, model.model_control with
  | _, ControlNew ->
    hs.hs_transcript == Tr.empty /\
    no_handshake_message_slots_after_start hs
  | ClientEndpoint, ControlHandshaking HsStarted
  | ServerEndpoint, ControlHandshaking HsAwaitingClientHello ->
    hs.hs_transcript == Tr.empty /\
    no_handshake_message_slots_after_start hs
  | ClientEndpoint, ControlHandshaking HsClientHelloSent
  | ServerEndpoint, ControlHandshaking HsClientHelloReceived ->
    no_handshake_message_slots_after_client_hello hs /\
    transcript_checkpoint_bytes TH_CH hs == Some hs.hs_transcript
  | ClientEndpoint, ControlHandshaking HsServerHelloReceived
  | ServerEndpoint, ControlHandshaking HsServerHelloSent ->
    no_handshake_message_slots_after_server_hello hs /\
    transcript_checkpoint_bytes TH_SH hs == Some hs.hs_transcript
  | ClientEndpoint, ControlHandshaking HsEncryptedExtensionsReceived ->
    no_handshake_message_slots_after_encrypted_extensions hs /\
    transcript_after_encrypted_extensions_bytes hs == Some hs.hs_transcript
  | ClientEndpoint, ControlHandshaking HsCertificateReceived
  | ClientEndpoint, ControlHandshaking HsCertificateValidated ->
    no_handshake_message_slots_after_certificate hs /\
    transcript_checkpoint_bytes TH_before_CV hs == Some hs.hs_transcript
  | ClientEndpoint, ControlHandshaking HsCertificateVerifyReceived
  | ClientEndpoint, ControlHandshaking HsCertificateVerifyVerified ->
    no_handshake_message_slots_after_certificate_verify hs /\
    transcript_checkpoint_bytes TH_before_SF hs == Some hs.hs_transcript
  | ClientEndpoint, ControlHandshaking HsServerFinishedReceived ->
    no_handshake_message_slots_after_server_finished_received hs /\
    transcript_checkpoint_bytes TH_before_SF hs == Some hs.hs_transcript
  | ClientEndpoint, ControlHandshaking HsServerFinishedVerified
  | ServerEndpoint, ControlHandshaking HsServerFinishedSent ->
    no_handshake_message_slots_after_server_finished hs /\
    transcript_checkpoint_bytes TH_SF hs == Some hs.hs_transcript
  | ServerEndpoint, ControlHandshaking HsClientFinishedReceived ->
    no_handshake_message_slots_after_client_finished_received hs /\
    transcript_checkpoint_bytes TH_SF hs == Some hs.hs_transcript
  | ServerEndpoint, ControlHandshaking HsServerEncryptedFlightSent ->
    Some? hs.hs_client_hello /\
    Some? hs.hs_server_hello /\
    Some? hs.hs_encrypted_extensions /\
    hs.hs_server_finished == None /\
    hs.hs_server_finished_verified == false /\
    hs.hs_client_finished == None /\
    (if hs.hs_certificate_verify_verified then
      Some? hs.hs_certificate /\
      Some? hs.hs_certificate_verify /\
      transcript_checkpoint_bytes TH_before_SF hs == Some hs.hs_transcript
    else if Some? hs.hs_certificate then
      transcript_checkpoint_bytes TH_before_CV hs == Some hs.hs_transcript
    else
      hs.hs_certificate == None /\
      hs.hs_certificate_verify == None /\
      transcript_after_encrypted_extensions_bytes hs == Some hs.hs_transcript)
  | _, _ ->
    True

let first_epoch_application_traffic_material_replay_invariant_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  model.model_config.config_role == role /\
  model_supported_profile_key_schedule_reachable_shape model /\
  model_application_record_epoch_reachable_shape_for_role role model /\
  application_traffic_key_slot_stage_shape_for_role role model /\
  application_traffic_install_checkpoint_ready_for_role role model /\
  first_epoch_application_traffic_material_slots_match_expected_model model

let lemma_server_hs_server_hello_sent_checkpoint_ready_elim
  (model:connection_model)
  : Lemma
      (requires
        application_traffic_install_checkpoint_ready_for_role
          ServerEndpoint
          model /\
        model.model_control == ControlHandshaking HsServerHelloSent)
      (ensures
        transcript_checkpoint_bytes TH_SH model.model_handshake ==
        Some model.model_handshake.hs_transcript)
=
  match model.model_control with
  | ControlHandshaking HsServerHelloSent ->
    ()
  | _ ->
    assert False

let lemma_client_certificate_verify_verified_checkpoint_ready_elim
  (model:connection_model)
  : Lemma
      (requires
        application_traffic_install_checkpoint_ready_for_role
          ClientEndpoint
          model /\
        model.model_control == ControlHandshaking HsCertificateVerifyVerified)
      (ensures
        transcript_checkpoint_bytes TH_before_SF model.model_handshake ==
        Some model.model_handshake.hs_transcript)
=
  match model.model_control with
  | ControlHandshaking HsCertificateVerifyVerified ->
    ()
  | _ ->
    assert False

let lemma_server_finished_sent_checkpoint_ready_elim
  (model:connection_model)
  : Lemma
      (requires
        application_traffic_install_checkpoint_ready_for_role
          ServerEndpoint
          model /\
        model.model_control == ControlHandshaking HsServerFinishedSent)
      (ensures
        transcript_checkpoint_bytes TH_SF model.model_handshake ==
        Some model.model_handshake.hs_transcript)
=
  match model.model_control with
  | ControlHandshaking HsServerFinishedSent ->
    ()
  | _ ->
    assert False

let lemma_step_sent_client_hello_checkpoint_ready
  (model0:connection_model)
  (ch:GCH.clientHello)
  (model1:connection_model)
  : Lemma
      (requires
        model0.model_control == ControlHandshaking HsStarted /\
        model0.model_handshake.hs_transcript == Tr.empty /\
        no_handshake_message_slots_after_start model0.model_handshake /\
        step_model
          model0
          (ConnNetworkEvent
            { CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.ClientHello ch) }) ==
        Some model1)
      (ensures
        application_traffic_install_checkpoint_ready_for_role
          ClientEndpoint
          model1)
=
  Seq.append_empty_l (W.serialize_handshake (M.ClientHello ch));
  Seq.lemma_create_len 0 B.zero;
  Seq.lemma_empty B.empty;
  assert (B.append B.empty (W.serialize_handshake (M.ClientHello ch)) ==
          W.serialize_handshake (M.ClientHello ch))

let lemma_step_received_client_hello_checkpoint_ready
  (model0:connection_model)
  (ch:GCH.clientHello)
  (model1:connection_model)
  : Lemma
      (requires
        model0.model_control == ControlHandshaking HsAwaitingClientHello /\
        model0.model_handshake.hs_transcript == Tr.empty /\
        no_handshake_message_slots_after_start model0.model_handshake /\
        step_model
          model0
          (ConnNetworkEvent
            { CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ClientHello ch) }) ==
        Some model1)
      (ensures
        application_traffic_install_checkpoint_ready_for_role
          ServerEndpoint
          model1)
=
  Seq.append_empty_l (W.serialize_handshake (M.ClientHello ch));
  Seq.lemma_create_len 0 B.zero;
  Seq.lemma_empty B.empty;
  assert (B.append B.empty (W.serialize_handshake (M.ClientHello ch)) ==
          W.serialize_handshake (M.ClientHello ch))

let lemma_initial_first_epoch_application_traffic_material_replay_invariant_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma
      (requires cfg.config_role == role)
      (ensures
        first_epoch_application_traffic_material_replay_invariant_for_role
          role
          (initial_model cfg))
=
  lemma_initial_application_record_epoch_reachable_shape_for_role role cfg

#push-options "--z3rlimit 100"
let lemma_step_model_preserves_application_traffic_install_checkpoint_ready_for_role
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        model0.model_config.config_role == role /\
        application_traffic_install_checkpoint_ready_for_role role model0 /\
        legal_event model0 ev /\
        step_model model0 ev == Some model1)
      (ensures
        application_traffic_install_checkpoint_ready_for_role role model1)
=
  lemma_step_model_preserves_config model0 ev model1;
  let hs0 = model0.model_handshake in
  match ev with
  | ConnLocalEvent local ->
    (match role, local, model0.model_control with
     | ClientEndpoint,
       LocalStartHandshake _,
       ControlNew ->
       assert (hs0.hs_transcript == Tr.empty)
     | ServerEndpoint,
       LocalStartServer,
       ControlNew ->
       assert (hs0.hs_transcript == Tr.empty)
     | ServerEndpoint,
       LocalSelectServerParameters selection,
       ControlHandshaking HsClientHelloReceived ->
       assert (hs0.hs_client_hello == Some selection.server_selected_client_hello)
     | ClientEndpoint,
       LocalVerifyFinished fin,
       ControlHandshaking HsServerFinishedReceived ->
       assert (transcript_checkpoint_bytes TH_before_SF hs0 ==
               Some hs0.hs_transcript)
     | ServerEndpoint,
       LocalVerifyClientFinished fin,
       ControlHandshaking HsClientFinishedReceived ->
       assert (transcript_checkpoint_bytes TH_SF hs0 ==
               Some hs0.hs_transcript)
     | _, _, _ ->
       ())
  | ConnNetworkEvent msg ->
    (match
       role,
       msg.CL.message_direction,
       msg.CL.message_value,
       model0.model_control
     with
     | ClientEndpoint,
       CL.Sent,
       M.TlsHandshake (M.ClientHello ch),
       ControlHandshaking HsStarted ->
       assert (hs0.hs_transcript == Tr.empty);
       lemma_step_sent_client_hello_checkpoint_ready model0 ch model1
     | ClientEndpoint,
       CL.Received,
       M.TlsHandshake (M.ServerHello sh),
       ControlHandshaking HsClientHelloSent ->
       assert (transcript_checkpoint_bytes TH_CH hs0 ==
               Some hs0.hs_transcript)
     | ClientEndpoint,
       CL.Received,
       M.TlsHandshake (M.EncryptedExtensions ee),
       ControlHandshaking HsServerHelloReceived ->
       assert (transcript_checkpoint_bytes TH_SH hs0 ==
               Some hs0.hs_transcript)
     | ClientEndpoint,
       CL.Received,
       M.TlsHandshake (M.Certificate cert),
       ControlHandshaking HsEncryptedExtensionsReceived ->
       assert (transcript_after_encrypted_extensions_bytes hs0 ==
               Some hs0.hs_transcript)
     | ClientEndpoint,
       CL.Received,
       M.TlsHandshake (M.CertificateVerify cv),
       ControlHandshaking HsCertificateValidated ->
       assert (transcript_checkpoint_bytes TH_before_CV hs0 ==
               Some hs0.hs_transcript)
     | ClientEndpoint,
       CL.Received,
       M.TlsHandshake (M.Finished fin),
       ControlHandshaking HsCertificateVerifyVerified ->
       lemma_client_certificate_verify_verified_checkpoint_ready_elim model0
     | ClientEndpoint,
       CL.Sent,
       M.TlsHandshake (M.Finished fin),
       ControlHandshaking HsServerFinishedVerified ->
       assert (transcript_checkpoint_bytes TH_SF hs0 ==
               Some hs0.hs_transcript)
     | ServerEndpoint,
       CL.Received,
       M.TlsHandshake (M.ClientHello ch),
       ControlHandshaking HsAwaitingClientHello ->
       assert (hs0.hs_transcript == Tr.empty);
       lemma_step_received_client_hello_checkpoint_ready model0 ch model1
     | ServerEndpoint,
       CL.Sent,
       M.TlsHandshake (M.ServerHello sh),
       ControlHandshaking HsClientHelloReceived ->
       assert (transcript_checkpoint_bytes TH_CH hs0 ==
               Some hs0.hs_transcript)
     | ServerEndpoint,
       CL.Sent,
       M.TlsHandshake (M.EncryptedExtensions ee),
       ControlHandshaking HsServerHelloSent ->
       assert (role == ServerEndpoint);
       assert (model0.model_control == ControlHandshaking HsServerHelloSent);
       assert (application_traffic_install_checkpoint_ready_for_role
         ServerEndpoint
         model0);
       (match role, model0.model_control with
        | ServerEndpoint, ControlHandshaking HsServerHelloSent ->
          lemma_server_hs_server_hello_sent_checkpoint_ready_elim model0;
          assert (transcript_checkpoint_bytes TH_SH model0.model_handshake ==
                  Some model0.model_handshake.hs_transcript)
        | _, _ ->
          assert False)
     | ServerEndpoint,
       CL.Sent,
       M.TlsHandshake (M.Certificate cert),
       ControlHandshaking HsServerEncryptedFlightSent ->
       assert (transcript_after_encrypted_extensions_bytes hs0 ==
               Some hs0.hs_transcript)
     | ServerEndpoint,
       CL.Sent,
       M.TlsHandshake (M.CertificateVerify cv),
       ControlHandshaking HsServerEncryptedFlightSent ->
       assert (Some? hs0.hs_certificate);
       assert (hs0.hs_certificate_verify_verified == false);
       assert (transcript_checkpoint_bytes TH_before_CV hs0 ==
               Some hs0.hs_transcript)
     | ServerEndpoint,
       CL.Sent,
       M.TlsHandshake (M.Finished fin),
       ControlHandshaking HsServerEncryptedFlightSent ->
       assert (hs0.hs_certificate_verify_verified);
       assert (transcript_checkpoint_bytes TH_before_SF hs0 ==
               Some hs0.hs_transcript)
     | ServerEndpoint,
       CL.Received,
       M.TlsHandshake (M.Finished fin),
       ControlHandshaking HsServerFinishedSent ->
       lemma_server_finished_sent_checkpoint_ready_elim model0
     | _, _, _, _ ->
       ())
  | ConnProtectedHandshake step ->
    if step.protected_handshake_buffering
    then
      (* Buffering leaves the transcript and control state untouched, so any
         checkpoint that was ready before is still ready. *)
      ()
    else
    (match role, step.protected_handshake_message, model0.model_control with
     | ClientEndpoint, M.EncryptedExtensions _,
      ControlHandshaking HsServerHelloReceived ->
      assert (transcript_checkpoint_bytes TH_SH hs0 ==
              Some hs0.hs_transcript)
     | ClientEndpoint, M.Certificate _,
      ControlHandshaking HsEncryptedExtensionsReceived ->
      assert (transcript_after_encrypted_extensions_bytes hs0 ==
              Some hs0.hs_transcript)
     | ClientEndpoint, M.CertificateVerify _,
      ControlHandshaking HsCertificateValidated ->
      assert (transcript_checkpoint_bytes TH_before_CV hs0 ==
              Some hs0.hs_transcript)
     | ClientEndpoint, M.Finished _,
      ControlHandshaking HsCertificateVerifyVerified ->
      lemma_client_certificate_verify_verified_checkpoint_ready_elim model0
     | _, _, _ ->
      assert False)

#pop-options
#restart-solver
let lemma_application_traffic_install_for_role_material_matches_expected
  (role:endpoint_role)
  (model0:connection_model)
  (stage:handshake_stage)
  (install:traffic_key_install)
  (model1:connection_model)
  : Lemma
      (requires
        model0.model_config.config_role == role /\
        model0.model_control == ControlHandshaking stage /\
        application_traffic_install_checkpoint_ready_for_role role model0 /\
        traffic_install_allowed_at_stage_for_role role stage install /\
        traffic_install_matches_key_schedule_for_role
          role
          model0.model_handshake
          install /\
        install.install_epoch == TrafficApplication /\
        model1.model_handshake ==
          { model0.model_handshake with
              hs_keys =
                update_key_schedule_with_install_for_role
                  role
                  model0.model_handshake.hs_keys
                  install })
      (ensures
        traffic_material_matches_expected_derived_material
          (traffic_id
            TrafficApplication
            (traffic_label_for_endpoint_direction
              role
              install.install_direction))
          (state_of_model_for_first_epoch_application_material model1) /\
        traffic_material_matches_expected_at_count
          (traffic_id
            TrafficApplication
            (traffic_label_for_endpoint_direction
              role
              install.install_direction))
          (state_of_model_for_first_epoch_application_material model1)
          0)
=
  let hs0 = model0.model_handshake in
  let hs1 = model1.model_handshake in
  assert (transcript_checkpoint_bytes TH_SF hs0 == Some hs0.hs_transcript);
  assert (transcript_checkpoint_bytes TH_SF hs1 == Some hs0.hs_transcript);
  match role, install.install_direction with
  | ClientEndpoint, TrafficWrite ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite ==
                 ClientTraffic)
  | ClientEndpoint, TrafficRead ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead ==
                 ServerTraffic)
  | ServerEndpoint, TrafficWrite ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite ==
                 ServerTraffic)
  | ServerEndpoint, TrafficRead ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead ==
                 ClientTraffic);
  match
    expected_traffic_secret_for_role
      role
      hs0
      install.install_epoch
      install.install_direction
  with
  | Some secret ->
    assert (install.install_material ==
      traffic_key_material_for_secret (negotiated_aead_alg hs0) secret);
    assert (install.install_material.traffic_key ==
      K.derive_aead_key (negotiated_aead_alg hs0) secret);
    assert (install.install_material.traffic_iv == K.derive_aead_iv secret);
    Seq.lemma_eq_refl
      install.install_material.traffic_key
      (K.derive_aead_key (negotiated_aead_alg hs0) secret);
    Seq.lemma_eq_refl
      install.install_material.traffic_iv
      (K.derive_aead_iv secret)
  | None ->
    assert False

let lemma_application_traffic_label_match_expected_preserved
  (label:traffic_label)
  (model0:connection_model)
  (model1:connection_model)
  : Lemma
      (requires
        traffic_material_matches_expected_derived_material
          (traffic_id TrafficApplication label)
          (state_of_model_for_first_epoch_application_material model0) /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficApplication
          label ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          label /\
        model1.model_handshake.hs_keys.ks_master_secret ==
        model0.model_handshake.hs_keys.ks_master_secret /\
        negotiated_aead_alg model1.model_handshake ==
          negotiated_aead_alg model0.model_handshake /\
        transcript_checkpoint_bytes TH_SF model1.model_handshake ==
        transcript_checkpoint_bytes TH_SF model0.model_handshake)
      (ensures
        traffic_material_matches_expected_derived_material
          (traffic_id TrafficApplication label)
          (state_of_model_for_first_epoch_application_material model1) /\
        (traffic_material_matches_expected_at_count
           (traffic_id TrafficApplication label)
           (state_of_model_for_first_epoch_application_material model0)
           0 ==>
         traffic_material_matches_expected_at_count
           (traffic_id TrafficApplication label)
           (state_of_model_for_first_epoch_application_material model1)
           0))
=
  let st0 = state_of_model_for_first_epoch_application_material model0 in
  let st1 = state_of_model_for_first_epoch_application_material model1 in
  assert
    (expected_traffic_secret_for_state
      (traffic_id TrafficApplication label)
      st1 ==
     expected_traffic_secret_for_state
      (traffic_id TrafficApplication label)
      st0);
  assert
    (expected_derived_key_material
      (TrafficKey (traffic_id TrafficApplication label))
      st1 ==
     expected_derived_key_material
      (TrafficKey (traffic_id TrafficApplication label))
      st0);
  assert
    (expected_derived_key_material
      (TrafficIV (traffic_id TrafficApplication label))
      st1 ==
     expected_derived_key_material
      (TrafficIV (traffic_id TrafficApplication label))
      st0)

let lemma_first_epoch_application_label_match_expected_preserved
  (label:traffic_label)
  (model0:connection_model)
  (model1:connection_model)
  : Lemma
      (requires
        first_epoch_application_traffic_material_slots_match_expected_model
          model0 /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficApplication
          label ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          label /\
        model1.model_handshake.hs_keys.ks_master_secret ==
        model0.model_handshake.hs_keys.ks_master_secret /\
        negotiated_aead_alg model1.model_handshake ==
          negotiated_aead_alg model0.model_handshake /\
        transcript_checkpoint_bytes TH_SF model1.model_handshake ==
        transcript_checkpoint_bytes TH_SF model0.model_handshake)
      (ensures
        Some?
          (traffic_material_for_label
            model1.model_handshake.hs_keys
            TrafficApplication
            label) ==>
        (traffic_material_matches_expected_derived_material
           (traffic_id TrafficApplication label)
           (state_of_model_for_first_epoch_application_material model1) /\
         traffic_material_matches_expected_at_count
           (traffic_id TrafficApplication label)
           (state_of_model_for_first_epoch_application_material model1)
           0))
=
  match label with
  | ClientTraffic ->
    if Some? model1.model_handshake.hs_keys.ks_client_application_traffic
    then begin
      assert (Some? model0.model_handshake.hs_keys.ks_client_application_traffic);
      assert
        (traffic_material_matches_expected_derived_material
          (traffic_id TrafficApplication ClientTraffic)
          (state_of_model_for_first_epoch_application_material model0));
      assert
        (traffic_material_matches_expected_at_count
          (traffic_id TrafficApplication ClientTraffic)
          (state_of_model_for_first_epoch_application_material model0)
          0);
      lemma_application_traffic_label_match_expected_preserved
        ClientTraffic
        model0
        model1
    end
  | ServerTraffic ->
    if Some? model1.model_handshake.hs_keys.ks_server_application_traffic
    then begin
      assert (Some? model0.model_handshake.hs_keys.ks_server_application_traffic);
      assert
        (traffic_material_matches_expected_derived_material
          (traffic_id TrafficApplication ServerTraffic)
          (state_of_model_for_first_epoch_application_material model0));
      assert
        (traffic_material_matches_expected_at_count
          (traffic_id TrafficApplication ServerTraffic)
          (state_of_model_for_first_epoch_application_material model0)
          0);
      lemma_application_traffic_label_match_expected_preserved
        ServerTraffic
        model0
        model1
    end

let lemma_first_epoch_application_label_match_expected_preserved_when_slot_unchanged_or_checkpoint_stable
  (label:traffic_label)
  (model0:connection_model)
  (model1:connection_model)
  : Lemma
      (requires
        first_epoch_application_traffic_material_slots_match_expected_model
          model0 /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficApplication
          label ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          label /\
        (traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          label == None \/
         (model1.model_handshake.hs_keys.ks_master_secret ==
          model0.model_handshake.hs_keys.ks_master_secret /\
          negotiated_aead_alg model1.model_handshake ==
            negotiated_aead_alg model0.model_handshake /\
          transcript_checkpoint_bytes TH_SF model1.model_handshake ==
          transcript_checkpoint_bytes TH_SF model0.model_handshake)))
      (ensures
        Some?
          (traffic_material_for_label
            model1.model_handshake.hs_keys
            TrafficApplication
            label) ==>
        (traffic_material_matches_expected_derived_material
           (traffic_id TrafficApplication label)
           (state_of_model_for_first_epoch_application_material model1) /\
         traffic_material_matches_expected_at_count
           (traffic_id TrafficApplication label)
           (state_of_model_for_first_epoch_application_material model1)
           0))
=
  if Some?
      (traffic_material_for_label
        model1.model_handshake.hs_keys
        TrafficApplication
        label)
  then begin
    assert
      (Some?
        (traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          label));
    match
      traffic_material_for_label
        model0.model_handshake.hs_keys
        TrafficApplication
        label
    with
    | None ->
      assert False
    | Some _ ->
      assert
        (model1.model_handshake.hs_keys.ks_master_secret ==
         model0.model_handshake.hs_keys.ks_master_secret);
      assert
        (negotiated_aead_alg model1.model_handshake ==
         negotiated_aead_alg model0.model_handshake);
      assert
        (transcript_checkpoint_bytes TH_SF model1.model_handshake ==
         transcript_checkpoint_bytes TH_SF model0.model_handshake);
      assert
        (traffic_material_matches_expected_at_count
          (traffic_id TrafficApplication label)
          (state_of_model_for_first_epoch_application_material model0)
          0);
      lemma_application_traffic_label_match_expected_preserved
        label
        model0
        model1
  end

let lemma_first_epoch_application_slots_preserved_when_slots_unchanged_or_checkpoint_stable
  (model0:connection_model)
  (model1:connection_model)
  : Lemma
      (requires
        first_epoch_application_traffic_material_slots_match_expected_model
          model0 /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficApplication
          ClientTraffic ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          ClientTraffic /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficApplication
          ServerTraffic ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          ServerTraffic /\
        (traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          ClientTraffic == None \/
         (model1.model_handshake.hs_keys.ks_master_secret ==
          model0.model_handshake.hs_keys.ks_master_secret /\
          negotiated_aead_alg model1.model_handshake ==
            negotiated_aead_alg model0.model_handshake /\
          transcript_checkpoint_bytes TH_SF model1.model_handshake ==
          transcript_checkpoint_bytes TH_SF model0.model_handshake)) /\
        (traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          ServerTraffic == None \/
         (model1.model_handshake.hs_keys.ks_master_secret ==
          model0.model_handshake.hs_keys.ks_master_secret /\
          negotiated_aead_alg model1.model_handshake ==
            negotiated_aead_alg model0.model_handshake /\
          transcript_checkpoint_bytes TH_SF model1.model_handshake ==
          transcript_checkpoint_bytes TH_SF model0.model_handshake)))
      (ensures
        first_epoch_application_traffic_material_slots_match_expected_model
          model1)
=
  lemma_first_epoch_application_label_match_expected_preserved_when_slot_unchanged_or_checkpoint_stable
    ClientTraffic
    model0
    model1;
  lemma_first_epoch_application_label_match_expected_preserved_when_slot_unchanged_or_checkpoint_stable
    ServerTraffic
    model0
    model1

let lemma_first_epoch_application_slots_preserved_when_application_labels_unchanged
  (model0:connection_model)
  (model1:connection_model)
  : Lemma
      (requires
        first_epoch_application_traffic_material_slots_match_expected_model
          model0 /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficApplication
          ClientTraffic ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          ClientTraffic /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficApplication
          ServerTraffic ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          ServerTraffic /\
        model1.model_handshake.hs_keys.ks_master_secret ==
        model0.model_handshake.hs_keys.ks_master_secret /\
        negotiated_aead_alg model1.model_handshake ==
          negotiated_aead_alg model0.model_handshake /\
        transcript_checkpoint_bytes TH_SF model1.model_handshake ==
        transcript_checkpoint_bytes TH_SF model0.model_handshake)
      (ensures
        first_epoch_application_traffic_material_slots_match_expected_model
          model1)
=
  lemma_first_epoch_application_label_match_expected_preserved
    ClientTraffic
    model0
    model1;
  lemma_first_epoch_application_label_match_expected_preserved
    ServerTraffic
    model0
    model1

// Model-Fix-1: the atomic Finished-delivery network steps now install an application
// traffic slot in a single step (deriving the secret inline from the transcript through
// the server Finished).  This lemma shows that such a freshly-installed slot matches the
// expected derived material, given that the material was derived from the TH_SF-checkpoint
// transcript `cp` using the model's master secret.
let lemma_atomic_application_install_matches_expected
  (label:traffic_label)
  (model1:connection_model)
  (cp:B.bytes)
  : Lemma
      (requires
        (match model1.model_handshake.hs_keys.ks_master_secret with
         | Some master ->
           transcript_checkpoint_bytes TH_SF model1.model_handshake == Some cp /\
           traffic_material_for_label
             model1.model_handshake.hs_keys
             TrafficApplication
             label ==
           Some
             (traffic_key_material_for_secret
               (negotiated_aead_alg model1.model_handshake)
               (derive_traffic_secret_for_label TrafficApplication label master cp))
         | None -> False))
      (ensures
        traffic_material_matches_expected_derived_material
          (traffic_id TrafficApplication label)
          (state_of_model_for_first_epoch_application_material model1))
=
  let st1 = state_of_model_for_first_epoch_application_material model1 in
  match model1.model_handshake.hs_keys.ks_master_secret with
  | Some master ->
    let secret = derive_traffic_secret_for_label TrafficApplication label master cp in
    assert (traffic_secret_base_for_epoch
              TrafficApplication
              model1.model_handshake.hs_keys == Some master);
    assert_norm (key_checkpoint_for_epoch TrafficApplication == DeriveApplicationTraffic);
    assert_norm (key_derivation_checkpoint_transcript DeriveApplicationTraffic == Some TH_SF);
    assert (transcript_bytes_for_key_checkpoint
              (key_checkpoint_for_epoch TrafficApplication)
              st1 == Some cp);
    assert (expected_traffic_secret_for_state
              (traffic_id TrafficApplication label)
              st1 == Some secret);
    let alg = negotiated_aead_alg model1.model_handshake in
    let material = traffic_key_material_for_secret alg secret in
    assert (material.traffic_key == K.derive_aead_key alg secret);
    assert (material.traffic_iv == K.derive_aead_iv secret);
    Seq.lemma_eq_refl material.traffic_key (K.derive_aead_key alg secret);
    Seq.lemma_eq_refl material.traffic_iv (K.derive_aead_iv secret)

(* Localized rlimit bump (10 -> 20) for this single lemma.  Two independent
   changes push it over the file default of 10:

   - enlarging the application-record-epoch reachable-shape axiom (the added
     `application_record_keys_installed_for_role` conjunct on the Closing/Closed
     arms) shifts the module SMT context and tips the final slots-match
     conjunction over;
   - strengthening the slot invariant with the stored-secret conjunct enlarges
     this lemma's hypothesis, moving two of its sub-queries from a used rlimit
     of ~9.5 to ~11.9 (measured with --query_stats).

   All sub-facts are already discharged as explicit intermediate assertions;
   the extra budget only funds the final definition unfold.  20 is a little
   under 2x the observed peak.  Scoped to this lemma so the surrounding block
   stays at 10. *)
#restart-solver
#push-options "--z3rlimit 20"
let lemma_step_model_preserves_first_epoch_application_traffic_material_slots_match_expected_model
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        first_epoch_application_traffic_material_replay_invariant_for_role
          role
          model0 /\
        legal_event model0 ev /\
        step_model model0 ev == Some model1 /\
        conn_event_is_key_update ev == false)
      (ensures
        first_epoch_application_traffic_material_slots_match_expected_model
          model1)
=
  let hs0 = model0.model_handshake in
  lemma_step_model_preserves_application_traffic_key_slot_stage_shape_for_role
    role
    model0
    ev
    model1;
  lemma_step_model_preserves_application_traffic_install_checkpoint_ready_for_role
    role
    model0
    ev
    model1;
  match ev with
  | ConnLocalEvent local ->
    (match local, model0.model_control with
     | LocalInstallTrafficKeys install, ControlHandshaking stage ->
       assert (role == ClientEndpoint);
       assert (traffic_install_allowed_at_stage stage install);
       assert (traffic_install_allowed_at_stage_for_role
         ClientEndpoint
         stage
         install);
       lemma_expected_traffic_secret_client_projection
         hs0
         install.install_epoch
         install.install_direction;
       assert
         (traffic_install_matches_key_schedule_for_role
           ClientEndpoint
           hs0
           install);
       assert (model1.model_handshake ==
         { hs0 with
             hs_keys =
               update_key_schedule_with_install
                 hs0.hs_keys
                 install });
       lemma_update_key_schedule_with_install_client_projection
         hs0.hs_keys
         install;
       assert (model1.model_handshake ==
         { hs0 with
             hs_keys =
               update_key_schedule_with_install_for_role
                 ClientEndpoint
                 hs0.hs_keys
                 install });
       (match install.install_epoch with
        | TrafficApplication ->
          lemma_application_traffic_install_for_role_material_matches_expected
            ClientEndpoint
            model0
            stage
            install
            model1;
          (match install.install_direction with
           | TrafficWrite ->
             assert_norm
               (traffic_label_for_endpoint_direction
                 ClientEndpoint
                 TrafficWrite == ClientTraffic);
             lemma_first_epoch_application_label_match_expected_preserved
               ServerTraffic
               model0
               model1
           | TrafficRead ->
             assert_norm
               (traffic_label_for_endpoint_direction
                 ClientEndpoint
                 TrafficRead == ServerTraffic);
             lemma_first_epoch_application_label_match_expected_preserved
               ClientTraffic
               model0
               model1);
          assert (first_epoch_application_traffic_material_slots_match_expected_model
            model1)
        | TrafficHandshake ->
          lemma_first_epoch_application_slots_preserved_when_application_labels_unchanged
            model0
            model1)
     | LocalInstallTrafficKeysForRole role_install, ControlHandshaking stage ->
       let install = role_install.install_payload in
       assert (role_install.install_role == role);
       assert (model1.model_handshake ==
         { hs0 with
             hs_keys =
               update_key_schedule_with_install_for_role
                 role_install.install_role
                 hs0.hs_keys
                 install });
       assert (model1.model_handshake ==
         { hs0 with
             hs_keys =
               update_key_schedule_with_install_for_role
                 role
                 hs0.hs_keys
                 install });
       (match install.install_epoch with
        | TrafficApplication ->
          lemma_application_traffic_install_for_role_material_matches_expected
            role
            model0
            stage
            install
            model1;
          (match role, install.install_direction with
           | ClientEndpoint, TrafficWrite ->
             assert_norm
               (traffic_label_for_endpoint_direction
                 ClientEndpoint
                 TrafficWrite == ClientTraffic);
             lemma_first_epoch_application_label_match_expected_preserved
               ServerTraffic
               model0
               model1
           | ClientEndpoint, TrafficRead ->
             assert_norm
               (traffic_label_for_endpoint_direction
                 ClientEndpoint
                 TrafficRead == ServerTraffic);
             lemma_first_epoch_application_label_match_expected_preserved
               ClientTraffic
               model0
               model1
           | ServerEndpoint, TrafficWrite ->
             assert_norm
               (traffic_label_for_endpoint_direction
                 ServerEndpoint
                 TrafficWrite == ServerTraffic);
             lemma_first_epoch_application_label_match_expected_preserved
               ClientTraffic
               model0
               model1
           | ServerEndpoint, TrafficRead ->
             assert_norm
               (traffic_label_for_endpoint_direction
                 ServerEndpoint
                 TrafficRead == ClientTraffic);
             lemma_first_epoch_application_label_match_expected_preserved
               ServerTraffic
               model0
               model1);
          assert (first_epoch_application_traffic_material_slots_match_expected_model
            model1)
        | TrafficHandshake ->
          lemma_first_epoch_application_slots_preserved_when_application_labels_unchanged
            model0
            model1)
     | _, _ ->
       lemma_first_epoch_application_slots_preserved_when_slots_unchanged_or_checkpoint_stable
         model0
         model1)
  | ConnProtectedHandshake step ->
    if step.protected_handshake_buffering
    then
      (* Buffering rewrites only [model_record] and the handshake buffers,
         which no traffic-material slot or checkpoint predicate reads. *)
      lemma_first_epoch_application_slots_preserved_when_slots_unchanged_or_checkpoint_stable
        model0
        model1
    else
    (match step.protected_handshake_message, model0.model_control with
     | M.Finished _, ControlHandshaking HsCertificateVerifyVerified ->
       assert (role == ClientEndpoint);
       assert (application_traffic_install_checkpoint_ready_for_role role model1);
       assert (model1.model_control == ControlHandshaking HsServerFinishedVerified);
       assert (transcript_checkpoint_bytes TH_SF model1.model_handshake ==
               Some model1.model_handshake.hs_transcript);
       assert (model1.model_handshake.hs_keys.ks_client_application_traffic == None);
       lemma_atomic_application_install_matches_expected
         ServerTraffic
         model1
         model1.model_handshake.hs_transcript;
       assert (first_epoch_application_traffic_material_slots_match_expected_model
         model1)
     | M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived
     | M.Certificate _, ControlHandshaking HsEncryptedExtensionsReceived
     | M.CertificateVerify _, ControlHandshaking HsCertificateValidated ->
       lemma_first_epoch_application_slots_preserved_when_slots_unchanged_or_checkpoint_stable
         model0
         model1
     | _, _ ->
       assert False)
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value, msg.CL.message_direction, model0.model_control with
     | M.TlsKeyUpdate _, _, _ ->
       assert False
     | M.TlsHandshake (M.Finished _), CL.Received,
       ControlHandshaking HsCertificateVerifyVerified ->
       // Model-Fix-1 (client atomic delivery): installs ks_server_application_traffic
       // (deriving from the transcript through the server Finished) and lands at
       // HsServerFinishedVerified.  ks_client_application_traffic stays None (vacuous).
       assert (role == ClientEndpoint);
       assert (application_traffic_install_checkpoint_ready_for_role role model1);
       assert (model1.model_control == ControlHandshaking HsServerFinishedVerified);
       assert (transcript_checkpoint_bytes TH_SF model1.model_handshake ==
               Some model1.model_handshake.hs_transcript);
       assert (model1.model_handshake.hs_keys.ks_client_application_traffic == None);
       lemma_atomic_application_install_matches_expected
         ServerTraffic
         model1
         model1.model_handshake.hs_transcript;
       assert (first_epoch_application_traffic_material_slots_match_expected_model
         model1)
     | M.TlsHandshake (M.Finished _), CL.Received,
       ControlHandshaking HsServerFinishedSent ->
       // Model-Fix-1 (server atomic delivery): installs ks_client_application_traffic
       // (deriving from the CURRENT transcript, through the server Finished, before
       // appending the client Finished) and lands at ControlApplicationData.
       // ks_server_application_traffic is unchanged; the TH_SF checkpoint only reads the
       // handshake slots up to the server Finished and is unchanged by the client-Finished
       // append.
       assert (role == ServerEndpoint);
       assert (model1.model_control == ControlApplicationData);
       assert (application_traffic_install_checkpoint_ready_for_role role model0);
       assert (transcript_checkpoint_bytes TH_SF model0.model_handshake ==
               Some model0.model_handshake.hs_transcript);
       assert (model1.model_handshake.hs_client_hello == model0.model_handshake.hs_client_hello);
       assert (model1.model_handshake.hs_server_hello == model0.model_handshake.hs_server_hello);
       assert (model1.model_handshake.hs_encrypted_extensions ==
               model0.model_handshake.hs_encrypted_extensions);
       assert (model1.model_handshake.hs_certificate == model0.model_handshake.hs_certificate);
       assert (model1.model_handshake.hs_certificate_verify ==
               model0.model_handshake.hs_certificate_verify);
       assert (model1.model_handshake.hs_server_finished ==
               model0.model_handshake.hs_server_finished);
       assert (transcript_checkpoint_bytes TH_SF model1.model_handshake ==
               transcript_checkpoint_bytes TH_SF model0.model_handshake);
       assert (transcript_checkpoint_bytes TH_SF model1.model_handshake ==
               Some model0.model_handshake.hs_transcript);
       // ServerTraffic slot unchanged and its expected material is stable across the
       // client-Finished append (master + TH_SF checkpoint unchanged).
       assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
               model0.model_handshake.hs_keys.ks_server_application_traffic);
       assert (model1.model_handshake.hs_keys.ks_master_secret ==
               model0.model_handshake.hs_keys.ks_master_secret);
       lemma_first_epoch_application_label_match_expected_preserved
         ServerTraffic
         model0
         model1;
       // ClientTraffic slot freshly installed: matches the expected derived material.
       lemma_atomic_application_install_matches_expected
         ClientTraffic
         model1
         model0.model_handshake.hs_transcript;
       // Bridge the two per-slot facts explicitly to the goal.  (Restated over the
       // same [state_of_model_for_first_epoch_application_material model1] so the
       // final conjunction is a trivial AND of two in-context facts — keeps this
       // rlimit-10 query robust against SMT-context shifts elsewhere in the module.)
       let st1 = state_of_model_for_first_epoch_application_material model1 in
       // [traffic_material_for_label _ TrafficApplication ServerTraffic] reduces to
       // [ks_server_application_traffic]; state the equality so the preserved-lemma
       // ensures transports onto the goal's guard without relying on Z3 unfolding.
       assert_norm (traffic_material_for_label
                      model1.model_handshake.hs_keys
                      TrafficApplication
                      ServerTraffic ==
                    model1.model_handshake.hs_keys.ks_server_application_traffic);
       assert (traffic_material_matches_expected_derived_material
                 (traffic_id TrafficApplication ClientTraffic) st1);
       assert (Some? model1.model_handshake.hs_keys.ks_server_application_traffic ==>
               traffic_material_matches_expected_derived_material
                 (traffic_id TrafficApplication ServerTraffic) st1);
       assert (st1.cs_model.model_handshake.hs_keys.ks_client_application_traffic ==
               model1.model_handshake.hs_keys.ks_client_application_traffic);
       assert (st1.cs_model.model_handshake.hs_keys.ks_server_application_traffic ==
               model1.model_handshake.hs_keys.ks_server_application_traffic);
       assert (first_epoch_application_traffic_material_slots_match_expected_model
         model1)
     | _, _, _ ->
       lemma_first_epoch_application_slots_preserved_when_slots_unchanged_or_checkpoint_stable
         model0
         model1)
#pop-options

#pop-options
let lemma_step_model_preserves_first_epoch_application_traffic_material_replay_invariant_for_role
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        first_epoch_application_traffic_material_replay_invariant_for_role
          role
          model0 /\
        legal_event model0 ev /\
        step_model model0 ev == Some model1 /\
        conn_event_is_key_update ev == false)
      (ensures
        first_epoch_application_traffic_material_replay_invariant_for_role
          role
          model1)
=
  lemma_step_model_preserves_config model0 ev model1;
  lemma_step_model_supported_profile_key_schedule_reachable_shape
    model0
    ev
    model1;
  lemma_step_model_application_record_epoch_reachable_shape_for_role
    role
    model0
    ev
    model1;
  lemma_step_model_preserves_application_traffic_key_slot_stage_shape_for_role
    role
    model0
    ev
    model1;
  lemma_step_model_preserves_application_traffic_install_checkpoint_ready_for_role
    role
    model0
    ev
    model1;
  lemma_step_model_preserves_first_epoch_application_traffic_material_slots_match_expected_model
    role
    model0
    ev
    model1

let rec lemma_conn_events_raw_replay_no_key_update_first_epoch_application_traffic_material_replay_invariant_for_role
  (role:endpoint_role)
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        first_epoch_application_traffic_material_replay_invariant_for_role
          role
          model /\
        conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model /\
        conn_events_no_key_update events == true)
      (ensures
        first_epoch_application_traffic_material_replay_invariant_for_role
          role
          final_model)
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    assert (conn_event_is_key_update ev == false);
    assert (conn_events_no_key_update rest == true);
    lemma_raw_replay_cons_unfold model ev rest raw_sent raw_received final_model;
    eliminate exists
      (model1:connection_model)
      (delta_sent:B.bytes)
      (delta_received:B.bytes)
      (tail_sent:B.bytes)
      (tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_raw_replay model1 rest tail_sent tail_received final_model
    with
    ( lemma_step_model_preserves_first_epoch_application_traffic_material_replay_invariant_for_role
        role
        model
        ev
        model1;
      lemma_conn_events_raw_replay_no_key_update_first_epoch_application_traffic_material_replay_invariant_for_role
        role
        model1
        rest
        tail_sent
        tail_received
        final_model )

let lemma_connection_state_no_key_update_trace_first_epoch_application_traffic_material_slots_match_expected
  (st:connection_state)
  : Lemma
      (requires
        connection_state_raw_event_replay_consistent st /\
        connection_state_no_key_update_trace st)
      (ensures
        first_epoch_application_traffic_material_slots_match_expected st)
=
  let role = st.cs_model.model_config.config_role in
  let cfg = st.cs_model.model_config in
  lemma_initial_first_epoch_application_traffic_material_replay_invariant_for_role
    role
    cfg;
  lemma_conn_events_raw_replay_no_key_update_first_epoch_application_traffic_material_replay_invariant_for_role
    role
    (initial_model cfg)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model;
  assert
    (first_epoch_application_traffic_material_slots_match_expected_model
      st.cs_model);
  let st_model = state_of_model_for_first_epoch_application_material st.cs_model in
  assert
    (first_epoch_application_traffic_material_slots_match_expected st_model);
  (* Transfer the epoch-0 slot facts from the model-only state to `st`.  Both
     carry the same `cs_model`, and both `traffic_material_for_label` and
     `expected_traffic_secret_for_state` read nothing but the model, so the
     transfer lemma's hypotheses hold definitionally.  Discharging them by hand
     keeps the epoch-count conjuncts out of the ambient SMT search, which no
     longer closes them at the module's default rlimit. *)
  if Some? st.cs_model.model_handshake.hs_keys.ks_client_application_traffic
  then
    lemma_traffic_material_matches_expected_at_count_transfer
      (traffic_id TrafficApplication ClientTraffic)
      st_model
      st
      0;
  if Some? st.cs_model.model_handshake.hs_keys.ks_server_application_traffic
  then
    lemma_traffic_material_matches_expected_at_count_transfer
      (traffic_id TrafficApplication ServerTraffic)
      st_model
      st
      0;
  assert
    (first_epoch_application_traffic_material_slots_match_expected st)

#pop-options

(**
  ──────────────────────────────────────────────────────────────────────────
  Epoch-indexed application traffic material
  ──────────────────────────────────────────────────────────────────────────

  `first_epoch_application_traffic_material_replay_invariant_for_role` pins the
  application traffic material at *epoch 0*, and is therefore only replayable
  along a trace that contains no KeyUpdate.  RFC 8446 §7.2 lets either endpoint
  rotate an application traffic secret at any time once the handshake is
  complete, so that invariant cannot be the one a rekeying-aware system theorem
  carries.

  What follows lifts it to an epoch-indexed invariant that survives KeyUpdates:
  instead of excluding rotations it *counts* them, relating the stored material
  to the `n`-fold `application_traffic_secret_update` iterate of the epoch-0
  secret, with `n` read off the event log by `key_update_count_for_label`.

  The invariant is a disjunction of two phases.  That is what makes it
  inductive without re-doing the (large) epoch-0 step analysis:

    * **Phase 1** — no rotation has happened yet, both counters are zero, and
      the epoch-0 invariant holds verbatim.  Traffic-key *installation* happens
      only here, because every installing transition requires
      `ControlHandshaking`.  The step rule for this phase is the existing
      epoch-0 step lemma, used unchanged.
    * **Phase 2** — rotations may have happened, so control has left the
      handshake for good.  No transition out of a post-handshake control state
      installs traffic keys, so the only thing that can move an application
      slot is a KeyUpdate, and rotation is discharged by
      `lemma_traffic_material_matches_expected_at_count_rotate`.

  A KeyUpdate moves phase 1 to phase 2 — it is legal only at
  `ControlApplicationData` — and nothing moves phase 2 back.
 **)

let post_handshake_control (c:connection_control_state) : bool =
  match c with
  | ControlNew -> false
  | ControlHandshaking _ -> false
  | ControlApplicationData -> true
  | ControlClosing -> true
  | ControlClosed -> true
  | ControlFailed _ -> true

let other_traffic_label (label:traffic_label) : traffic_label =
  match label with
  | ClientTraffic -> ServerTraffic
  | ServerTraffic -> ClientTraffic

(** The epoch-0 application traffic secret is determined by the master secret
    and the TH_SF transcript checkpoint, so a step preserving both leaves every
    application epoch-0 secret alone. **)
let lemma_expected_application_traffic_secret_stable
  (label:traffic_label)
  (model0:connection_model)
  (model1:connection_model)
  : Lemma
      (requires
        model1.model_handshake.hs_keys.ks_master_secret ==
        model0.model_handshake.hs_keys.ks_master_secret /\
        negotiated_aead_alg model1.model_handshake ==
          negotiated_aead_alg model0.model_handshake /\
        transcript_checkpoint_bytes TH_SF model1.model_handshake ==
        transcript_checkpoint_bytes TH_SF model0.model_handshake)
      (ensures
        expected_traffic_secret_for_state
          (traffic_id TrafficApplication label)
          (state_of_model_for_first_epoch_application_material model1) ==
        expected_traffic_secret_for_state
          (traffic_id TrafficApplication label)
          (state_of_model_for_first_epoch_application_material model0))
=
  assert_norm (key_checkpoint_for_epoch TrafficApplication == DeriveApplicationTraffic);
  assert_norm (key_derivation_checkpoint_transcript DeriveApplicationTraffic == Some TH_SF)

(** No transition out of a post-handshake control state installs traffic keys
    or extends the handshake transcript, so the only application slot movement
    available there is a KeyUpdate rotation — which this lemma excludes. **)
let lemma_step_model_post_handshake_application_slots_stable
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        post_handshake_control model0.model_control == true /\
        legal_event model0 ev /\
        step_model model0 ev == Some model1 /\
        conn_event_key_update_label model0.model_config.config_role ev == None)
      (ensures
        post_handshake_control model1.model_control == true /\
        model1.model_handshake.hs_keys.ks_client_application_traffic ==
        model0.model_handshake.hs_keys.ks_client_application_traffic /\
        model1.model_handshake.hs_keys.ks_server_application_traffic ==
        model0.model_handshake.hs_keys.ks_server_application_traffic /\
        model1.model_handshake.hs_keys.ks_master_secret ==
        model0.model_handshake.hs_keys.ks_master_secret /\
        negotiated_aead_alg model1.model_handshake ==
          negotiated_aead_alg model0.model_handshake /\
        transcript_checkpoint_bytes TH_SF model1.model_handshake ==
        transcript_checkpoint_bytes TH_SF model0.model_handshake)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnProtectedHandshake _ -> ()
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsKeyUpdate _ -> assert False
     | _ -> ())

(** `conn_event_key_update_label` refines `conn_event_is_key_update`: the label
    is `Some` exactly on the events the flag calls KeyUpdates. **)
let lemma_conn_event_key_update_label_none
  (role:endpoint_role)
  (ev:conn_event)
  : Lemma
      (requires conn_event_key_update_label role ev == None)
      (ensures conn_event_is_key_update ev == false)
=
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsKeyUpdate _ ->
       (match msg.CL.message_direction with
        | CL.Sent ->
          (match traffic_label_for_endpoint_direction role TrafficWrite with
           | ClientTraffic -> ()
           | ServerTraffic -> ())
        | CL.Received ->
          (match traffic_label_for_endpoint_direction role TrafficRead with
           | ClientTraffic -> ()
           | ServerTraffic -> ()))
     | _ -> ())
  | _ -> ()

(** A KeyUpdate rotates exactly the slot its label names, leaves the other slot
    and both epoch-0 secrets alone, and fires only at `ControlApplicationData`. **)
let lemma_step_model_key_update_rotates_labeled_slot
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  (label:traffic_label)
  : Lemma
      (requires
        model0.model_config.config_role == role /\
        step_model model0 ev == Some model1 /\
        conn_event_key_update_label role ev == Some label)
      (ensures
        model0.model_control == ControlApplicationData /\
        model1.model_control == ControlApplicationData /\
        model1.model_handshake.hs_keys.ks_master_secret ==
        model0.model_handshake.hs_keys.ks_master_secret /\
        transcript_checkpoint_bytes TH_SF model1.model_handshake ==
        transcript_checkpoint_bytes TH_SF model0.model_handshake /\
        (match
           traffic_material_for_label
             model0.model_handshake.hs_keys TrafficApplication label,
           traffic_material_for_label
             model1.model_handshake.hs_keys TrafficApplication label
         with
         | Some m0, Some m1 -> m1 == updated_traffic_key_material m0
         | _, _ -> False) /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficApplication
          (other_traffic_label label) ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          (other_traffic_label label))
=
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsKeyUpdate _ ->
       let tdir =
         match msg.CL.message_direction with
         | CL.Sent -> TrafficWrite
         | CL.Received -> TrafficRead in
       assert (traffic_label_for_endpoint_direction role tdir == label);
       (match rotate_application_traffic model0 tdir with
        | Some rotated ->
          assert (model1.model_handshake == rotated.model_handshake);
          (match label with
           | ClientTraffic -> ()
           | ServerTraffic -> ())
        | None -> assert False)
     | _ -> assert False)
  | _ -> assert False

(** The epoch bookkeeping of a single KeyUpdate step, stated label-generically:
    the named slot advances one epoch, the other slot stands still. **)
let lemma_key_update_step_slots_at_counts
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  (label:traffic_label)
  (n_label:nat)
  (n_other:nat)
  : Lemma
      (requires
        model0.model_config.config_role == role /\
        step_model model0 ev == Some model1 /\
        conn_event_key_update_label role ev == Some label /\
        traffic_material_matches_expected_at_count
          (traffic_id TrafficApplication label)
          (state_of_model_for_first_epoch_application_material model0)
          n_label /\
        (Some?
          (traffic_material_for_label
            model0.model_handshake.hs_keys
            TrafficApplication
            (other_traffic_label label)) ==>
         traffic_material_matches_expected_at_count
           (traffic_id TrafficApplication (other_traffic_label label))
           (state_of_model_for_first_epoch_application_material model0)
           n_other))
      (ensures
        model1.model_control == ControlApplicationData /\
        Some?
          (traffic_material_for_label
            model1.model_handshake.hs_keys TrafficApplication label) /\
        traffic_material_matches_expected_at_count
          (traffic_id TrafficApplication label)
          (state_of_model_for_first_epoch_application_material model1)
          (n_label + 1) /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficApplication
          (other_traffic_label label) ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficApplication
          (other_traffic_label label) /\
        (Some?
          (traffic_material_for_label
            model1.model_handshake.hs_keys
            TrafficApplication
            (other_traffic_label label)) ==>
         traffic_material_matches_expected_at_count
           (traffic_id TrafficApplication (other_traffic_label label))
           (state_of_model_for_first_epoch_application_material model1)
           n_other))
=
  let st0 = state_of_model_for_first_epoch_application_material model0 in
  let st1 = state_of_model_for_first_epoch_application_material model1 in
  let other = other_traffic_label label in
  lemma_step_model_key_update_rotates_labeled_slot role model0 ev model1 label;
  lemma_expected_application_traffic_secret_stable label model0 model1;
  lemma_expected_application_traffic_secret_stable other model0 model1;
  lemma_traffic_material_matches_expected_at_count_rotate
    (traffic_id TrafficApplication label) st0 st1 n_label;
  if Some?
       (traffic_material_for_label
         model0.model_handshake.hs_keys TrafficApplication other)
  then
    lemma_traffic_material_matches_expected_at_count_transfer
      (traffic_id TrafficApplication other) st0 st1 n_other
  else ()

let application_traffic_material_shape_inv_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  model.model_config.config_role == role /\
  model_supported_profile_key_schedule_reachable_shape model /\
  model_application_record_epoch_reachable_shape_for_role role model /\
  application_traffic_key_slot_stage_shape_for_role role model /\
  application_traffic_install_checkpoint_ready_for_role role model

let application_traffic_material_epoch_phase_two
  (model:connection_model)
  (nc:nat)
  (ns:nat)
  : prop =
  post_handshake_control model.model_control == true /\
  (model.model_handshake.hs_keys.ks_client_application_traffic == None ==> nc == 0) /\
  (model.model_handshake.hs_keys.ks_server_application_traffic == None ==> ns == 0) /\
  application_traffic_material_slots_match_expected_at_counts
    (state_of_model_for_first_epoch_application_material model)
    nc
    ns

let application_traffic_material_replay_invariant_at_counts_for_role
  (role:endpoint_role)
  (model:connection_model)
  (nc:nat)
  (ns:nat)
  : prop =
  application_traffic_material_shape_inv_for_role role model /\
  ((nc == 0 /\
    ns == 0 /\
    first_epoch_application_traffic_material_slots_match_expected_model model) \/
   application_traffic_material_epoch_phase_two model nc ns)

let key_update_delta_for_label
  (role:endpoint_role)
  (ev:conn_event)
  (label:traffic_label)
  : nat =
  if conn_event_key_update_label role ev = Some label then 1 else 0

let lemma_step_shape_inv_at_counts_for_role
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        application_traffic_material_shape_inv_for_role role model0 /\
        legal_event model0 ev /\
        step_model model0 ev == Some model1)
      (ensures application_traffic_material_shape_inv_for_role role model1)
=
  lemma_step_model_preserves_config model0 ev model1;
  lemma_step_model_supported_profile_key_schedule_reachable_shape model0 ev model1;
  lemma_step_model_application_record_epoch_reachable_shape_for_role role model0 ev model1;
  lemma_step_model_preserves_application_traffic_key_slot_stage_shape_for_role
    role model0 ev model1;
  lemma_step_model_preserves_application_traffic_install_checkpoint_ready_for_role
    role model0 ev model1

#restart-solver
#push-options "--z3rlimit 30"
(** Phase 1 step: either the event is not a KeyUpdate, in which case the
    existing epoch-0 step lemma applies verbatim and we stay in phase 1; or it
    is, in which case we promote to phase 2 with the rotated label at epoch 1. **)
let lemma_step_model_preserves_epoch_phase_one
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        application_traffic_material_shape_inv_for_role role model0 /\
        first_epoch_application_traffic_material_slots_match_expected_model model0 /\
        legal_event model0 ev /\
        step_model model0 ev == Some model1)
      (ensures
        application_traffic_material_replay_invariant_at_counts_for_role
          role
          model1
          (key_update_delta_for_label role ev ClientTraffic)
          (key_update_delta_for_label role ev ServerTraffic))
=
  lemma_step_shape_inv_at_counts_for_role role model0 ev model1;
  match conn_event_key_update_label role ev with
  | None ->
    lemma_conn_event_key_update_label_none role ev;
    lemma_step_model_preserves_first_epoch_application_traffic_material_slots_match_expected_model
      role model0 ev model1
  | Some ClientTraffic ->
    lemma_key_update_step_slots_at_counts role model0 ev model1 ClientTraffic 0 0;
    assert (key_update_delta_for_label role ev ClientTraffic == 1);
    assert (key_update_delta_for_label role ev ServerTraffic == 0);
    assert (application_traffic_material_epoch_phase_two model1 1 0)
  | Some ServerTraffic ->
    lemma_key_update_step_slots_at_counts role model0 ev model1 ServerTraffic 0 0;
    assert (key_update_delta_for_label role ev ServerTraffic == 1);
    assert (key_update_delta_for_label role ev ClientTraffic == 0);
    assert (application_traffic_material_epoch_phase_two model1 0 1)

(** Phase 2 step: control has left the handshake, so a non-KeyUpdate event
    cannot touch an application slot and a KeyUpdate advances exactly one. **)
let lemma_step_model_preserves_epoch_phase_two
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  (nc:nat)
  (ns:nat)
  : Lemma
      (requires
        application_traffic_material_shape_inv_for_role role model0 /\
        application_traffic_material_epoch_phase_two model0 nc ns /\
        legal_event model0 ev /\
        step_model model0 ev == Some model1)
      (ensures
        application_traffic_material_replay_invariant_at_counts_for_role
          role
          model1
          (nc + key_update_delta_for_label role ev ClientTraffic)
          (ns + key_update_delta_for_label role ev ServerTraffic))
=
  lemma_step_shape_inv_at_counts_for_role role model0 ev model1;
  let st0 = state_of_model_for_first_epoch_application_material model0 in
  let st1 = state_of_model_for_first_epoch_application_material model1 in
  match conn_event_key_update_label role ev with
  | None ->
    assert (key_update_delta_for_label role ev ClientTraffic == 0);
    assert (key_update_delta_for_label role ev ServerTraffic == 0);
    lemma_step_model_post_handshake_application_slots_stable model0 ev model1;
    lemma_expected_application_traffic_secret_stable ClientTraffic model0 model1;
    lemma_expected_application_traffic_secret_stable ServerTraffic model0 model1;
    (if Some? model0.model_handshake.hs_keys.ks_client_application_traffic
     then
       lemma_traffic_material_matches_expected_at_count_transfer
         (traffic_id TrafficApplication ClientTraffic) st0 st1 nc
     else ());
    (if Some? model0.model_handshake.hs_keys.ks_server_application_traffic
     then
       lemma_traffic_material_matches_expected_at_count_transfer
         (traffic_id TrafficApplication ServerTraffic) st0 st1 ns
     else ());
    assert (application_traffic_material_epoch_phase_two model1 nc ns)
  | Some ClientTraffic ->
    lemma_key_update_step_slots_at_counts role model0 ev model1 ClientTraffic nc ns;
    assert (key_update_delta_for_label role ev ClientTraffic == 1);
    assert (key_update_delta_for_label role ev ServerTraffic == 0);
    assert (application_traffic_material_epoch_phase_two model1 (nc + 1) ns)
  | Some ServerTraffic ->
    lemma_key_update_step_slots_at_counts role model0 ev model1 ServerTraffic ns nc;
    assert (key_update_delta_for_label role ev ServerTraffic == 1);
    assert (key_update_delta_for_label role ev ClientTraffic == 0);
    assert (application_traffic_material_epoch_phase_two model1 nc (ns + 1))
#pop-options

let lemma_step_model_preserves_application_traffic_material_replay_invariant_at_counts_for_role
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  (nc:nat)
  (ns:nat)
  : Lemma
      (requires
        application_traffic_material_replay_invariant_at_counts_for_role
          role model0 nc ns /\
        legal_event model0 ev /\
        step_model model0 ev == Some model1)
      (ensures
        application_traffic_material_replay_invariant_at_counts_for_role
          role
          model1
          (nc + key_update_delta_for_label role ev ClientTraffic)
          (ns + key_update_delta_for_label role ev ServerTraffic))
=
  eliminate
    (nc == 0 /\
     ns == 0 /\
     first_epoch_application_traffic_material_slots_match_expected_model model0)
    \/ application_traffic_material_epoch_phase_two model0 nc ns
  with
    lemma_step_model_preserves_epoch_phase_one role model0 ev model1
  and
    lemma_step_model_preserves_epoch_phase_two role model0 ev model1 nc ns

#push-options "--fuel 1 --ifuel 1"
let lemma_key_update_count_for_label_cons
  (role:endpoint_role)
  (ev:conn_event)
  (rest:list conn_event)
  (l:traffic_label)
  : Lemma
      (key_update_count_for_label role (ev :: rest) l ==
       key_update_delta_for_label role ev l +
       key_update_count_for_label role rest l)
= ()
#pop-options

#push-options "--z3rlimit 100"
let rec lemma_conn_events_raw_replay_application_traffic_material_at_counts_for_role
  (role:endpoint_role)
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (nc:nat)
  (ns:nat)
  : Lemma
      (requires
        application_traffic_material_replay_invariant_at_counts_for_role
          role model nc ns /\
        conn_events_raw_replay model events raw_sent raw_received final_model)
      (ensures
        application_traffic_material_replay_invariant_at_counts_for_role
          role
          final_model
          (nc + key_update_count_for_label role events ClientTraffic)
          (ns + key_update_count_for_label role events ServerTraffic))
      (decreases events)
=
  match events with
  | [] ->
    assert (final_model == model)
  | ev :: rest ->
    lemma_key_update_count_for_label_cons role ev rest ClientTraffic;
    lemma_key_update_count_for_label_cons role ev rest ServerTraffic;
    // `eliminate exists` desugars through `indefinite_description5`, whose
    // precondition is the existential itself.  Supply it as a folded unfolding
    // equation rather than making Z3 re-derive it from the recursive definition.
    lemma_raw_replay_cons_unfold model ev rest raw_sent raw_received final_model;
    eliminate exists
      (model1:connection_model)
      (delta_sent:B.bytes)
      (delta_received:B.bytes)
      (tail_sent:B.bytes)
      (tail_received:B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received) /\
      conn_events_raw_replay model1 rest tail_sent tail_received final_model
    with
    ( lemma_step_model_preserves_application_traffic_material_replay_invariant_at_counts_for_role
        role model ev model1 nc ns;
      lemma_conn_events_raw_replay_application_traffic_material_at_counts_for_role
        role
        model1
        rest
        tail_sent
        tail_received
        final_model
        (nc + key_update_delta_for_label role ev ClientTraffic)
        (ns + key_update_delta_for_label role ev ServerTraffic) )

#pop-options
let lemma_initial_application_traffic_material_at_counts_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma
      (requires cfg.config_role == role)
      (ensures
        application_traffic_material_replay_invariant_at_counts_for_role
          role
          (initial_model cfg)
          0
          0)
=
  lemma_initial_first_epoch_application_traffic_material_replay_invariant_for_role role cfg

(**
  The epoch-indexed replacement for
  `lemma_connection_state_no_key_update_trace_first_epoch_application_traffic_material_slots_match_expected`.
  Note the absence of any `connection_state_no_key_update_trace` hypothesis:
  replay consistency alone determines the live application traffic material, at
  the state's own epoch.
 **)
#push-options "--z3rlimit 30"
let lemma_connection_state_application_traffic_material_slots_match_expected_at_epoch
  (st:connection_state)
  : Lemma
      (requires connection_state_raw_event_replay_consistent st)
      (ensures application_traffic_material_slots_match_expected_at_epoch st)
=
  let role = st.cs_model.model_config.config_role in
  let cfg = st.cs_model.model_config in
  lemma_initial_application_traffic_material_at_counts_for_role role cfg;
  lemma_conn_events_raw_replay_application_traffic_material_at_counts_for_role
    role
    (initial_model cfg)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model
    0
    0;
  let nc = connection_state_key_update_count st ClientTraffic in
  let ns = connection_state_key_update_count st ServerTraffic in
  assert (nc == key_update_count_for_label role st.cs_event_log ClientTraffic);
  assert (ns == key_update_count_for_label role st.cs_event_log ServerTraffic);
  assert
    (application_traffic_material_replay_invariant_at_counts_for_role
      role st.cs_model nc ns);
  assert
    (application_traffic_material_slots_match_expected_at_counts
      (state_of_model_for_first_epoch_application_material st.cs_model) nc ns);
  assert_norm (key_checkpoint_for_epoch TrafficApplication == DeriveApplicationTraffic);
  assert_norm (key_derivation_checkpoint_transcript DeriveApplicationTraffic == Some TH_SF);
  assert
    (expected_traffic_secret_for_state (traffic_id TrafficApplication ClientTraffic) st ==
     expected_traffic_secret_for_state
       (traffic_id TrafficApplication ClientTraffic)
       (state_of_model_for_first_epoch_application_material st.cs_model));
  assert
    (expected_traffic_secret_for_state (traffic_id TrafficApplication ServerTraffic) st ==
     expected_traffic_secret_for_state
       (traffic_id TrafficApplication ServerTraffic)
       (state_of_model_for_first_epoch_application_material st.cs_model));
  assert (application_traffic_material_slots_match_expected_at_counts st nc ns)
#pop-options

(**
  The epoch-indexed replacement for
  `lemma_no_key_update_application_traffic_material_matches_expected`.  At
  `ControlApplicationData` with both application record epochs installed, both
  slots are populated, so the epoch-indexed slot invariant pins each of them to
  the material of its own epoch — with no "no rekeying" hypothesis anywhere.
 **)
let lemma_application_traffic_material_matches_expected_at_epoch
  (role:endpoint_role)
  (st:connection_state)
  : Lemma
      (requires
        connection_state_raw_event_replay_consistent st /\
        st.cs_model.model_config.config_role == role /\
        st.cs_model.model_control == ControlApplicationData /\
        application_record_keys_installed_for_role role st.cs_model)
      (ensures
        supported_profile_application_traffic_material_matches_expected_at_epoch st)
=
  lemma_connection_state_application_traffic_material_slots_match_expected_at_epoch st;
  match role with
  | ClientEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_server_application_traffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_client_application_traffic)
  | ServerEndpoint ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_client_application_traffic);
    assert (Some? st.cs_model.model_handshake.hs_keys.ks_server_application_traffic)


let server_certificate_verify_body_empty_reachable_shape
  (st:connection_state)
  : prop =
  st.cs_model.model_config.config_role == ServerEndpoint ==>
  (match st.cs_model.model_handshake.hs_certificate_verify with
   | Some _ -> True
   | None -> True)

let lemma_step_model_server_certificate_verify_body_empty_reachable_shape
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires
        server_certificate_verify_body_empty_reachable_shape
          { cs_model = model; cs_wire_log = CL.empty_raw_io_log; cs_event_log = [] } /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures
        server_certificate_verify_body_empty_reachable_shape
          { cs_model = model'; cs_wire_log = CL.empty_raw_io_log; cs_event_log = [] })
=
  lemma_step_model_preserves_config model ev model';
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalSignCertificateVerify _ ->
       ()
     | LocalVerifyCertificateSignature _ ->
       assert (model.model_config.config_role == ClientEndpoint)
     | _ ->
       assert (model'.model_handshake.hs_certificate_verify ==
               model.model_handshake.hs_certificate_verify))
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.CertificateVerify _) ->
       ()
     | CL.Received, M.TlsHandshake (M.CertificateVerify _) ->
       assert (model.model_config.config_role == ClientEndpoint)
     | _, _ ->
       assert (model'.model_handshake.hs_certificate_verify ==
               model.model_handshake.hs_certificate_verify))
  | ConnProtectedHandshake step ->
    assert (model.model_config.config_role == ClientEndpoint)

#restart-solver
let lemma_connection_delta_server_certificate_verify_body_empty_reachable_shape
  (st0:connection_state)
  (st1:connection_state)
  : Lemma
      (requires
        server_certificate_verify_body_empty_reachable_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures server_certificate_verify_body_empty_reachable_shape st1)
=
  match st1 with
  | _ ->
    assert (exists delta. legal_connection_delta st0 delta st1);
    let delta_w =
      ID.indefinite_description_ghost
        connection_delta
        (fun delta -> legal_connection_delta st0 delta st1) in
    let delta : connection_delta = delta_w in
    assert (legal_connection_delta st0 delta st1);
    assert (legal_event st0.cs_model delta.delta_event);
    assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
    lemma_step_model_server_certificate_verify_body_empty_reachable_shape
      st0.cs_model
      delta.delta_event
      st1.cs_model

let lemma_initial_server_certificate_verify_body_empty_reachable_shape
  (cfg:connection_config)
  : Lemma
      (ensures
        server_certificate_verify_body_empty_reachable_shape (initial cfg))
=
  ()

let lemma_connection_state_single_step_server_certificate_verify_body_empty_reachable_shape
  (u:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern
            (server_certificate_verify_body_empty_reachable_shape y);
            (connection_state_single_step x y)}
          server_certificate_verify_body_empty_reachable_shape x /\
          connection_state_single_step x y ==>
          server_certificate_verify_body_empty_reachable_shape y)
=
  introduce forall x y.
    server_certificate_verify_body_empty_reachable_shape x /\
    connection_state_single_step x y ==>
    server_certificate_verify_body_empty_reachable_shape y
  with
    introduce _ ==> _ with
    lemma_connection_delta_server_certificate_verify_body_empty_reachable_shape x y

let lemma_connection_state_consistent_server_certificate_verify_body_empty
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st)
      (ensures True)
=
  let p = server_certificate_verify_body_empty_reachable_shape in
  lemma_initial_server_certificate_verify_body_empty_reachable_shape
    st.cs_model.model_config;
  lemma_connection_state_single_step_server_certificate_verify_body_empty_reachable_shape ();
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure
    connection_state_single_step
    p
    stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)

let lemma_step_model_key_update_pending_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 ev == Some model1)
      (ensures model_key_update_pending_delta model0 ev model1)
=
  match ev with
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Received, M.TlsKeyUpdate req ->
       (* No role hypothesis here, so name the rotated slot through the
          role-indexed label rather than assuming the client's view. *)
       (match model0.model_control with
        | ControlApplicationData ->
          (match traffic_material_for_label
                   model0.model_handshake.hs_keys
                   TrafficApplication
                   (traffic_label_for_endpoint_direction
                      model0.model_config.config_role
                      TrafficRead) with
           | Some _ -> ()
           | None -> assert False)
        | _ -> assert False)
     | CL.Sent, M.TlsKeyUpdate req ->
       (* Both request forms are legal to send.  [key_update_response_pending_step]
          already leaves [pending] untouched for a spontaneous [update_requested]
          and clears it only for the [update_not_requested] response, which is
          exactly what [sent_key_update_response] does. *)
       (match model0.model_control with
        | ControlApplicationData ->
          (match traffic_material_for_label
                   model0.model_handshake.hs_keys
                   TrafficApplication
                   (traffic_label_for_endpoint_direction
                      model0.model_config.config_role
                      TrafficWrite) with
           | Some _ -> ()
           | None -> assert False)
        | _ -> assert False)
     | _, _ -> ())
  | ConnLocalEvent _ -> ()
  | ConnProtectedHandshake _ -> ()

#push-options "--z3rlimit 150"
let lemma_step_model_record_keys_consistent
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        legal_event model0 ev /\
        step_model model0 ev == Some model1 /\
        model0.model_config.config_role == ClientEndpoint /\
        model_record_keys_consistent model0)
      (ensures model_record_keys_consistent model1)
=
  lemma_step_model_preserves_config_for_x25519_reachable_shape model0 ev model1;
  assert (model1.model_config == model0.model_config);
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalDeriveSharedSecret _ ->
       assert (model1.model_record == model0.model_record);
       assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
         model0.model_handshake.hs_keys.ks_client_handshake_traffic);
       assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
         model0.model_handshake.hs_keys.ks_server_handshake_traffic);
       assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
         model0.model_handshake.hs_keys.ks_client_application_traffic);
       assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
         model0.model_handshake.hs_keys.ks_server_application_traffic)
     | LocalInstallTrafficKeys install ->
       (match install.install_epoch, install.install_direction with
        | TrafficHandshake, TrafficWrite ->
          assert (model1.model_record.record_write ==
            R.install_keys
              model0.model_record.record_write
              R.Handshake
              install.install_material.traffic_alg install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
            Some install.install_material)
        | TrafficHandshake, TrafficRead ->
          assert (model1.model_record.record_read ==
            R.install_keys
              model0.model_record.record_read
              R.Handshake
              install.install_material.traffic_alg install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
            Some install.install_material)
        | TrafficApplication, TrafficWrite ->
          assert (model1.model_record == model0.model_record);
          assert (model1.model_control == model0.model_control);
          assert (model0.model_control == ControlHandshaking HsServerFinishedVerified)
        | TrafficApplication, TrafficRead ->
          assert (model1.model_record.record_read ==
            R.install_keys
              model0.model_record.record_read
              R.Application
              install.install_material.traffic_alg install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
            Some install.install_material))
     | LocalInstallTrafficKeysForRole role_install ->
       assert (role_install.install_role == ClientEndpoint);
       let install = role_install.install_payload in
       (match install.install_epoch, install.install_direction with
        | TrafficHandshake, TrafficWrite ->
          assert (model1.model_record.record_write ==
            R.install_keys
              model0.model_record.record_write
              R.Handshake
              install.install_material.traffic_alg install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
            Some install.install_material)
        | TrafficHandshake, TrafficRead ->
          assert (model1.model_record.record_read ==
            R.install_keys
              model0.model_record.record_read
              R.Handshake
              install.install_material.traffic_alg install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
            Some install.install_material)
        | TrafficApplication, TrafficWrite ->
          assert (model1.model_record == model0.model_record);
          assert (model1.model_control == model0.model_control);
          assert (model0.model_control == ControlHandshaking HsServerFinishedVerified)
        | TrafficApplication, TrafficRead ->
          assert (model1.model_record.record_read ==
            R.install_keys
              model0.model_record.record_read
              R.Application
              install.install_material.traffic_alg install.install_material.traffic_key
              install.install_material.traffic_iv);
          assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
            Some install.install_material))
     | LocalFail _ -> ()
     | _ ->
       assert (model1.model_record == model0.model_record);
       assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys))
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.Finished _) ->
       (match model0.model_control with
        | ControlHandshaking HsServerFinishedVerified ->
          assert (Some? model0.model_handshake.hs_keys.ks_client_application_traffic);
          (match model0.model_handshake.hs_keys.ks_client_application_traffic with
           | Some material ->
             assert (model1.model_record.record_write ==
               R.install_keys
                 (R.next_seq model0.model_record.record_write)
                 R.Application
                 material.traffic_alg material.traffic_key
                 material.traffic_iv);
             assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
               Some material)
           | None -> assert False)
        | _ -> assert False)
     | CL.Received, M.TlsKeyUpdate _ ->
       (match model0.model_control with
        | ControlApplicationData ->
          assert (Some? model0.model_handshake.hs_keys.ks_server_application_traffic);
          (match model0.model_handshake.hs_keys.ks_server_application_traffic with
           | Some old_server_app ->
             let new_server_app = updated_traffic_key_material old_server_app in
             assert (model1.model_record.record_read ==
               R.install_keys
                 (R.next_seq model0.model_record.record_read)
                 R.Application
                 new_server_app.traffic_alg new_server_app.traffic_key
                 new_server_app.traffic_iv);
             assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
               Some new_server_app)
           | None -> assert False)
        | _ -> assert False)
     | CL.Sent, M.TlsKeyUpdate _ ->
       (match model0.model_control with
        | ControlApplicationData ->
          assert (Some? model0.model_handshake.hs_keys.ks_client_application_traffic);
          (match model0.model_handshake.hs_keys.ks_client_application_traffic with
           | Some old_client_app ->
             let new_client_app = updated_traffic_key_material old_client_app in
             assert (model1.model_record.record_write ==
               R.install_keys
                 (R.next_seq model0.model_record.record_write)
                 R.Application
                 new_client_app.traffic_alg new_client_app.traffic_key
                 new_client_app.traffic_iv);
             assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
               Some new_client_app)
           | None -> assert False)
        | _ -> assert False)
     | CL.Sent, M.TlsApplicationData bytes ->
       assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
       assert (model1.model_record.record_write ==
         advance_direction_records
           model0.model_record.record_write
           (S.application_data_record_count bytes));
       lemma_record_write_keys_advance
         model0.model_control
         model0.model_handshake.hs_keys
         model0.model_record.record_write
         (S.application_data_record_count bytes)
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions _)
     | CL.Received, M.TlsHandshake (M.Certificate _)
     | CL.Received, M.TlsHandshake (M.CertificateVerify _)
     | CL.Received, M.TlsApplicationData _
     | CL.Received, M.TlsIgnoredPostHandshake _ ->
       assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
       assert (model1.model_record.record_read ==
         R.next_seq model0.model_record.record_read);
       lemma_record_read_keys_next_seq
         model0.model_handshake.hs_keys
         model0.model_record.record_read
     | CL.Received, M.TlsHandshake (M.Finished _) ->
       // Model-Fix-1 client atomic delivery: installs the server-app READ keys
       // (record_read epoch -> Application) and populates ks_server_application_traffic;
       // write side, handshake-slot keys and client-app slot are unchanged and control
       // stays within ControlHandshaking.
       (match model0.model_control with
        | ControlHandshaking HsCertificateVerifyVerified ->
          assert (model1.model_control == ControlHandshaking HsServerFinishedVerified);
          assert (model1.model_record.record_write == model0.model_record.record_write);
          assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
                  model0.model_handshake.hs_keys.ks_client_handshake_traffic);
          assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
                  model0.model_handshake.hs_keys.ks_server_handshake_traffic);
          assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
                  model0.model_handshake.hs_keys.ks_client_application_traffic);
          // Write side is preserved (record_write and the client-side key slots are
          // unchanged, and control remains within ControlHandshaking).
          assert (record_keys_match_key_schedule_for_role
            ClientEndpoint TrafficWrite model1.model_control
            model1.model_handshake.hs_keys model1.model_record.record_write);
          // Read side: record_read1 matches the freshly-installed server-app slot.
          (match model1.model_handshake.hs_keys.ks_server_application_traffic with
           | Some material ->
             assert (model1.model_record.record_read ==
               R.install_keys model0.model_record.record_read R.Application
                 material.traffic_alg material.traffic_key material.traffic_iv);
             assert (traffic_material_matches_record_direction
               material model1.model_record.record_read);
             assert (record_keys_match_key_schedule_for_role
               ClientEndpoint TrafficRead model1.model_control
               model1.model_handshake.hs_keys model1.model_record.record_read)
           | None -> assert False);
          assert (model_record_keys_consistent model1)
        | _ -> assert False)
     | CL.Received, M.TlsAlert T.Close_notify ->
       (match model1.model_control with
        | ControlFailed _ -> ()
        | _ ->
          assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
          assert (model1.model_record.record_read ==
            R.next_seq model0.model_record.record_read);
          lemma_record_read_keys_next_seq
            model0.model_handshake.hs_keys
            model0.model_record.record_read)
     | CL.Sent, M.TlsAlert T.Close_notify ->
       (match model1.model_control with
        | ControlFailed _ -> ()
        | _ ->
          assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
          assert (model1.model_record.record_write ==
            R.next_seq model0.model_record.record_write);
          lemma_record_write_keys_next_seq
            model0.model_control
            model0.model_handshake.hs_keys
            model0.model_record.record_write)
     | _, M.TlsAlert alert ->
       (match model1.model_control with
        | ControlFailed _ -> ()
        | _ ->
          assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys))
     | _ ->
       (match model1.model_control with
        | ControlFailed _ -> ()
        | _ ->
          assert (model1.model_record == model0.model_record);
          assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys)))
  | ConnProtectedHandshake step ->
    if step.protected_handshake_buffering
    then begin
      (* Buffering advances only the read sequence, and [next_seq] keeps the
         epoch and its installed material. *)
      assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
      assert (model1.model_record.record_read ==
        R.next_seq model0.model_record.record_read);
      assert (model1.model_record.record_write ==
        model0.model_record.record_write);
      lemma_record_read_keys_next_seq
        model0.model_handshake.hs_keys
        model0.model_record.record_read
    end
    else
    (match step.protected_handshake_message, model0.model_control with
     | M.Finished _, ControlHandshaking HsCertificateVerifyVerified ->
      assert (model1.model_control == ControlHandshaking HsServerFinishedVerified);
      assert (model1.model_record.record_write == model0.model_record.record_write);
      assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
              model0.model_handshake.hs_keys.ks_client_handshake_traffic);
      assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
              model0.model_handshake.hs_keys.ks_server_handshake_traffic);
      assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
              model0.model_handshake.hs_keys.ks_client_application_traffic);
      (match model1.model_handshake.hs_keys.ks_server_application_traffic with
       | Some material ->
         assert (model1.model_record.record_read ==
           R.install_keys model0.model_record.record_read R.Application
             material.traffic_alg material.traffic_key material.traffic_iv);
         assert (traffic_material_matches_record_direction
           material model1.model_record.record_read);
         assert (record_keys_match_key_schedule_for_role
           ClientEndpoint TrafficRead model1.model_control
           model1.model_handshake.hs_keys model1.model_record.record_read)
       | None -> assert False);
      assert (model_record_keys_consistent model1)
     | M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived
     | M.Certificate _, ControlHandshaking HsEncryptedExtensionsReceived
     | M.CertificateVerify _, ControlHandshaking HsCertificateValidated ->
      assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
      if step.protected_handshake_head
      then
        begin
          assert (model1.model_record.record_read ==
            R.next_seq model0.model_record.record_read);
          assert (model1.model_record.record_write ==
            model0.model_record.record_write);
          lemma_record_read_keys_next_seq
            model0.model_handshake.hs_keys
            model0.model_record.record_read
        end
      else
        assert (model1.model_record == model0.model_record)
     | _, _ ->
      assert False)

#pop-options
let lemma_step_model_record_keys_consistent_for_role
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
     (requires
       legal_event model0 ev /\
       step_model model0 ev == Some model1 /\
       role == model0.model_config.config_role /\
       model_record_keys_consistent_for_role role model0)
     (ensures model_record_keys_consistent_for_role role model1)
=
  match role with
  | ClientEndpoint ->
    assert (model0.model_config.config_role == ClientEndpoint);
    assert (model_record_keys_consistent model0);
    lemma_step_model_record_keys_consistent model0 ev model1
  | ServerEndpoint ->
    (match ev with
     | ConnLocalEvent local ->
      (match local with
       | LocalInstallTrafficKeysForRole role_install ->
         assert (role_install.install_role == model0.model_config.config_role);
         assert (role_install.install_role == ServerEndpoint);
         let install = role_install.install_payload in
         lemma_step_role_install_record_keys_consistent_for_role
           ServerEndpoint
           model0
           install
           model1
       | LocalInstallTrafficKeys _ ->
         assert False
       | LocalDeriveSharedSecret _ ->
         assert (model1.model_record == model0.model_record);
         assert (model1.model_handshake.hs_keys.ks_client_handshake_traffic ==
           model0.model_handshake.hs_keys.ks_client_handshake_traffic);
         assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
           model0.model_handshake.hs_keys.ks_server_handshake_traffic);
         assert (model1.model_handshake.hs_keys.ks_client_application_traffic ==
           model0.model_handshake.hs_keys.ks_client_application_traffic);
         assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
           model0.model_handshake.hs_keys.ks_server_application_traffic)
       | LocalVerifyClientFinished _ ->
         assert (model1.model_record == model0.model_record);
         assert (model1.model_control == ControlApplicationData);
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
         assert (application_record_keys_installed_for_role ServerEndpoint model0);
         assert (application_record_keys_installed_for_role ServerEndpoint model1)
       | LocalFail _ ->
         ()
       | _ ->
         assert (model1.model_record == model0.model_record);
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys))
     | ConnNetworkEvent msg ->
      (match msg.CL.message_value with
       | M.TlsApplicationData bytes ->
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
         (match msg.CL.message_direction with
          | CL.Sent ->
            assert (model1.model_record.record_write ==
              advance_direction_records
                model0.model_record.record_write
                (S.application_data_record_count bytes));
            assert (model1.model_record.record_read ==
              model0.model_record.record_read);
            lemma_record_keys_advance_for_role
              ServerEndpoint
              TrafficWrite
              model0.model_control
              model0.model_handshake.hs_keys
              model0.model_record.record_write
              (S.application_data_record_count bytes)
          | CL.Received ->
            assert (model1.model_record.record_read ==
              R.next_seq model0.model_record.record_read);
            assert (model1.model_record.record_write ==
              model0.model_record.record_write);
            lemma_record_keys_next_seq_for_role
              ServerEndpoint
              TrafficRead
              model0.model_control
              model0.model_handshake.hs_keys
              model0.model_record.record_read)
       | M.TlsHandshake (M.ClientHello _)
       | M.TlsHandshake (M.ServerHello _) ->
         assert (model1.model_record == model0.model_record);
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys)
       | M.TlsHandshake (M.Finished _) ->
         (match msg.CL.message_direction with
          | CL.Sent ->
            assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
            assert (model1.model_record.record_write ==
              R.next_seq model0.model_record.record_write);
            assert (model1.model_record.record_read ==
              model0.model_record.record_read);
            lemma_record_keys_next_seq_for_role
              ServerEndpoint
              TrafficWrite
              model0.model_control
              model0.model_handshake.hs_keys
              model0.model_record.record_write
          | CL.Received ->
            // Model-Fix-1 server atomic delivery: installs the client-app READ keys
            // (record_read epoch -> Application) and populates ks_client_application_traffic;
            // write side and the server-side key slots are unchanged.  Lands at
            // ControlApplicationData.
            (match model0.model_control with
             | ControlHandshaking HsServerFinishedSent ->
               assert (model1.model_control == ControlApplicationData);
               assert (model1.model_record.record_write ==
                 model0.model_record.record_write);
               assert (model1.model_handshake.hs_keys.ks_server_handshake_traffic ==
                       model0.model_handshake.hs_keys.ks_server_handshake_traffic);
               assert (model1.model_handshake.hs_keys.ks_server_application_traffic ==
                       model0.model_handshake.hs_keys.ks_server_application_traffic);
               // Write side is preserved (record_write and the server-side key slots
               // are unchanged; the server write obligation is control-insensitive).
               assert (record_keys_match_key_schedule_for_role
                 ServerEndpoint TrafficWrite model1.model_control
                 model1.model_handshake.hs_keys model1.model_record.record_write);
               // Read side: record_read1 matches the freshly-installed client-app slot.
               (match model1.model_handshake.hs_keys.ks_client_application_traffic with
                | Some material ->
                  assert (model1.model_record.record_read ==
                    R.install_keys model0.model_record.record_read R.Application
                      material.traffic_alg material.traffic_key material.traffic_iv);
                  assert (traffic_material_matches_record_direction
                    material model1.model_record.record_read);
                  assert (record_keys_match_key_schedule_for_role
                    ServerEndpoint TrafficRead model1.model_control
                    model1.model_handshake.hs_keys model1.model_record.record_read)
                | None -> assert False);
               assert (model_record_keys_consistent_for_role ServerEndpoint model1)
             | _ -> assert False))
       | M.TlsHandshake (M.EncryptedExtensions _)
       | M.TlsHandshake (M.Certificate _)
       | M.TlsHandshake (M.CertificateVerify _) ->
         assert (msg.CL.message_direction == CL.Sent);
         assert (model1.model_record.record_write ==
           R.next_seq model0.model_record.record_write);
         assert (model1.model_record.record_read ==
           model0.model_record.record_read);
         assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
         lemma_record_keys_next_seq_for_role
           ServerEndpoint
           TrafficWrite
           model0.model_control
           model0.model_handshake.hs_keys
           model0.model_record.record_write
       | M.TlsAlert T.Close_notify ->
         (match model0.model_control with
          | ControlApplicationData ->
            assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
            (match msg.CL.message_direction with
             | CL.Sent ->
               assert (model1.model_record.record_write ==
                 R.next_seq model0.model_record.record_write);
               assert (model1.model_record.record_read ==
                 model0.model_record.record_read);
               lemma_record_keys_next_seq_for_role
                 ServerEndpoint
                 TrafficWrite
                 model0.model_control
                 model0.model_handshake.hs_keys
                 model0.model_record.record_write
             | CL.Received ->
               assert (model1.model_record.record_read ==
                 R.next_seq model0.model_record.record_read);
               assert (model1.model_record.record_write ==
                 model0.model_record.record_write);
               lemma_record_keys_next_seq_for_role
                 ServerEndpoint
                 TrafficRead
                 model0.model_control
                 model0.model_handshake.hs_keys
                 model0.model_record.record_read)
          | ControlClosing ->
            assert (msg.CL.message_direction == CL.Received);
            assert (model1.model_handshake.hs_keys == model0.model_handshake.hs_keys);
            assert (model1.model_record.record_read ==
              R.next_seq model0.model_record.record_read);
            assert (model1.model_record.record_write ==
              model0.model_record.record_write);
            lemma_record_keys_next_seq_for_role
              ServerEndpoint
              TrafficRead
              model0.model_control
              model0.model_handshake.hs_keys
              model0.model_record.record_read
          | _ ->
            assert (ControlFailed? model1.model_control))
       | M.TlsAlert _ ->
         assert (ControlFailed? model1.model_control)
       | M.TlsKeyUpdate _ ->
         (* Rotation reinstalls the Application keys of the slot this endpoint
            owns in the stepped direction, and leaves the other direction
            untouched; for a server the read slot is ClientTraffic and the
            write slot is ServerTraffic. *)
         (match msg.CL.message_direction with
          | CL.Received ->
            (match traffic_material_for_label
                     model0.model_handshake.hs_keys
                     TrafficApplication
                     ClientTraffic with
             | Some old_read_app ->
               let new_read_app = updated_traffic_key_material old_read_app in
               assert (model1.model_record.record_read ==
                 R.install_keys
                   (R.next_seq model0.model_record.record_read)
                   R.Application
                   new_read_app.traffic_alg new_read_app.traffic_key
                   new_read_app.traffic_iv);
               assert (traffic_material_for_label
                         model1.model_handshake.hs_keys
                         TrafficApplication
                         ClientTraffic == Some new_read_app);
               assert (model1.model_record.record_write ==
                       model0.model_record.record_write);
               assert (traffic_material_for_label
                         model1.model_handshake.hs_keys
                         TrafficApplication
                         ServerTraffic ==
                       traffic_material_for_label
                         model0.model_handshake.hs_keys
                         TrafficApplication
                         ServerTraffic)
             | None -> assert False)
          | CL.Sent ->
            (match traffic_material_for_label
                     model0.model_handshake.hs_keys
                     TrafficApplication
                     ServerTraffic with
             | Some old_write_app ->
               let new_write_app = updated_traffic_key_material old_write_app in
               assert (model1.model_record.record_write ==
                 R.install_keys
                   (R.next_seq model0.model_record.record_write)
                   R.Application
                   new_write_app.traffic_alg new_write_app.traffic_key
                   new_write_app.traffic_iv);
               assert (traffic_material_for_label
                         model1.model_handshake.hs_keys
                         TrafficApplication
                         ServerTraffic == Some new_write_app);
               assert (model1.model_record.record_read ==
                       model0.model_record.record_read);
               assert (traffic_material_for_label
                         model1.model_handshake.hs_keys
                         TrafficApplication
                         ClientTraffic ==
                       traffic_material_for_label
                         model0.model_handshake.hs_keys
                         TrafficApplication
                         ClientTraffic)
             | None -> assert False))
       | M.TlsChangeCipherSpec ->
         assert (model1 == model0)
       | _ ->
         assert False)
     | ConnProtectedHandshake step ->
       assert False)

(* [set_pending_protected_handshake] rewrites the handshake buffers and nothing
   else; both of its branches leave [model_record] alone.  Naming the fact
   spares every caller the case split. *)
let lemma_set_pending_preserves_record
  (m:connection_model)
  (fragment:B.bytes)
  (parsed:nat)
  : Lemma
      (ensures
        (set_pending_protected_handshake m fragment parsed).model_record ==
          m.model_record /\
        (set_pending_protected_handshake m fragment parsed).model_control ==
          m.model_control /\
        (set_pending_protected_handshake m fragment parsed).model_handshake.hs_keys ==
          m.model_handshake.hs_keys)
=
  ()

let lemma_step_model_record_layer_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        legal_event model0 ev /\
        step_model model0 ev == Some model1)
      (ensures model_record_layer_delta model0 ev model1)
=
  (match ev with
  | ConnLocalEvent local ->
    assert (ev == ConnLocalEvent local);
    (match local with
     | LocalInstallTrafficKeys install ->
       assert (model1.model_record == install_record_keys model0.model_record install);
       lemma_projected_install_record_keys_of_record model0.model_record install;
       assert (model_record_layer_delta model0 ev model1)
     | LocalInstallTrafficKeysForRole role_install ->
      let install = role_install.install_payload in
      assert (role_install.install_role == model0.model_config.config_role);
      assert (model1.model_record ==
        install_record_keys_for_role
          role_install.install_role
          model0.model_record
          install);
      lemma_projected_install_record_keys_of_record_for_role
        role_install.install_role
        model0.model_record
        install;
      assert (model_record_layer_delta model0 ev model1)
     | _ ->
       assert (model1.model_record == model0.model_record);
       assert (model_record_layer_delta model0 ev model1))
  | ConnNetworkEvent msg ->
    assert (ev == ConnNetworkEvent msg);
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsApplicationData bytes ->
       assert (model1.model_record == {
         model0.model_record with
           record_write =
             advance_direction_records
               model0.model_record.record_write
               (S.application_data_record_count bytes)
       });
       lemma_projected_record_advance_write
         model0.model_record
         (S.application_data_record_count bytes);
       assert (model_record_layer_delta model0 ev model1)
     | CL.Sent, M.TlsHandshake (M.Finished _) ->
       (match model0.model_config.config_role with
        | ClientEndpoint ->
          (match model0.model_control with
           | ControlHandshaking HsServerFinishedVerified ->
             assert (Some? model0.model_handshake.hs_keys.ks_client_application_traffic);
             (match model0.model_handshake.hs_keys.ks_client_application_traffic with
              | Some _ ->
                assert (model1.model_record ==
                  install_client_application_write_after_finished
                    model0.model_record
                    model0.model_handshake.hs_keys);
                lemma_projected_client_application_write_after_finished
                  model0.model_record
                  model0.model_handshake.hs_keys;
                assert (model_record_layer_delta model0 ev model1)
              | None -> assert False)
           | _ -> assert False)
        | ServerEndpoint ->
          (match model0.model_control with
           | ControlHandshaking HsServerEncryptedFlightSent ->
             assert (model1.model_record == {
               model0.model_record with
                 record_write = R.next_seq model0.model_record.record_write
             });
             lemma_projected_record_next_write model0.model_record;
             assert (model_record_layer_delta model0 ev model1)
           | _ -> assert False))
     | CL.Received, M.TlsKeyUpdate _ ->
       (* Role-generic: a received KeyUpdate rotates whichever
          application-traffic slot this endpoint reads with. *)
       (match model0.model_control with
        | ControlApplicationData ->
          (match traffic_material_for_label
                   model0.model_handshake.hs_keys
                   TrafficApplication
                   (traffic_label_for_endpoint_direction
                      model0.model_config.config_role
                      TrafficRead) with
           | Some old_read_app ->
             let new_read_app = updated_traffic_key_material old_read_app in
             assert (model1.model_record == {
               model0.model_record with
                 record_read =
                   R.install_keys
                     (R.next_seq model0.model_record.record_read)
                     R.Application
                     new_read_app.traffic_alg new_read_app.traffic_key
                     new_read_app.traffic_iv
             });
             lemma_projected_install_keys_of_record
               (R.next_seq model0.model_record.record_read)
               R.Application
               new_read_app.traffic_alg
               new_read_app.traffic_key
               new_read_app.traffic_iv;
             assert (model_record_layer_delta model0 ev model1)
           | None -> assert False)
        | _ -> assert False)
     | CL.Sent, M.TlsKeyUpdate req ->
       (* Role-generic: a sent KeyUpdate rotates whichever application-traffic
          slot this endpoint writes with, and both request forms are legal. *)
       (match model0.model_control with
        | ControlApplicationData ->
          (match traffic_material_for_label
                   model0.model_handshake.hs_keys
                   TrafficApplication
                   (traffic_label_for_endpoint_direction
                      model0.model_config.config_role
                      TrafficWrite) with
           | Some old_write_app ->
             let new_write_app = updated_traffic_key_material old_write_app in
             assert (model1.model_record == {
               model0.model_record with
                 record_write =
                   R.install_keys
                     (R.next_seq model0.model_record.record_write)
                     R.Application
                     new_write_app.traffic_alg new_write_app.traffic_key
                     new_write_app.traffic_iv
             });
             lemma_projected_install_keys_of_record
               (R.next_seq model0.model_record.record_write)
               R.Application
               new_write_app.traffic_alg
               new_write_app.traffic_key
               new_write_app.traffic_iv;
             assert (model_record_layer_delta model0 ev model1)
           | None -> assert False)
        | _ -> assert False)
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions _)
     | CL.Received, M.TlsHandshake (M.Certificate _)
     | CL.Received, M.TlsHandshake (M.CertificateVerify _) ->
       assert (model1.model_record == {
         model0.model_record with
           record_read = R.next_seq model0.model_record.record_read
       });
       lemma_projected_record_next_read model0.model_record;
       assert (
         projected_record_layer_step_for_role
           model0.model_config.config_role
           (projected_record_layer_state_of_record model0.model_record)
           ev ==
         { projected_record_layer_state_of_record model0.model_record with
             projected_read =
               projected_next_seq
                 (projected_record_layer_state_of_record model0.model_record).projected_read });
       assert (model_record_layer_delta model0 ev model1)
     | CL.Received, M.TlsHandshake (M.Finished _) ->
       // Model-Fix-1 atomic delivery: recv-Finished installs the peer application
       // READ keys (record_read epoch -> Application, seq reset to 0), so the
       // projected read side installs Application keys rather than merely advancing
       // the sequence number.  step_handshake_message only produces a (non-None)
       // result for a received Finished at HsCertificateVerifyVerified (client
       // delivery) or HsServerFinishedSent (server delivery); the projected step is
       // role-insensitive and installs the Application read keys in both.
       (match model0.model_control with
        | ControlHandshaking HsCertificateVerifyVerified ->
          (match model1.model_handshake.hs_keys.ks_server_application_traffic with
           | Some material ->
             assert (model1.model_record == {
               model0.model_record with
                 record_read =
                   R.install_keys
                     model0.model_record.record_read
                     R.Application
                     material.traffic_alg material.traffic_key
                     material.traffic_iv
             });
             lemma_projected_install_keys_of_record
               model0.model_record.record_read
               R.Application
               material.traffic_alg
               material.traffic_key
               material.traffic_iv;
             assert (model_record_layer_delta model0 ev model1)
           | None -> assert False)
        | ControlHandshaking HsServerFinishedSent ->
          (match model1.model_handshake.hs_keys.ks_client_application_traffic with
           | Some material ->
             assert (model1.model_record == {
               model0.model_record with
                 record_read =
                   R.install_keys
                     model0.model_record.record_read
                     R.Application
                     material.traffic_alg material.traffic_key
                     material.traffic_iv
             });
             lemma_projected_install_keys_of_record
               model0.model_record.record_read
               R.Application
               material.traffic_alg
               material.traffic_key
               material.traffic_iv;
             assert (model_record_layer_delta model0 ev model1)
           | None -> assert False)
        | _ -> assert False)
     | CL.Sent, M.TlsHandshake (M.EncryptedExtensions _)
     | CL.Sent, M.TlsHandshake (M.Certificate _)
     | CL.Sent, M.TlsHandshake (M.CertificateVerify _) ->
       assert (model1.model_record == {
         model0.model_record with
           record_write = R.next_seq model0.model_record.record_write
       });
       lemma_projected_record_next_write model0.model_record;
       assert (
         projected_record_layer_step_for_role
           model0.model_config.config_role
           (projected_record_layer_state_of_record model0.model_record)
           ev ==
         { projected_record_layer_state_of_record model0.model_record with
             projected_write =
               projected_next_seq
                 (projected_record_layer_state_of_record model0.model_record).projected_write });
       assert (model_record_layer_delta model0 ev model1)
     | CL.Received, M.TlsApplicationData _ ->
       assert (model1.model_record == {
         model0.model_record with
           record_read = R.next_seq model0.model_record.record_read
       });
       lemma_projected_record_next_read model0.model_record;
       assert (
         projected_record_layer_step_for_role
           model0.model_config.config_role
           (projected_record_layer_state_of_record model0.model_record)
           ev ==
         { projected_record_layer_state_of_record model0.model_record with
             projected_read =
               projected_next_seq
                 (projected_record_layer_state_of_record model0.model_record).projected_read });
       assert (model_record_layer_delta model0 ev model1)
     | CL.Received, M.TlsIgnoredPostHandshake _ ->
       assert (model1.model_record == {
         model0.model_record with
           record_read = R.next_seq model0.model_record.record_read
       });
       lemma_projected_record_next_read model0.model_record;
       assert (
         projected_record_layer_step_for_role
           model0.model_config.config_role
           (projected_record_layer_state_of_record model0.model_record)
           ev ==
         { projected_record_layer_state_of_record model0.model_record with
             projected_read =
               projected_next_seq
                 (projected_record_layer_state_of_record model0.model_record).projected_read });
       assert (model_record_layer_delta model0 ev model1)
     | CL.Received, M.TlsAlert T.Close_notify ->
       (match model0.model_control with
        | ControlApplicationData
        | ControlClosing ->
          assert (model1.model_record == {
            model0.model_record with
              record_read = R.next_seq model0.model_record.record_read
          });
          lemma_projected_record_next_read model0.model_record;
          assert (
            projected_record_layer_step_for_role
              model0.model_config.config_role
              (projected_record_layer_state_of_record model0.model_record)
              ev ==
            { projected_record_layer_state_of_record model0.model_record with
                projected_read =
                  projected_next_seq
                    (projected_record_layer_state_of_record model0.model_record).projected_read });
          assert (model_record_layer_delta model0 ev model1)
        | _ ->
          assert (model1.model_control == ControlFailed (T.AlertError T.Close_notify));
          assert (model_record_layer_delta model0 ev model1))
     | CL.Sent, M.TlsAlert T.Close_notify ->
       (match model0.model_control with
        | ControlApplicationData ->
          assert (model1.model_record == {
            model0.model_record with
              record_write = R.next_seq model0.model_record.record_write
          });
          lemma_projected_record_next_write model0.model_record;
          assert (
            projected_record_layer_step_for_role
              model0.model_config.config_role
              (projected_record_layer_state_of_record model0.model_record)
              ev ==
            { projected_record_layer_state_of_record model0.model_record with
                projected_write =
                  projected_next_seq
                    (projected_record_layer_state_of_record model0.model_record).projected_write });
          assert (model_record_layer_delta model0 ev model1)
        | _ ->
          assert (model1.model_control == ControlFailed (T.AlertError T.Close_notify));
          assert (model_record_layer_delta model0 ev model1))
     | _, _ ->
       assert (model1.model_record == model0.model_record);
       assert (model_record_layer_delta model0 ev model1))
  | ConnProtectedHandshake step ->
    assert (ev == ConnProtectedHandshake step);
    if step.protected_handshake_buffering
    then begin
      (* Buffering rewrites only the handshake buffers on top of a read-sequence
         bump, so the record layer moves exactly as it does for a head step. *)
      assert_norm (
        step_model model0 (ConnProtectedHandshake step) ==
          step_protected_handshake model0 step);
      assert (step_protected_handshake model0 step == Some model1);
      assert (model1 == step_protected_handshake_buffer model0 step);
      lemma_set_pending_preserves_record
        { model0 with
            model_record =
              { model0.model_record with
                  record_read = R.next_seq model0.model_record.record_read } }
        (protected_handshake_stream model0 step)
        0;
      assert (model1.model_record ==
        { model0.model_record with
            record_read = R.next_seq model0.model_record.record_read });
      lemma_projected_record_next_read model0.model_record;
      assert (model_record_layer_delta model0 ev model1)
    end
    else
    (match step.protected_handshake_message, model0.model_control with
     | M.Finished _, ControlHandshaking HsCertificateVerifyVerified ->
       (match model1.model_handshake.hs_keys.ks_server_application_traffic with
        | Some material ->
          assert (model1.model_record.record_read ==
            R.install_keys model0.model_record.record_read R.Application
              material.traffic_alg material.traffic_key material.traffic_iv);
          lemma_projected_install_keys_of_record
            model0.model_record.record_read
            R.Application
            material.traffic_alg
            material.traffic_key
            material.traffic_iv;
          assert (model_record_layer_delta model0 ev model1)
        | None -> assert False)
     | M.EncryptedExtensions _, ControlHandshaking HsServerHelloReceived
     | M.Certificate _, ControlHandshaking HsEncryptedExtensionsReceived
     | M.CertificateVerify _, ControlHandshaking HsCertificateValidated ->
       if step.protected_handshake_head
       then
         begin
           assert (model1.model_record == {
             model0.model_record with
               record_read = R.next_seq model0.model_record.record_read
           });
           lemma_projected_record_next_read model0.model_record;
           assert (model_record_layer_delta model0 ev model1)
         end
       else
         begin
           assert (model1.model_record == model0.model_record);
           assert (model_record_layer_delta model0 ev model1)
         end
     | _, _ ->
       assert False))

#restart-solver
let lemma_step_model_pending_application_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 ev == Some model1)
      (ensures model_pending_application_delta model0 ev model1)
=
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalDeliverApplicationData _
     | LocalFail _ -> ()
     | _ ->
       assert (model1.model_application == model0.model_application))
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsApplicationData _ ->
       assert (model1.model_application.app_pending_plaintext ==
         model0.model_application.app_pending_plaintext);
       assert (model1.model_application.app_pending_source_record ==
         model0.model_application.app_pending_source_record);
       assert (model1.model_application.app_pending_source_offset ==
         model0.model_application.app_pending_source_offset);
       assert (model1.model_application.app_pending_received_raw ==
         model0.model_application.app_pending_received_raw)
     | M.TlsKeyUpdate _ ->
       assert (model1.model_application.app_pending_plaintext ==
         model0.model_application.app_pending_plaintext);
       assert (model1.model_application.app_pending_source_record ==
         model0.model_application.app_pending_source_record);
       assert (model1.model_application.app_pending_source_offset ==
         model0.model_application.app_pending_source_offset);
       assert (model1.model_application.app_pending_received_raw ==
         model0.model_application.app_pending_received_raw)
     | _ ->
       assert (model1.model_application == model0.model_application))
  | ConnProtectedHandshake _ ->
    assert (model1.model_application == model0.model_application)

let lemma_step_model_transcript_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 ev == Some model1)
      (ensures model_transcript_delta model0 ev model1)
=
  let t0 = model0.model_handshake.hs_transcript in
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalVerifyFinished _ -> ()
     | LocalVerifyClientFinished _ -> ()
     | _ ->
       CL.lemma_append_empty_right t0;
       Seq.lemma_eq_refl model1.model_handshake.hs_transcript t0)
  | ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Sent, M.TlsHandshake (M.ClientHello _) -> ()
     | CL.Received, M.TlsHandshake (M.ClientHello _) -> ()
     | CL.Received, M.TlsHandshake (M.ServerHello _) -> ()
     | CL.Sent, M.TlsHandshake (M.ServerHello _) -> ()
     | CL.Sent, M.TlsHandshake (M.EncryptedExtensions _) -> ()
     | CL.Received, M.TlsHandshake (M.EncryptedExtensions _) -> ()
     | CL.Sent, M.TlsHandshake (M.Certificate _) -> ()
     | CL.Received, M.TlsHandshake (M.Certificate _) -> ()
     | CL.Sent, M.TlsHandshake (M.CertificateVerify _) -> ()
     | CL.Received, M.TlsHandshake (M.CertificateVerify _) -> ()
     | CL.Sent, M.TlsHandshake (M.Finished _) -> ()
     | CL.Received, M.TlsHandshake (M.Finished _) -> ()
     | _, _ ->
       CL.lemma_append_empty_right t0;
       Seq.lemma_eq_refl model1.model_handshake.hs_transcript t0)
  | ConnProtectedHandshake _ -> ()

let lemma_step_model_app_log_delta
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires step_model model0 ev == Some model1)
      (ensures model_app_log_delta model0 ev model1)
=
  let app = model0.model_application.app_log in
  match ev with
  | ConnLocalEvent local ->
    (match local with
     | LocalDeliverApplicationData bytes ->
       (match model0.model_control with
        | ControlApplicationData -> ()
        | _ -> assert False)
     | _ ->
       append_l_nil app.CL.app_sent;
       append_l_nil app.CL.app_received)
  | ConnProtectedHandshake _ ->
    append_l_nil app.CL.app_sent;
    append_l_nil app.CL.app_received
  | ConnNetworkEvent msg ->
    (match msg.CL.message_value with
     | M.TlsApplicationData bytes ->
       (match model0.model_control with
        | ControlApplicationData ->
          (match msg.CL.message_direction with
           | CL.Sent -> append_l_nil app.CL.app_received
           | CL.Received -> append_l_nil app.CL.app_sent)
        | _ -> assert False)
     | _ ->
       append_l_nil app.CL.app_sent;
       append_l_nil app.CL.app_received)

let rec lemma_connection_log_trace_sent_tls
  (events:list conn_event)
  : Lemma
      (ensures
        CL.sent_tls_of_host_trace (connection_log_trace_of_conn_events events) ==
          sent_tls_messages events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_sent_tls rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnProtectedHandshake _ -> ()
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let rec lemma_connection_log_trace_received_tls
  (events:list conn_event)
  : Lemma
      (ensures
        CL.received_tls_of_host_trace (connection_log_trace_of_conn_events events) ==
          received_tls_messages events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_received_tls rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnProtectedHandshake _ -> ()
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let rec lemma_connection_log_trace_state_events
  (events:list conn_event)
  : Lemma
      (ensures
        CL.state_events_of_host_trace (connection_log_trace_of_conn_events events) ==
          state_machine_events events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_state_events rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnProtectedHandshake step ->
      (match step.protected_handshake_message with
       | M.ClientHello _
       | M.ServerHello _
       | M.EncryptedExtensions _
       | M.Certificate _
       | M.CertificateVerify _
       | M.Finished _
       | M.HelloRetryRequest -> ())
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let rec lemma_connection_log_trace_app_sent
  (events:list conn_event)
  : Lemma
      (ensures
        CL.app_sent_of_host_trace (connection_log_trace_of_conn_events events) ==
          app_sent_messages events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_app_sent rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnProtectedHandshake _ -> ()
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let rec lemma_connection_log_trace_app_received
  (events:list conn_event)
  : Lemma
      (ensures
        CL.app_received_of_host_trace (connection_log_trace_of_conn_events events) ==
          app_received_messages events)
      (decreases events)
=
  match events with
  | [] -> ()
  | ev :: rest ->
    lemma_connection_log_trace_app_received rest;
    match ev with
    | ConnNetworkEvent _ -> ()
    | ConnProtectedHandshake _ -> ()
    | ConnLocalEvent local ->
      (match local with
       | LocalValidateCertificate _
       | LocalDeliverApplicationData _
       | LocalFail _ -> ()
       | _ -> ())

let lemma_connection_state_connection_log_view_consistent
  (st:connection_state)
  : Lemma
      (requires
        connection_state_app_log_consistent st /\
        connection_state_pending_application_consistent st)
      (ensures connection_state_connection_log_view_consistent st)
=
  let view = connection_log_view_of_state st in
  CL.lemma_raw_stream_view_shape
    #M.tls_message
    st.cs_wire_log.CL.raw_sent
    (sent_tls_messages st.cs_event_log);
  CL.lemma_raw_stream_view_shape
    #M.tls_message
    st.cs_wire_log.CL.raw_received
    (received_tls_messages st.cs_event_log);
  CL.lemma_parse_record_prefix_serializes st.cs_wire_log.CL.raw_sent;
  CL.lemma_parse_record_prefix_serializes st.cs_wire_log.CL.raw_received;
  lemma_connection_log_trace_sent_tls st.cs_event_log;
  lemma_connection_log_trace_received_tls st.cs_event_log;
  lemma_connection_log_trace_state_events st.cs_event_log;
  lemma_connection_log_trace_app_sent st.cs_event_log;
  lemma_connection_log_trace_app_received st.cs_event_log;
  assert (view.CL.sent_tls.CL.values == sent_tls_messages st.cs_event_log);
  assert (view.CL.received_tls.CL.values == received_tls_messages st.cs_event_log);
  assert (CL.app_log_of_host_trace view.CL.host_trace == {
    CL.app_sent = app_sent_messages st.cs_event_log;
    CL.app_received = app_received_messages st.cs_event_log;
  });
  assert (CL.app_log_of_host_trace view.CL.host_trace == view.CL.app_view);
  assert (CL.pending_app_source_consistent view)

let lemma_raw_records_exactly_one_parse_record
  (raw:B.bytes)
  (outer:T.content_type)
  : Lemma
      (requires raw_records_exactly raw outer 1)
      (ensures exists fragment.
        W.parse_record raw == Some (outer, fragment, B.length raw))
=
  let parsed = CL.parse_record_prefix raw in
  assert (CL.record_stream_serializes raw parsed);
  assert (Seq.equal parsed.CL.residual B.empty);
  assert (length parsed.CL.values == 1);
  assert (all_records_outer_type outer parsed.CL.values);
  assert (parsed.CL.consumed <= B.length raw);
  assert (Seq.equal parsed.CL.residual
                    (Seq.slice raw parsed.CL.consumed (B.length raw)));
  Seq.lemma_eq_elim parsed.CL.residual B.empty;
  Seq.lemma_eq_elim
    parsed.CL.residual
    (Seq.slice raw parsed.CL.consumed (B.length raw));
  Seq.lemma_len_slice raw parsed.CL.consumed (B.length raw);
  assert (B.length (Seq.slice raw parsed.CL.consumed (B.length raw)) == 0);
  assert (parsed.CL.consumed == B.length raw);
  match W.parse_record raw with
  | None ->
    assert (B.length raw + 1 > 0);
    assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
    assert (parsed.CL.values == []);
    assert False
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_serializes raw;
    if consumed == 0 || consumed > B.length raw then (
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    ) else (
      let rest = Seq.slice raw consumed (B.length raw) in
      let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
      let record =
        { M.record_outer_type = content_type;
          M.record_fragment = fragment } in
      assert (CL.parse_record_prefix raw ==
        {
          CL.values = record :: tail.CL.values;
          CL.consumed = consumed + tail.CL.consumed;
          CL.residual = tail.CL.residual;
        });
      assert (parsed.CL.values == record :: tail.CL.values);
      assert (length tail.CL.values == 0);
      assert (all_records_outer_type outer (record :: tail.CL.values));
      assert (content_type == outer);
      CL.lemma_parse_record_prefix_fuel_serializes (B.length raw) rest;
      assert (CL.record_stream_serializes rest tail);
      assert (tail.CL.consumed == B.length (CL.serialize_tls_records tail.CL.values));
      match tail.CL.values with
      | [] ->
        assert (CL.serialize_tls_records tail.CL.values == B.empty);
        assert (tail.CL.consumed == 0);
        assert (parsed.CL.consumed == consumed + tail.CL.consumed);
        assert (consumed == parsed.CL.consumed);
        assert (consumed == B.length raw);
        assert (W.parse_record raw == Some (outer, fragment, B.length raw));
        assert (exists fragment'. W.parse_record raw == Some (outer, fragment', B.length raw))
      | _ :: _ ->
        assert False
    )

let lemma_raw_records_exactly_nonempty_parse_record
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw)
=
  let parsed = CL.parse_record_prefix raw in
  assert (length parsed.CL.values == count);
  assert (all_records_outer_type outer parsed.CL.values);
  match W.parse_record raw with
  | None ->
    assert (B.length raw + 1 > 0);
    assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
    assert (parsed.CL.values == []);
    assert False
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_serializes raw;
    if consumed == 0 || consumed > B.length raw then (
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    ) else (
      let rest = Seq.slice raw consumed (B.length raw) in
      let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
      let record =
        { M.record_outer_type = content_type;
          M.record_fragment = fragment } in
      assert (CL.parse_record_prefix raw ==
        {
          CL.values = record :: tail.CL.values;
          CL.consumed = consumed + tail.CL.consumed;
          CL.residual = tail.CL.residual;
        });
      assert (parsed.CL.values == record :: tail.CL.values);
      assert (all_records_outer_type outer (record :: tail.CL.values));
      assert (content_type == outer);
      assert (W.parse_record raw == Some (outer, fragment, consumed));
      assert (exists fragment'. exists (consumed':nat).
        W.parse_record raw == Some (outer, fragment', consumed') /\
        consumed' > 0 /\
        consumed' <= B.length raw)
    )

let lemma_raw_records_exactly_nonempty_decompose
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        (let rest = Seq.slice raw consumed (B.length raw) in
         let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
         CL.record_stream_serializes rest tail /\
         Seq.equal tail.CL.residual B.empty /\
         length tail.CL.values == count - 1 /\
         all_records_outer_type outer tail.CL.values))
=
  let parsed = CL.parse_record_prefix raw in
  assert (CL.record_stream_serializes raw parsed);
  assert (Seq.equal parsed.CL.residual B.empty);
  assert (length parsed.CL.values == count);
  assert (all_records_outer_type outer parsed.CL.values);
  match W.parse_record raw with
  | None ->
    assert (B.length raw + 1 > 0);
    assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
    assert (parsed.CL.values == []);
    assert False
  | Some (content_type, fragment, consumed) ->
    W.lemma_parse_record_serializes raw;
    if consumed == 0 || consumed > B.length raw then (
      assert (CL.parse_record_prefix raw == CL.raw_record_stream_view raw);
      assert (parsed.CL.values == []);
      assert False
    ) else (
      let rest = Seq.slice raw consumed (B.length raw) in
      let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
      let record =
        { M.record_outer_type = content_type;
          M.record_fragment = fragment } in
      assert (CL.parse_record_prefix raw ==
        {
          CL.values = record :: tail.CL.values;
          CL.consumed = consumed + tail.CL.consumed;
          CL.residual = tail.CL.residual;
        });
      assert (parsed.CL.values == record :: tail.CL.values);
      assert (parsed.CL.residual == tail.CL.residual);
      assert (all_records_outer_type outer (record :: tail.CL.values));
      assert (content_type == outer);
      assert (all_records_outer_type outer tail.CL.values);
      CL.lemma_parse_record_prefix_fuel_serializes (B.length raw) rest;
      assert (CL.record_stream_serializes rest tail);
      assert (Seq.equal tail.CL.residual B.empty);
      assert (length tail.CL.values == count - 1);
      assert (W.parse_record raw == Some (outer, fragment, consumed));
      assert (exists fragment'. exists (consumed':nat).
        W.parse_record raw == Some (outer, fragment', consumed') /\
        consumed' > 0 /\
        consumed' <= B.length raw /\
        (let rest' = Seq.slice raw consumed' (B.length raw) in
         let tail' = CL.parse_record_prefix_fuel (B.length raw) rest' in
         CL.record_stream_serializes rest' tail' /\
         Seq.equal tail'.CL.residual B.empty /\
         length tail'.CL.values == count - 1 /\
         all_records_outer_type outer tail'.CL.values))
    )

let lemma_raw_records_exactly_nonempty_decompose_prefix
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count /\ count > 0)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (outer, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        raw_records_exactly
          (Seq.slice raw consumed (B.length raw))
          outer
          (count - 1))
=
  lemma_raw_records_exactly_nonempty_decompose raw outer count;
  match W.parse_record raw with
  | None ->
    assert False
  | Some (content_type, fragment, consumed) ->
    assert (W.parse_record raw == Some (content_type, fragment, consumed));
    assert (content_type == outer);
    assert (W.parse_record raw == Some (outer, fragment, consumed));
    assert (consumed > 0);
    assert (consumed <= B.length raw);
    let rest = Seq.slice raw consumed (B.length raw) in
    let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
    assert (CL.record_stream_serializes rest tail);
    assert (Seq.equal tail.CL.residual B.empty);
    assert (length tail.CL.values == count - 1);
    assert (all_records_outer_type outer tail.CL.values);
    Seq.lemma_len_slice raw consumed (B.length raw);
    assert (consumed + B.length rest == B.length raw);
    assert (B.length rest + 1 <= B.length raw);
    CL.lemma_parse_record_prefix_fuel_eq_parse_record_prefix (B.length raw) rest;
    assert (tail == CL.parse_record_prefix rest);
    let parsed_rest = CL.parse_record_prefix rest in
    assert (CL.record_stream_serializes rest parsed_rest);
    assert (Seq.equal parsed_rest.CL.residual B.empty);
    assert (length parsed_rest.CL.values == count - 1);
    assert (all_records_outer_type outer parsed_rest.CL.values);
    assert (raw_records_exactly rest outer (count - 1));
    assert (exists fragment'. exists (consumed':nat).
      W.parse_record raw == Some (outer, fragment', consumed') /\
      consumed' > 0 /\
      consumed' <= B.length raw /\
      raw_records_exactly
        (Seq.slice raw consumed' (B.length raw))
        outer
        (count - 1))

let rec lemma_raw_records_exactly_segmented
  (raw:B.bytes)
  (outer:T.content_type)
  (count:nat)
  : Lemma
      (requires raw_records_exactly raw outer count)
      (ensures raw_records_segmented raw outer count)
      (decreases count)
=
  if count == 0 then (
    let parsed = CL.parse_record_prefix raw in
    assert (CL.record_stream_serializes raw parsed);
    assert (Seq.equal parsed.CL.residual B.empty);
    assert (length parsed.CL.values == 0);
    match parsed.CL.values with
    | [] ->
      assert (CL.serialize_tls_records parsed.CL.values == B.empty);
      assert (parsed.CL.consumed == 0);
      assert (Seq.equal parsed.CL.residual
                        (Seq.slice raw parsed.CL.consumed (B.length raw)));
      Seq.lemma_eq_elim parsed.CL.residual B.empty;
      Seq.lemma_eq_elim
        parsed.CL.residual
        (Seq.slice raw parsed.CL.consumed (B.length raw));
      Seq.lemma_len_slice raw parsed.CL.consumed (B.length raw);
      assert (B.length (Seq.slice raw parsed.CL.consumed (B.length raw)) == 0);
      assert (parsed.CL.consumed == 0);
      assert (B.length raw == 0);
      assert (forall (i:nat{i < B.length raw}).
        Seq.index raw i == Seq.index B.empty i);
      Seq.lemma_eq_intro raw B.empty
    | _ :: _ ->
      assert False
  ) else (
    lemma_raw_records_exactly_nonempty_decompose_prefix raw outer count;
    match W.parse_record raw with
    | None -> assert False
    | Some (content_type, fragment, consumed) ->
      assert (content_type == outer);
      assert (W.parse_record raw == Some (outer, fragment, consumed));
      assert (consumed > 0);
      assert (consumed <= B.length raw);
      let rest = Seq.slice raw consumed (B.length raw) in
      assert (raw_records_exactly rest outer (count - 1));
      lemma_raw_records_exactly_segmented rest outer (count - 1);
      assert (raw_records_segmented rest outer (count - 1));
      assert (exists fragment'. exists (consumed':nat).
        W.parse_record raw == Some (outer, fragment', consumed') /\
        consumed' > 0 /\
        consumed' <= B.length raw /\
        raw_records_segmented
          (Seq.slice raw consumed' (B.length raw))
          outer
          (count - 1))
  )

let lemma_raw_records_exactly_single_serialized
  (outer:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
      (raw_records_exactly (W.serialize_record outer fragment) outer 1)
=
  let raw = W.serialize_record outer fragment in
  W.lemma_parse_record_serialize_record outer fragment;
  CL.lemma_parse_record_prefix_serializes raw;
  assert (B.length raw > 0);
  assert (W.parse_record raw == Some (outer, fragment, B.length raw));
  let rest = Seq.slice raw (B.length raw) (B.length raw) in
  Seq.lemma_len_slice raw (B.length raw) (B.length raw);
  assert (B.length rest == 0);
  Seq.lemma_eq_intro rest B.empty;
  assert (rest == B.empty);
  assert (CL.parse_record_prefix_fuel (B.length raw) rest ==
    CL.raw_record_stream_view rest);
  assert (CL.raw_record_stream_view rest ==
    { CL.values = []; CL.consumed = 0; CL.residual = rest });
  assert (CL.record_stream_serializes raw (CL.parse_record_prefix raw));
  assert (CL.parse_record_prefix raw ==
    {
      CL.values = [{ M.record_outer_type = outer; M.record_fragment = fragment }];
      CL.consumed = B.length raw;
      CL.residual = B.empty;
    });
  assert (length (CL.parse_record_prefix raw).CL.values == 1);
  assert (all_records_outer_type outer (CL.parse_record_prefix raw).CL.values)

let lemma_raw_application_data_record_exactly
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
      (raw_records_exactly (W.serialize_record T.Application_data fragment) T.Application_data 1)
=
  lemma_raw_records_exactly_single_serialized T.Application_data fragment

let lemma_parse_record_full_raw_records_exactly
  (raw:B.bytes)
  (outer:T.content_type)
  (fragment:B.bytes)
  : Lemma
      (requires W.parse_record raw == Some (outer, fragment, B.length raw))
      (ensures raw_records_exactly raw outer 1 /\
               raw_records_segmented raw outer 1)
=
  W.lemma_parse_record_serializes raw;
  W.lemma_parse_record_fragment_bound raw;
  assert (B.length fragment <= 16640);
  let serialized = W.serialize_record outer fragment in
  assert (B.length raw == B.length serialized);
  assert (Seq.equal serialized (Seq.slice raw 0 (B.length raw)));
  Seq.lemma_len_slice raw 0 (B.length raw);
  assert (B.length (Seq.slice raw 0 (B.length raw)) == B.length raw);
  assert (forall (i:nat{i < B.length raw}).
    Seq.index raw i == Seq.index (Seq.slice raw 0 (B.length raw)) i);
  Seq.lemma_eq_intro raw (Seq.slice raw 0 (B.length raw));
  assert (Seq.equal raw serialized);
  lemma_raw_records_exactly_single_serialized outer fragment;
  Seq.lemma_eq_elim raw serialized;
  assert (raw_records_exactly raw outer 1);
  lemma_raw_records_exactly_segmented raw outer 1

let lemma_sent_single_protected_message_seal_intro
  (model:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  (aad:B.bytes)
  (ciphertext:B.bytes)
  : Lemma
      (requires
        W.parse_record raw == Some (T.Application_data, ciphertext, B.length raw) /\
        Seq.equal aad (record_header_aad raw) /\
        R.seal
          model.model_record.record_write
          aad
          {
            R.content_type = T.Application_data;
            R.fragment = sent_tls_inner_plaintext_fragment msg;
          } ==
          Some (ciphertext, R.next_seq model.model_record.record_write))
      (ensures sent_single_protected_message_seal model msg raw)
=
  Seq.lemma_eq_elim aad (record_header_aad raw);
  assert (exists ciphertext'.
    W.parse_record raw == Some (T.Application_data, ciphertext', B.length raw) /\
    R.seal
      model.model_record.record_write
      (record_header_aad raw)
      {
        R.content_type = T.Application_data;
        R.fragment = sent_tls_inner_plaintext_fragment msg;
      } ==
      Some (ciphertext', R.next_seq model.model_record.record_write))

let lemma_protected_record_count_positive
  (dir:direction)
  (msg:M.tls_message)
  : Lemma (protected_record_count dir msg > 0)
=
  match dir, msg with
  | CL.Sent, M.TlsApplicationData bytes ->
    S.lemma_application_data_record_count_len_positive (B.length bytes)
  | _, _ -> ()

let lemma_sent_event_seal_projection_intro
  (model:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  (aad:B.bytes)
  (plaintext:B.bytes)
  (ciphertext:B.bytes)
  : Lemma
      (requires
        network_message_is_cleartext CL.Sent msg == false /\
        protected_record_count CL.Sent msg == 1 /\
        W.parse_record raw == Some (T.Application_data, ciphertext, B.length raw) /\
        Seq.equal aad (record_header_aad raw) /\
        Seq.equal plaintext (sent_tls_inner_plaintext_fragment msg) /\
        R.seal
          model.model_record.record_write
          aad
          {
            R.content_type = T.Application_data;
            R.fragment = plaintext;
          } ==
          Some (ciphertext, R.next_seq model.model_record.record_write))
      (ensures sent_event_seal_projection
        model
        (ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = msg;
        })
        raw)
=
  Seq.lemma_eq_elim plaintext (sent_tls_inner_plaintext_fragment msg);
  lemma_sent_single_protected_message_seal_intro model msg raw aad ciphertext

let lemma_received_record_opened_from_sent_single_protected_message_seal
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write == receiver.model_record.record_read /\
        sent_single_protected_message_seal sender msg raw)
      (ensures
        exists outer_fragment.
          W.parse_record raw ==
            Some (T.Application_data, outer_fragment, B.length raw) /\
          received_record_opened
            receiver
            raw
            outer_fragment
            (sent_tls_inner_plaintext_fragment msg))
=
  eliminate exists (ciphertext:B.bytes).
    W.parse_record raw == Some (T.Application_data, ciphertext, B.length raw) /\
    R.seal
      sender.model_record.record_write
      (record_header_aad raw)
      {
        R.content_type = T.Application_data;
        R.fragment = sent_tls_inner_plaintext_fragment msg;
      } ==
      Some (ciphertext, R.next_seq sender.model_record.record_write)
  with
  ( let st = sender.model_record.record_write in
    let aad = record_header_aad raw in
    let pt = {
      R.content_type = T.Application_data;
      R.fragment = sent_tls_inner_plaintext_fragment msg;
    } in
    match st.R.key, st.R.static_iv with
    | Some _, Some _ ->
      R.lemma_open_record_after_seal st aad pt;
      assert (R.open_record st aad ciphertext ==
        Some (sent_tls_inner_plaintext_fragment msg, R.next_seq st));
      assert (st == receiver.model_record.record_read);
      assert (R.open_record
        receiver.model_record.record_read
        (record_header_aad raw)
        ciphertext ==
        Some (sent_tls_inner_plaintext_fragment msg, R.next_seq st));
      assert (received_record_opened
        receiver
        raw
        ciphertext
        (sent_tls_inner_plaintext_fragment msg));
      assert (exists outer_fragment.
        W.parse_record raw ==
          Some (T.Application_data, outer_fragment, B.length raw) /\
        received_record_opened
          receiver
          raw
          outer_fragment
          (sent_tls_inner_plaintext_fragment msg))
    | _, _ ->
      assert False )

let lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write == receiver.model_record.record_read /\
        sent_single_protected_message_seal sender msg raw /\
        (let (content_type, fragment) = W.serialize_tls_message msg in
         W.parse_tls_message content_type fragment == Some msg))
      (ensures received_single_protected_message_decode receiver msg raw)
=
  lemma_received_record_opened_from_sent_single_protected_message_seal
    sender
    receiver
    msg
    raw;
  eliminate exists (outer_fragment:B.bytes).
    W.parse_record raw ==
      Some (T.Application_data, outer_fragment, B.length raw) /\
    received_record_opened
      receiver
      raw
      outer_fragment
      (sent_tls_inner_plaintext_fragment msg)
  with
  ( let (content_type, fragment) = W.serialize_tls_message msg in
    let plaintext = { M.content_type = content_type; M.fragment = fragment } in
    assert (sent_tls_inner_plaintext_fragment msg ==
            W.serialize_plaintext plaintext);
    W.lemma_parse_plaintext_serialize_plaintext plaintext;
    assert (W.parse_plaintext (sent_tls_inner_plaintext_fragment msg) ==
            Some plaintext);
    W.lemma_parse_record_implies_parse_record_wire raw;
    assert (W.parse_record_wire raw ==
      Some (T.Application_data, outer_fragment, B.length raw));
    assert (received_record_opened
      receiver
      raw
      outer_fragment
      (sent_tls_inner_plaintext_fragment msg));
    assert (W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
      Some msg);
    introduce exists (outer_fragment':B.bytes) (opened:B.bytes) (plaintext':M.plaintext).
      W.parse_record_wire raw ==
        Some (T.Application_data, outer_fragment', B.length raw) /\
      received_record_opened receiver raw outer_fragment' opened /\
      W.parse_plaintext opened == Some plaintext' /\
      W.parse_tls_message plaintext'.M.content_type plaintext'.M.fragment ==
        Some msg
    with outer_fragment (sent_tls_inner_plaintext_fragment msg) plaintext
    and () )

#restart-solver
let lemma_received_record_opened_from_sent_single_protected_message_seal_peer
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        sent_single_protected_message_seal sender msg raw)
      (ensures
        exists outer_fragment.
          W.parse_record raw ==
            Some (T.Application_data, outer_fragment, B.length raw) /\
          received_record_opened
            receiver
            raw
            outer_fragment
            (sent_tls_inner_plaintext_fragment msg))
=
  eliminate exists (ciphertext:B.bytes).
    W.parse_record raw == Some (T.Application_data, ciphertext, B.length raw) /\
    R.seal
      sender.model_record.record_write
      (record_header_aad raw)
      {
        R.content_type = T.Application_data;
        R.fragment = sent_tls_inner_plaintext_fragment msg;
      } ==
      Some (ciphertext, R.next_seq sender.model_record.record_write)
  with
  ( let write_st = sender.model_record.record_write in
    let read_st = receiver.model_record.record_read in
    let aad = record_header_aad raw in
    let pt = {
      R.content_type = T.Application_data;
      R.fragment = sent_tls_inner_plaintext_fragment msg;
    } in
    match
      write_st.R.key,
      write_st.R.static_iv,
      read_st.R.key,
      read_st.R.static_iv
    with
    | Some write_key, Some write_iv, Some read_key, Some read_iv ->
      assert (record_direction_material write_st ==
        Some { record_material_alg = write_st.R.alg;
               record_material_key = write_key; record_material_iv = write_iv });
      assert (record_direction_material read_st ==
        Some { record_material_alg = read_st.R.alg;
               record_material_key = read_key; record_material_iv = read_iv });
      assert (write_st.R.alg == read_st.R.alg);
      assert (Seq.equal write_key read_key);
      assert (Seq.equal write_iv read_iv);
      R.lemma_open_record_after_seal_peer write_st read_st aad pt;
      assert (R.open_record read_st aad ciphertext ==
        Some (sent_tls_inner_plaintext_fragment msg, R.next_seq read_st));
      assert (received_record_opened
        receiver
        raw
        ciphertext
        (sent_tls_inner_plaintext_fragment msg));
      assert (exists outer_fragment.
        W.parse_record raw ==
          Some (T.Application_data, outer_fragment, B.length raw) /\
        received_record_opened
          receiver
          raw
          outer_fragment
          (sent_tls_inner_plaintext_fragment msg))
    | _, _, _, _ ->
      assert False )

let lemma_received_single_protected_message_decode_from_sent_single_protected_message_seal_peer
  (sender:connection_model)
  (receiver:connection_model)
  (msg:M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.model_record.record_write.R.seq ==
          receiver.model_record.record_read.R.seq /\
        (match
          record_direction_material sender.model_record.record_write,
          record_direction_material receiver.model_record.record_read
        with
        | Some sender_write, Some receiver_read ->
          record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        sent_single_protected_message_seal sender msg raw /\
        (let (content_type, fragment) = W.serialize_tls_message msg in
         W.parse_tls_message content_type fragment == Some msg))
      (ensures received_single_protected_message_decode receiver msg raw)
=
  lemma_received_record_opened_from_sent_single_protected_message_seal_peer
    sender
    receiver
    msg
    raw;
  eliminate exists (outer_fragment:B.bytes).
    W.parse_record raw ==
      Some (T.Application_data, outer_fragment, B.length raw) /\
    received_record_opened
      receiver
      raw
      outer_fragment
      (sent_tls_inner_plaintext_fragment msg)
  with
  ( let (content_type, fragment) = W.serialize_tls_message msg in
    let plaintext = { M.content_type = content_type; M.fragment = fragment } in
    assert (sent_tls_inner_plaintext_fragment msg ==
            W.serialize_plaintext plaintext);
    W.lemma_parse_plaintext_serialize_plaintext plaintext;
    assert (W.parse_plaintext (sent_tls_inner_plaintext_fragment msg) ==
            Some plaintext);
    W.lemma_parse_record_implies_parse_record_wire raw;
    assert (W.parse_record_wire raw ==
      Some (T.Application_data, outer_fragment, B.length raw));
    assert (received_record_opened
      receiver
      raw
      outer_fragment
      (sent_tls_inner_plaintext_fragment msg));
    assert (W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
      Some msg);
    introduce exists (outer_fragment':B.bytes) (opened:B.bytes) (plaintext':M.plaintext).
      W.parse_record_wire raw ==
        Some (T.Application_data, outer_fragment', B.length raw) /\
      received_record_opened receiver raw outer_fragment' opened /\
      W.parse_plaintext opened == Some plaintext' /\
      W.parse_tls_message plaintext'.M.content_type plaintext'.M.fragment ==
        Some msg
    with outer_fragment (sent_tls_inner_plaintext_fragment msg) plaintext
    and () )

let lemma_network_message_raw_delta_legal_protected_single_parse_record
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false /\
        protected_record_count msg.CL.message_direction msg.CL.message_value == 1)
      (ensures exists fragment.
        W.parse_record raw == Some (T.Application_data, fragment, B.length raw))
=
  assert (raw_records_exactly raw T.Application_data 1);
  lemma_raw_records_exactly_one_parse_record raw T.Application_data

let lemma_network_message_raw_delta_legal_protected_parse_prefix
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (T.Application_data, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw)
=
  lemma_protected_record_count_positive msg.CL.message_direction msg.CL.message_value;
  lemma_raw_records_exactly_nonempty_parse_record
    raw
    T.Application_data
    (protected_record_count msg.CL.message_direction msg.CL.message_value)

let lemma_network_message_raw_delta_legal_protected_decompose
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (T.Application_data, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        (let rest = Seq.slice raw consumed (B.length raw) in
         let tail = CL.parse_record_prefix_fuel (B.length raw) rest in
         CL.record_stream_serializes rest tail /\
         Seq.equal tail.CL.residual B.empty /\
         length tail.CL.values ==
           protected_record_count msg.CL.message_direction msg.CL.message_value - 1 /\
         all_records_outer_type T.Application_data tail.CL.values))
=
  lemma_protected_record_count_positive msg.CL.message_direction msg.CL.message_value;
  lemma_raw_records_exactly_nonempty_decompose
    raw
    T.Application_data
    (protected_record_count msg.CL.message_direction msg.CL.message_value)

let lemma_network_message_raw_delta_legal_protected_decompose_prefix
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false)
      (ensures exists fragment. exists (consumed:nat).
        W.parse_record raw == Some (T.Application_data, fragment, consumed) /\
        consumed > 0 /\
        consumed <= B.length raw /\
        raw_records_exactly
          (Seq.slice raw consumed (B.length raw))
          T.Application_data
          (protected_record_count msg.CL.message_direction msg.CL.message_value - 1))
=
  lemma_protected_record_count_positive msg.CL.message_direction msg.CL.message_value;
  lemma_raw_records_exactly_nonempty_decompose_prefix
    raw
    T.Application_data
    (protected_record_count msg.CL.message_direction msg.CL.message_value)

let lemma_network_message_raw_delta_legal_protected_segmented
  (model:connection_model)
  (msg:directed_message M.tls_message)
  (raw:B.bytes)
  : Lemma
      (requires
        network_message_raw_delta_legal model msg raw /\
        network_message_is_cleartext msg.CL.message_direction msg.CL.message_value == false)
      (ensures raw_records_segmented
        raw
        T.Application_data
        (protected_record_count msg.CL.message_direction msg.CL.message_value))
=
  lemma_raw_records_exactly_segmented
    raw
    T.Application_data
    (protected_record_count msg.CL.message_direction msg.CL.message_value)

let lemma_event_raw_delta_legal_protected_single_parse_record
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_single_raw_parse_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnProtectedHandshake step ->
    if step.protected_handshake_head
    then
      begin
        lemma_raw_records_exactly_one_parse_record
          raw_received
          T.Application_data;
        W.lemma_parse_record_implies_parse_record_wire raw_received
      end
    else ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else if protected_record_count msg.CL.message_direction msg.CL.message_value == 1
    then
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_single_parse_record model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_single_parse_record model msg raw_received;
        assert (exists fragment.
          W.parse_record raw_received ==
            Some (T.Application_data, fragment, B.length raw_received));
        W.lemma_parse_record_implies_parse_record_wire raw_received
    else ()

let lemma_event_raw_delta_legal_protected_parse_prefix
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_raw_parse_prefix_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnProtectedHandshake step ->
    if step.protected_handshake_head
    then
      begin
        lemma_raw_records_exactly_nonempty_parse_record
          raw_received
          T.Application_data
          1;
        W.lemma_parse_record_implies_parse_record_wire raw_received
      end
    else ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_parse_prefix model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_parse_prefix model msg raw_received;
        assert (exists fragment. exists (consumed:nat).
          W.parse_record raw_received ==
            Some (T.Application_data, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_received);
        W.lemma_parse_record_implies_parse_record_wire raw_received

let lemma_event_raw_delta_legal_protected_decompose_prefix
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_raw_decompose_prefix_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnProtectedHandshake step ->
    if step.protected_handshake_head
    then
      begin
        lemma_raw_records_exactly_nonempty_decompose_prefix
          raw_received
          T.Application_data
          1;
        W.lemma_parse_record_implies_parse_record_wire raw_received
      end
    else ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_decompose_prefix model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_decompose_prefix model msg raw_received;
        assert (exists fragment. exists (consumed:nat).
          W.parse_record raw_received ==
            Some (T.Application_data, fragment, consumed) /\
          consumed > 0 /\
          consumed <= B.length raw_received /\
          raw_records_exactly
            (Seq.slice raw_received consumed (B.length raw_received))
            T.Application_data
            (protected_record_count msg.CL.message_direction msg.CL.message_value - 1));
        W.lemma_parse_record_implies_parse_record_wire raw_received

let lemma_event_raw_delta_legal_protected_segmented
  (model:connection_model)
  (ev:conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires event_raw_delta_legal model ev raw_sent raw_received)
      (ensures event_protected_raw_segmented_success ev raw_sent raw_received)
=
  match ev with
  | ConnLocalEvent _ -> ()
  | ConnProtectedHandshake step ->
    if step.protected_handshake_head
    then
      lemma_raw_records_exactly_segmented
        raw_received
        T.Application_data
        1
    else ()
  | ConnNetworkEvent msg ->
    if network_message_is_cleartext msg.CL.message_direction msg.CL.message_value
    then ()
    else
      match msg.CL.message_direction with
      | CL.Sent ->
        lemma_network_message_raw_delta_legal_protected_segmented model msg raw_sent
      | CL.Received ->
        lemma_network_message_raw_delta_legal_protected_segmented model msg raw_received

#push-options "--z3rlimit 200"
let lemma_conn_events_raw_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_raw_replay model1 rest tail_sent tail_received final_model)
      (ensures
        conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_raw_replay model1 rest tail_sent tail_received' final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_raw_replay model1 rest tail_sent' tail_received' final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay model1 rest tail_sent' tail_received' final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay model1 rest tail_sent' tail_received' final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay model1' rest tail_sent' tail_received' final_model)
    model1;
  assert_norm (
    conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_raw_replay model1' rest tail_sent' tail_received' final_model));
  assert (conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model)

#pop-options
let rec lemma_conn_events_raw_replay_snoc
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (model1:connection_model)
  (ev:conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (model2:connection_model)
  : Lemma
      (requires
        conn_events_raw_replay model events raw_sent raw_received model1 /\
        legal_event model1 ev /\
        step_model model1 ev == Some model2 /\
        event_raw_delta_legal model1 ev delta_sent delta_received)
      (ensures
        conn_events_raw_replay
          model
          (events @ [ev])
          (B.append raw_sent delta_sent)
          (B.append raw_received delta_received)
          model2)
      (decreases events)
=
  match events with
  | [] ->
    Seq.lemma_eq_elim raw_sent B.empty;
    Seq.lemma_eq_elim raw_received B.empty;
    CL.lemma_append_empty_left delta_sent;
    CL.lemma_append_empty_left delta_received;
    CL.lemma_append_empty_right delta_sent;
    CL.lemma_append_empty_right delta_received;
    assert (model1 == model);
    assert (legal_event model ev);
    assert (step_model model ev == Some model2);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent B.empty));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received B.empty));
    assert (conn_events_raw_replay model2 [] B.empty B.empty model2);
    lemma_conn_events_raw_replay_cons
      model
      ev
      []
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model2
      delta_sent
      delta_received
      B.empty
      B.empty
  | ev0 :: rest ->
    assert_norm (
      conn_events_raw_replay model (ev0 :: rest) raw_sent raw_received model1 ==
      (exists (model0':connection_model)
              (delta_sent0:B.bytes)
              (delta_received0:B.bytes)
              (tail_sent:B.bytes)
              (tail_received:B.bytes).
         legal_event model ev0 /\
         step_model model ev0 == Some model0' /\
         event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
         Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
         Seq.equal raw_received (B.append delta_received0 tail_received) /\
         conn_events_raw_replay model0' rest tail_sent tail_received model1));
    assert (exists (model0':connection_model)
                   (delta_sent0:B.bytes)
                   (delta_received0:B.bytes)
                   (tail_sent:B.bytes)
                   (tail_received:B.bytes).
       legal_event model ev0 /\
       step_model model ev0 == Some model0' /\
       event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
       Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
       Seq.equal raw_received (B.append delta_received0 tail_received) /\
       conn_events_raw_replay model0' rest tail_sent tail_received model1);
    let model0'_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model0' -> exists delta_sent0 delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let model0' : connection_model = model0'_w in
    assert (exists delta_sent0' delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0' delta_received0' /\
      Seq.equal raw_sent (B.append delta_sent0' tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_raw_replay model0' rest tail_sent' tail_received' model1);
    let delta_sent0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent0 -> exists delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let delta_sent0 : B.bytes = delta_sent0_w in
    assert (exists delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0' /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_raw_replay model0' rest tail_sent' tail_received' model1);
    let delta_received0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received0 -> exists tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let delta_received0 : B.bytes = delta_received0_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_raw_replay model0' rest tail_sent' tail_received' model1);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_raw_replay model0' rest tail_sent tail_received' model1);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_raw_replay model0' rest tail_sent tail_received model1) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev0);
    assert (step_model model ev0 == Some model0');
    assert (event_raw_delta_legal model ev0 delta_sent0 delta_received0);
    assert (Seq.equal raw_sent (B.append delta_sent0 tail_sent));
    assert (Seq.equal raw_received (B.append delta_received0 tail_received));
    assert (conn_events_raw_replay model0' rest tail_sent tail_received model1);
    lemma_conn_events_raw_replay_snoc
      model0'
      rest
      tail_sent
      tail_received
      model1
      ev
      delta_sent
      delta_received
      model2;
    Seq.lemma_eq_elim raw_sent (B.append delta_sent0 tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received0 tail_received);
    Seq.append_assoc delta_sent0 tail_sent delta_sent;
    Seq.append_assoc delta_received0 tail_received delta_received;
    assert (Seq.equal
      (B.append (B.append delta_sent0 tail_sent) delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append (B.append delta_received0 tail_received) delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    assert (conn_events_raw_replay
      model0'
      (rest @ [ev])
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)
      model2);
    assert (events @ [ev] == ev0 :: (rest @ [ev]));
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    lemma_conn_events_raw_replay_cons
      model
      ev0
      (rest @ [ev])
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model0'
      delta_sent0
      delta_received0
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)

#push-options "--z3rlimit 400"
let lemma_conn_events_protected_raw_segmented_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        event_protected_raw_segmented_success ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_protected_raw_segmented_replay
          model1
          rest
          tail_sent
          tail_received
          final_model)
      (ensures
        conn_events_protected_raw_segmented_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      event_protected_raw_segmented_success ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_protected_raw_segmented_replay
        model1
        rest
        tail_sent
        tail_received'
        final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        event_protected_raw_segmented_success ev delta_sent delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_protected_raw_segmented_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        event_protected_raw_segmented_success ev delta_sent delta_received' /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_protected_raw_segmented_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        event_protected_raw_segmented_success ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_protected_raw_segmented_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        event_protected_raw_segmented_success ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_protected_raw_segmented_replay
          model1'
          rest
          tail_sent'
          tail_received'
          final_model)
    model1;
  assert_norm (
    conn_events_protected_raw_segmented_replay
      model
      (ev :: rest)
      raw_sent
      raw_received
      final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1' /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      event_protected_raw_segmented_success ev delta_sent' delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_protected_raw_segmented_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model));
  assert (conn_events_protected_raw_segmented_replay
    model
    (ev :: rest)
    raw_sent
    raw_received
    final_model)

#pop-options
#restart-solver
let rec lemma_conn_events_raw_replay_protected_segmented
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_raw_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (ensures
        conn_events_protected_raw_segmented_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (decreases events)
=
  match events with
  | [] ->
    ()
  | ev :: rest ->
    assert_norm (
      conn_events_raw_replay model (ev :: rest) raw_sent raw_received final_model ==
      (exists (model1':connection_model)
              (delta_sent':B.bytes)
              (delta_received':B.bytes)
              (tail_sent':B.bytes)
              (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_raw_replay model1' rest tail_sent' tail_received' final_model));
    assert (exists (model1':connection_model)
                   (delta_sent':B.bytes)
                   (delta_received':B.bytes)
                   (tail_sent':B.bytes)
                   (tail_received':B.bytes).
      legal_event model ev /\
      step_model model ev == Some model1' /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_raw_replay model1' rest tail_sent' tail_received' final_model);
    let model1_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model1 -> exists delta_sent delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let model1 : connection_model = model1_w in
    assert (exists delta_sent' delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_raw_replay model1 rest tail_sent' tail_received' final_model);
    let delta_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent -> exists delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let delta_sent : B.bytes = delta_sent_w in
    assert (exists delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received' /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_raw_replay model1 rest tail_sent' tail_received' final_model);
    let delta_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received -> exists tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let delta_received : B.bytes = delta_received_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_raw_replay model1 rest tail_sent' tail_received' final_model);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_raw_replay model1 rest tail_sent tail_received' final_model);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_raw_replay model1 rest tail_sent tail_received final_model) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev);
    assert (step_model model ev == Some model1);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (Seq.equal raw_sent (B.append delta_sent tail_sent));
    assert (Seq.equal raw_received (B.append delta_received tail_received));
    assert (conn_events_raw_replay model1 rest tail_sent tail_received final_model);
    lemma_event_raw_delta_legal_protected_segmented
      model
      ev
      delta_sent
      delta_received;
    lemma_conn_events_raw_replay_protected_segmented
      model1
      rest
      tail_sent
      tail_received
      final_model;
    lemma_conn_events_protected_raw_segmented_replay_cons
      model
      ev
      rest
      raw_sent
      raw_received
      final_model
      model1
      delta_sent
      delta_received
      tail_sent
      tail_received

let lemma_connection_state_protected_raw_segmented_replay
  (st:connection_state)
  : Lemma
      (requires connection_state_raw_event_replay_consistent st)
      (ensures connection_state_protected_raw_segmented_replay_consistent st)
=
  lemma_conn_events_raw_replay_protected_segmented
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

#push-options "--z3rlimit 200"
let lemma_conn_events_sent_seal_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_sent_seal_replay model1 rest tail_sent tail_received final_model)
      (ensures
        conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_sent_seal_replay model1 rest tail_sent tail_received' final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_sent_seal_replay model1 rest tail_sent' tail_received' final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay model1 rest tail_sent' tail_received' final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay model1 rest tail_sent' tail_received' final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay model1' rest tail_sent' tail_received' final_model)
    model1;
  assert_norm (
    conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_replay model1' rest tail_sent' tail_received' final_model));
  assert (conn_events_sent_seal_replay model (ev :: rest) raw_sent raw_received final_model)

#pop-options
#push-options "--z3rlimit 200"
let lemma_conn_events_sent_seal_key_schedule_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
       legal_event model ev /\
       step_model model ev == Some model1 /\
       event_raw_delta_legal model ev delta_sent delta_received /\
       sent_event_nonempty_seal_projection model ev delta_sent /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent tail_sent) /\
       Seq.equal raw_received (B.append delta_received tail_received) /\
       conn_events_sent_seal_key_schedule_replay
         model1
         rest
         tail_sent
         tail_received
         final_model)
      (ensures
       conn_events_sent_seal_key_schedule_replay
         model
         (ev :: rest)
         raw_sent
         raw_received
         final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      record_write_key_schedule_projection model /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_sent_seal_key_schedule_replay
       model1
       rest
       tail_sent
       tail_received'
       final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1 /\
       event_raw_delta_legal model ev delta_sent delta_received /\
       sent_event_nonempty_seal_projection model ev delta_sent /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent tail_sent') /\
       Seq.equal raw_received (B.append delta_received tail_received') /\
       conn_events_sent_seal_key_schedule_replay
         model1
         rest
         tail_sent'
         tail_received'
         final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1 /\
       event_raw_delta_legal model ev delta_sent delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_key_schedule_replay
         model1
         rest
         tail_sent'
         tail_received'
         final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1 /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_key_schedule_replay
         model1
         rest
         tail_sent'
         tail_received'
         final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_key_schedule_replay
         model1'
         rest
         tail_sent'
         tail_received'
         final_model)
    model1;
  assert_norm (
    conn_events_sent_seal_key_schedule_replay
      model
      (ev :: rest)
      raw_sent
      raw_received
      final_model ==
    (exists (model1':connection_model)
           (delta_sent':B.bytes)
           (delta_received':B.bytes)
           (tail_sent':B.bytes)
           (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       record_write_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_key_schedule_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model));
  assert (conn_events_sent_seal_key_schedule_replay
    model
    (ev :: rest)
    raw_sent
    raw_received
    final_model)

#pop-options
let rec lemma_conn_events_sent_seal_replay_strengthen
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
       conn_events_sent_seal_replay
         model
         events
         raw_sent
         raw_received
         final_model /\
       model.model_config.config_role == ClientEndpoint /\
       model_record_keys_consistent model)
      (ensures
       conn_events_sent_seal_key_schedule_replay
         model
         events
         raw_sent
         raw_received
         final_model)
      (decreases events)
=
  match events with
  | [] ->
    ()
  | ev :: rest ->
    assert_norm (
      conn_events_sent_seal_replay
       model
       (ev :: rest)
       raw_sent
       raw_received
       final_model ==
      (exists (model1':connection_model)
             (delta_sent':B.bytes)
             (delta_received':B.bytes)
             (tail_sent':B.bytes)
             (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        sent_event_nonempty_seal_projection model ev delta_sent' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_sent_seal_replay
          model1'
          rest
          tail_sent'
          tail_received'
          final_model));
    assert (exists (model1':connection_model)
                  (delta_sent':B.bytes)
                  (delta_received':B.bytes)
                  (tail_sent':B.bytes)
                  (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       sent_event_nonempty_seal_projection model ev delta_sent' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_sent_seal_replay
        model1'
        rest
        tail_sent'
        tail_received'
        final_model);
    let model1_w =
      ID.indefinite_description_ghost
       connection_model
       (fun model1 -> exists delta_sent delta_received tail_sent tail_received.
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let model1 : connection_model = model1_w in
    assert (exists delta_sent' delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      sent_event_nonempty_seal_projection model ev delta_sent' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_sent_seal_replay
       model1
       rest
       tail_sent'
       tail_received'
       final_model);
    let delta_sent_w =
      ID.indefinite_description_ghost
       B.bytes
       (fun delta_sent -> exists delta_received tail_sent tail_received.
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let delta_sent : B.bytes = delta_sent_w in
    assert (exists delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received' /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_sent_seal_replay
       model1
       rest
       tail_sent'
       tail_received'
       final_model);
    let delta_received_w =
      ID.indefinite_description_ghost
       B.bytes
       (fun delta_received -> exists tail_sent tail_received.
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let delta_received : B.bytes = delta_received_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_sent_seal_replay
       model1
       rest
       tail_sent'
       tail_received'
       final_model);
    let tail_sent_w =
      ID.indefinite_description_ghost
       B.bytes
       (fun tail_sent -> exists tail_received.
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      sent_event_nonempty_seal_projection model ev delta_sent /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_sent_seal_replay
       model1
       rest
       tail_sent
       tail_received'
       final_model);
    let tail_received_w =
      ID.indefinite_description_ghost
       B.bytes
       (fun tail_received ->
         legal_event model ev /\
         step_model model ev == Some model1 /\
         event_raw_delta_legal model ev delta_sent delta_received /\
         sent_event_nonempty_seal_projection model ev delta_sent /\
         Seq.equal raw_sent (B.append delta_sent tail_sent) /\
         Seq.equal raw_received (B.append delta_received tail_received) /\
         conn_events_sent_seal_replay
           model1
           rest
           tail_sent
           tail_received
           final_model) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev);
    assert (step_model model ev == Some model1);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (sent_event_nonempty_seal_projection model ev delta_sent);
    assert (Seq.equal raw_sent (B.append delta_sent tail_sent));
    assert (Seq.equal raw_received (B.append delta_received tail_received));
    assert (conn_events_sent_seal_replay
      model1
      rest
      tail_sent
      tail_received
      final_model);
    assert (model.model_config.config_role == ClientEndpoint);
    lemma_model_record_keys_consistent_record_write_key_schedule_projection model;
    lemma_step_model_record_keys_consistent model ev model1;
    assert (model_record_keys_consistent model1);
    assert_norm (model_record_keys_consistent model1 ==
      (model1.model_config.config_role == ClientEndpoint /\
       model_record_keys_consistent_for_role ClientEndpoint model1));
    assert (model1.model_config.config_role == ClientEndpoint);
    lemma_conn_events_sent_seal_replay_strengthen
      model1
      rest
      tail_sent
      tail_received
      final_model;
    lemma_conn_events_sent_seal_key_schedule_replay_cons
      model
      ev
      rest
      raw_sent
      raw_received
      final_model
      model1
      delta_sent
      delta_received
      tail_sent
      tail_received

let rec lemma_conn_events_sent_seal_replay_snoc
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (model1:connection_model)
  (ev:conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (model2:connection_model)
  : Lemma
      (requires
        conn_events_sent_seal_replay model events raw_sent raw_received model1 /\
        legal_event model1 ev /\
        step_model model1 ev == Some model2 /\
        event_raw_delta_legal model1 ev delta_sent delta_received /\
        sent_event_nonempty_seal_projection model1 ev delta_sent)
      (ensures
        conn_events_sent_seal_replay
          model
          (events @ [ev])
          (B.append raw_sent delta_sent)
          (B.append raw_received delta_received)
          model2)
      (decreases events)
=
  match events with
  | [] ->
    Seq.lemma_eq_elim raw_sent B.empty;
    Seq.lemma_eq_elim raw_received B.empty;
    CL.lemma_append_empty_left delta_sent;
    CL.lemma_append_empty_left delta_received;
    CL.lemma_append_empty_right delta_sent;
    CL.lemma_append_empty_right delta_received;
    assert (model1 == model);
    assert (legal_event model ev);
    assert (step_model model ev == Some model2);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (sent_event_nonempty_seal_projection model ev delta_sent);
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent B.empty));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received B.empty));
    assert (conn_events_sent_seal_replay model2 [] B.empty B.empty model2);
    lemma_conn_events_sent_seal_replay_cons
      model
      ev
      []
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model2
      delta_sent
      delta_received
      B.empty
      B.empty
  | ev0 :: rest ->
    assert_norm (
      conn_events_sent_seal_replay model (ev0 :: rest) raw_sent raw_received model1 ==
      (exists (model0':connection_model)
              (delta_sent0:B.bytes)
              (delta_received0:B.bytes)
              (tail_sent:B.bytes)
              (tail_received:B.bytes).
         legal_event model ev0 /\
         step_model model ev0 == Some model0' /\
         event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
         sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
         Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
         Seq.equal raw_received (B.append delta_received0 tail_received) /\
         conn_events_sent_seal_replay model0' rest tail_sent tail_received model1));
    assert (exists (model0':connection_model)
                   (delta_sent0:B.bytes)
                   (delta_received0:B.bytes)
                   (tail_sent:B.bytes)
                   (tail_received:B.bytes).
       legal_event model ev0 /\
       step_model model ev0 == Some model0' /\
       event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
       sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
       Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
       Seq.equal raw_received (B.append delta_received0 tail_received) /\
       conn_events_sent_seal_replay model0' rest tail_sent tail_received model1);
    let model0'_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model0' -> exists delta_sent0 delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let model0' : connection_model = model0'_w in
    assert (exists delta_sent0' delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0' delta_received0' /\
      sent_event_nonempty_seal_projection model ev0 delta_sent0' /\
      Seq.equal raw_sent (B.append delta_sent0' tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_sent_seal_replay model0' rest tail_sent' tail_received' model1);
    let delta_sent0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent0 -> exists delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let delta_sent0 : B.bytes = delta_sent0_w in
    assert (exists delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0' /\
      sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_sent_seal_replay model0' rest tail_sent' tail_received' model1);
    let delta_received0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received0 -> exists tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let delta_received0 : B.bytes = delta_received0_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_sent_seal_replay model0' rest tail_sent' tail_received' model1);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_sent_seal_replay model0' rest tail_sent tail_received' model1);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          sent_event_nonempty_seal_projection model ev0 delta_sent0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_sent_seal_replay model0' rest tail_sent tail_received model1) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev0);
    assert (step_model model ev0 == Some model0');
    assert (event_raw_delta_legal model ev0 delta_sent0 delta_received0);
    assert (sent_event_nonempty_seal_projection model ev0 delta_sent0);
    assert (Seq.equal raw_sent (B.append delta_sent0 tail_sent));
    assert (Seq.equal raw_received (B.append delta_received0 tail_received));
    assert (conn_events_sent_seal_replay model0' rest tail_sent tail_received model1);
    lemma_conn_events_sent_seal_replay_snoc
      model0'
      rest
      tail_sent
      tail_received
      model1
      ev
      delta_sent
      delta_received
      model2;
    Seq.lemma_eq_elim raw_sent (B.append delta_sent0 tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received0 tail_received);
    Seq.append_assoc delta_sent0 tail_sent delta_sent;
    Seq.append_assoc delta_received0 tail_received delta_received;
    assert (Seq.equal
      (B.append (B.append delta_sent0 tail_sent) delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append (B.append delta_received0 tail_received) delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    assert (conn_events_sent_seal_replay
      model0'
      (rest @ [ev])
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)
      model2);
    assert (events @ [ev] == ev0 :: (rest @ [ev]));
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    lemma_conn_events_sent_seal_replay_cons
      model
      ev0
      (rest @ [ev])
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model0'
      delta_sent0
      delta_received0
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)

#restart-solver
#push-options "--z3rlimit 200"
let lemma_conn_events_received_decode_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_received_decode_replay model1 rest tail_sent tail_received final_model)
      (ensures
        conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_received_decode_replay model1 rest tail_sent tail_received' final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_received_decode_replay model1 rest tail_sent' tail_received' final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_replay model1 rest tail_sent' tail_received' final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_replay model1 rest tail_sent' tail_received' final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_replay model1' rest tail_sent' tail_received' final_model)
    model1;
  assert_norm (
    conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       received_event_nonempty_decode_projection model ev delta_received' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_received_decode_replay model1' rest tail_sent' tail_received' final_model));
  assert (conn_events_received_decode_replay model (ev :: rest) raw_sent raw_received final_model)

#pop-options
#push-options "--z3rlimit 200"
let lemma_conn_events_received_decode_key_schedule_replay_cons
  (model:connection_model)
  (ev:conn_event)
  (rest:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  (model1:connection_model)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (tail_sent:B.bytes)
  (tail_received:B.bytes)
  : Lemma
      (requires
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent tail_sent) /\
        Seq.equal raw_received (B.append delta_received tail_received) /\
        conn_events_received_decode_key_schedule_replay
          model1
          rest
          tail_sent
          tail_received
          final_model)
      (ensures
        conn_events_received_decode_key_schedule_replay
          model
          (ev :: rest)
          raw_sent
          raw_received
          final_model)
=
  FStar.Classical.exists_intro
    (fun tail_received' ->
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      record_read_key_schedule_projection model /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_received_decode_key_schedule_replay
        model1
        rest
        tail_sent
        tail_received'
        final_model)
    tail_received;
  FStar.Classical.exists_intro
    (fun tail_sent' ->
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model ev delta_received /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received tail_received') /\
        conn_events_received_decode_key_schedule_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    tail_sent;
  FStar.Classical.exists_intro
    (fun delta_received' ->
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_key_schedule_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    delta_received;
  FStar.Classical.exists_intro
    (fun delta_sent' ->
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1 /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_key_schedule_replay
          model1
          rest
          tail_sent'
          tail_received'
          final_model)
    delta_sent;
  FStar.Classical.exists_intro
    (fun model1' ->
      exists (delta_sent':B.bytes).
      exists (delta_received':B.bytes).
      exists (tail_sent':B.bytes).
      exists (tail_received':B.bytes).
        legal_event model ev /\
        step_model model ev == Some model1' /\
        event_raw_delta_legal model ev delta_sent' delta_received' /\
        received_event_nonempty_decode_projection model ev delta_received' /\
        record_read_key_schedule_projection model /\
        Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
        Seq.equal raw_received (B.append delta_received' tail_received') /\
        conn_events_received_decode_key_schedule_replay
          model1'
          rest
          tail_sent'
          tail_received'
          final_model)
    model1;
  assert_norm (
    conn_events_received_decode_key_schedule_replay
      model
      (ev :: rest)
      raw_sent
      raw_received
      final_model ==
    (exists (model1':connection_model)
            (delta_sent':B.bytes)
            (delta_received':B.bytes)
            (tail_sent':B.bytes)
            (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       received_event_nonempty_decode_projection model ev delta_received' /\
       record_read_key_schedule_projection model /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_received_decode_key_schedule_replay
         model1'
         rest
         tail_sent'
         tail_received'
         final_model));
  assert (conn_events_received_decode_key_schedule_replay
    model
    (ev :: rest)
    raw_sent
    raw_received
    final_model)

#pop-options
let rec lemma_conn_events_received_decode_replay_strengthen
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (final_model:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay
          model
          events
          raw_sent
          raw_received
          final_model /\
        model.model_config.config_role == ClientEndpoint /\
        model_record_keys_consistent model)
      (ensures
        conn_events_received_decode_key_schedule_replay
          model
          events
          raw_sent
          raw_received
          final_model)
      (decreases events)
=
  match events with
  | [] ->
    ()
  | ev :: rest ->
    assert_norm (
      conn_events_received_decode_replay
        model
        (ev :: rest)
        raw_sent
        raw_received
        final_model ==
      (exists (model1':connection_model)
              (delta_sent':B.bytes)
              (delta_received':B.bytes)
              (tail_sent':B.bytes)
              (tail_received':B.bytes).
         legal_event model ev /\
         step_model model ev == Some model1' /\
         event_raw_delta_legal model ev delta_sent' delta_received' /\
         received_event_nonempty_decode_projection model ev delta_received' /\
         Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
         Seq.equal raw_received (B.append delta_received' tail_received') /\
         conn_events_received_decode_replay
           model1'
           rest
           tail_sent'
           tail_received'
           final_model));
    assert (exists (model1':connection_model)
                   (delta_sent':B.bytes)
                   (delta_received':B.bytes)
                   (tail_sent':B.bytes)
                   (tail_received':B.bytes).
       legal_event model ev /\
       step_model model ev == Some model1' /\
       event_raw_delta_legal model ev delta_sent' delta_received' /\
       received_event_nonempty_decode_projection model ev delta_received' /\
       Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
       Seq.equal raw_received (B.append delta_received' tail_received') /\
       conn_events_received_decode_replay
         model1'
         rest
         tail_sent'
         tail_received'
         final_model);
    let model1_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model1 -> exists delta_sent delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let model1 : connection_model = model1_w in
    assert (exists delta_sent' delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent' delta_received' /\
      received_event_nonempty_decode_projection model ev delta_received' /\
      Seq.equal raw_sent (B.append delta_sent' tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent'
        tail_received'
        final_model);
    let delta_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent -> exists delta_received tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let delta_sent : B.bytes = delta_sent_w in
    assert (exists delta_received' tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received' /\
      received_event_nonempty_decode_projection model ev delta_received' /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received' tail_received') /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent'
        tail_received'
        final_model);
    let delta_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received -> exists tail_sent tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let delta_received : B.bytes = delta_received_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent') /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent'
        tail_received'
        final_model);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev /\
      step_model model ev == Some model1 /\
      event_raw_delta_legal model ev delta_sent delta_received /\
      received_event_nonempty_decode_projection model ev delta_received /\
      Seq.equal raw_sent (B.append delta_sent tail_sent) /\
      Seq.equal raw_received (B.append delta_received tail_received') /\
      conn_events_received_decode_replay
        model1
        rest
        tail_sent
        tail_received'
        final_model);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev /\
          step_model model ev == Some model1 /\
          event_raw_delta_legal model ev delta_sent delta_received /\
          received_event_nonempty_decode_projection model ev delta_received /\
          Seq.equal raw_sent (B.append delta_sent tail_sent) /\
          Seq.equal raw_received (B.append delta_received tail_received) /\
          conn_events_received_decode_replay
            model1
            rest
            tail_sent
            tail_received
            final_model) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev);
    assert (step_model model ev == Some model1);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (received_event_nonempty_decode_projection model ev delta_received);
    assert (Seq.equal raw_sent (B.append delta_sent tail_sent));
    assert (Seq.equal raw_received (B.append delta_received tail_received));
    assert (conn_events_received_decode_replay
      model1
      rest
      tail_sent
      tail_received
      final_model);
    assert (model.model_config.config_role == ClientEndpoint);
    lemma_model_record_keys_consistent_record_read_key_schedule_projection model;
    lemma_step_model_record_keys_consistent model ev model1;
    assert (model_record_keys_consistent model1);
    assert_norm (model_record_keys_consistent model1 ==
      (model1.model_config.config_role == ClientEndpoint /\
       model_record_keys_consistent_for_role ClientEndpoint model1));
    assert (model1.model_config.config_role == ClientEndpoint);
    lemma_conn_events_received_decode_replay_strengthen
      model1
      rest
      tail_sent
      tail_received
      final_model;
    lemma_conn_events_received_decode_key_schedule_replay_cons
      model
      ev
      rest
      raw_sent
      raw_received
      final_model
      model1
      delta_sent
      delta_received
      tail_sent
      tail_received

let rec lemma_conn_events_received_decode_replay_snoc
  (model:connection_model)
  (events:list conn_event)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  (model1:connection_model)
  (ev:conn_event)
  (delta_sent:B.bytes)
  (delta_received:B.bytes)
  (model2:connection_model)
  : Lemma
      (requires
        conn_events_received_decode_replay model events raw_sent raw_received model1 /\
        legal_event model1 ev /\
        step_model model1 ev == Some model2 /\
        event_raw_delta_legal model1 ev delta_sent delta_received /\
        received_event_nonempty_decode_projection model1 ev delta_received)
      (ensures
        conn_events_received_decode_replay
          model
          (events @ [ev])
          (B.append raw_sent delta_sent)
          (B.append raw_received delta_received)
          model2)
      (decreases events)
=
  match events with
  | [] ->
    Seq.lemma_eq_elim raw_sent B.empty;
    Seq.lemma_eq_elim raw_received B.empty;
    CL.lemma_append_empty_left delta_sent;
    CL.lemma_append_empty_left delta_received;
    CL.lemma_append_empty_right delta_sent;
    CL.lemma_append_empty_right delta_received;
    assert (model1 == model);
    assert (legal_event model ev);
    assert (step_model model ev == Some model2);
    assert (event_raw_delta_legal model ev delta_sent delta_received);
    assert (received_event_nonempty_decode_projection model ev delta_received);
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent B.empty));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received B.empty));
    assert (conn_events_received_decode_replay model2 [] B.empty B.empty model2);
    lemma_conn_events_received_decode_replay_cons
      model
      ev
      []
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model2
      delta_sent
      delta_received
      B.empty
      B.empty
  | ev0 :: rest ->
    assert_norm (
      conn_events_received_decode_replay model (ev0 :: rest) raw_sent raw_received model1 ==
      (exists (model0':connection_model)
              (delta_sent0:B.bytes)
              (delta_received0:B.bytes)
              (tail_sent:B.bytes)
              (tail_received:B.bytes).
         legal_event model ev0 /\
         step_model model ev0 == Some model0' /\
         event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
         received_event_nonempty_decode_projection model ev0 delta_received0 /\
         Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
         Seq.equal raw_received (B.append delta_received0 tail_received) /\
         conn_events_received_decode_replay model0' rest tail_sent tail_received model1));
    assert (exists (model0':connection_model)
                   (delta_sent0:B.bytes)
                   (delta_received0:B.bytes)
                   (tail_sent:B.bytes)
                   (tail_received:B.bytes).
       legal_event model ev0 /\
       step_model model ev0 == Some model0' /\
       event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
       received_event_nonempty_decode_projection model ev0 delta_received0 /\
       Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
       Seq.equal raw_received (B.append delta_received0 tail_received) /\
       conn_events_received_decode_replay model0' rest tail_sent tail_received model1);
    let model0'_w =
      ID.indefinite_description_ghost
        connection_model
        (fun model0' -> exists delta_sent0 delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let model0' : connection_model = model0'_w in
    assert (exists delta_sent0' delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0' delta_received0' /\
      received_event_nonempty_decode_projection model ev0 delta_received0' /\
      Seq.equal raw_sent (B.append delta_sent0' tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_received_decode_replay model0' rest tail_sent' tail_received' model1);
    let delta_sent0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_sent0 -> exists delta_received0 tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let delta_sent0 : B.bytes = delta_sent0_w in
    assert (exists delta_received0' tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0' /\
      received_event_nonempty_decode_projection model ev0 delta_received0' /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0' tail_received') /\
      conn_events_received_decode_replay model0' rest tail_sent' tail_received' model1);
    let delta_received0_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun delta_received0 -> exists tail_sent tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let delta_received0 : B.bytes = delta_received0_w in
    assert (exists tail_sent' tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      received_event_nonempty_decode_projection model ev0 delta_received0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent') /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_received_decode_replay model0' rest tail_sent' tail_received' model1);
    let tail_sent_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_sent -> exists tail_received.
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let tail_sent : B.bytes = tail_sent_w in
    assert (exists tail_received'.
      legal_event model ev0 /\
      step_model model ev0 == Some model0' /\
      event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
      received_event_nonempty_decode_projection model ev0 delta_received0 /\
      Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
      Seq.equal raw_received (B.append delta_received0 tail_received') /\
      conn_events_received_decode_replay model0' rest tail_sent tail_received' model1);
    let tail_received_w =
      ID.indefinite_description_ghost
        B.bytes
        (fun tail_received ->
          legal_event model ev0 /\
          step_model model ev0 == Some model0' /\
          event_raw_delta_legal model ev0 delta_sent0 delta_received0 /\
          received_event_nonempty_decode_projection model ev0 delta_received0 /\
          Seq.equal raw_sent (B.append delta_sent0 tail_sent) /\
          Seq.equal raw_received (B.append delta_received0 tail_received) /\
          conn_events_received_decode_replay model0' rest tail_sent tail_received model1) in
    let tail_received : B.bytes = tail_received_w in
    assert (legal_event model ev0);
    assert (step_model model ev0 == Some model0');
    assert (event_raw_delta_legal model ev0 delta_sent0 delta_received0);
    assert (received_event_nonempty_decode_projection model ev0 delta_received0);
    assert (Seq.equal raw_sent (B.append delta_sent0 tail_sent));
    assert (Seq.equal raw_received (B.append delta_received0 tail_received));
    assert (conn_events_received_decode_replay model0' rest tail_sent tail_received model1);
    lemma_conn_events_received_decode_replay_snoc
      model0'
      rest
      tail_sent
      tail_received
      model1
      ev
      delta_sent
      delta_received
      model2;
    Seq.lemma_eq_elim raw_sent (B.append delta_sent0 tail_sent);
    Seq.lemma_eq_elim raw_received (B.append delta_received0 tail_received);
    Seq.append_assoc delta_sent0 tail_sent delta_sent;
    Seq.append_assoc delta_received0 tail_received delta_received;
    assert (Seq.equal
      (B.append (B.append delta_sent0 tail_sent) delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append (B.append delta_received0 tail_received) delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    assert (conn_events_received_decode_replay
      model0'
      (rest @ [ev])
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)
      model2);
    assert (events @ [ev] == ev0 :: (rest @ [ev]));
    assert (Seq.equal
      (B.append raw_sent delta_sent)
      (B.append delta_sent0 (B.append tail_sent delta_sent)));
    assert (Seq.equal
      (B.append raw_received delta_received)
      (B.append delta_received0 (B.append tail_received delta_received)));
    lemma_conn_events_received_decode_replay_cons
      model
      ev0
      (rest @ [ev])
      (B.append raw_sent delta_sent)
      (B.append raw_received delta_received)
      model2
      model0'
      delta_sent0
      delta_received0
      (B.append tail_sent delta_sent)
      (B.append tail_received delta_received)

let lemma_initial_sent_seal_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_sent_seal_replay_consistent (initial cfg))
=
  ()

let lemma_initial_sent_seal_key_schedule_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_sent_seal_key_schedule_replay_consistent (initial cfg))
=
  ()

let lemma_connection_state_sent_seal_key_schedule_replay
  (st:connection_state)
  : Lemma
      (requires
        st.cs_model.model_config.config_role == ClientEndpoint /\
        connection_state_sent_seal_replay_consistent st)
      (ensures connection_state_sent_seal_key_schedule_replay_consistent st)
=
  lemma_initial_record_keys_consistent st.cs_model.model_config;
  assert (model_record_keys_consistent (initial_model st.cs_model.model_config));
  lemma_conn_events_sent_seal_replay_strengthen
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let lemma_initial_received_decode_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_received_decode_replay_consistent (initial cfg))
=
  ()

let lemma_initial_received_decode_key_schedule_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_received_decode_key_schedule_replay_consistent (initial cfg))
=
  ()

let lemma_connection_state_received_decode_key_schedule_replay
  (st:connection_state)
  : Lemma
      (requires
        st.cs_model.model_config.config_role == ClientEndpoint /\
        connection_state_received_decode_replay_consistent st)
      (ensures connection_state_received_decode_key_schedule_replay_consistent st)
=
  lemma_initial_record_keys_consistent st.cs_model.model_config;
  assert (model_record_keys_consistent (initial_model st.cs_model.model_config));
  lemma_conn_events_received_decode_replay_strengthen
    (initial_model st.cs_model.model_config)
    st.cs_event_log
    st.cs_wire_log.CL.raw_sent
    st.cs_wire_log.CL.raw_received
    st.cs_model

let lemma_initial_raw_to_message_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_raw_to_message_replay_consistent (initial cfg))
=
  lemma_connection_state_protected_raw_segmented_replay (initial cfg);
  lemma_initial_sent_seal_replay_consistent cfg;
  lemma_initial_sent_seal_key_schedule_replay_consistent cfg;
  lemma_initial_received_decode_replay_consistent cfg;
  lemma_initial_received_decode_key_schedule_replay_consistent cfg

#restart-solver
let lemma_connection_state_raw_to_message_replay
  (st:connection_state)
  : Lemma
      (requires
        st.cs_model.model_config.config_role == ClientEndpoint /\
        connection_state_raw_event_replay_consistent st /\
        connection_state_sent_seal_replay_consistent st /\
        connection_state_received_decode_replay_consistent st)
      (ensures connection_state_raw_to_message_replay_consistent st)
=
  lemma_connection_state_protected_raw_segmented_replay st;
  lemma_connection_state_sent_seal_key_schedule_replay st;
  lemma_connection_state_received_decode_key_schedule_replay st

let lemma_initial_raw_event_replay_consistent
  (cfg:connection_config)
  : Lemma (connection_state_raw_event_replay_consistent (initial cfg))
=
  ()

let lemma_legal_connection_delta_raw_event_replay_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_raw_event_replay_consistent st0)
      (ensures connection_state_raw_event_replay_consistent st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_wire_log.CL.raw_sent ==
    B.append st0.cs_wire_log.CL.raw_sent delta.delta_raw_sent);
  assert (st1.cs_wire_log.CL.raw_received ==
    B.append st0.cs_wire_log.CL.raw_received delta.delta_raw_received);
  lemma_conn_events_raw_replay_snoc
    (initial_model st0.cs_model.model_config)
    st0.cs_event_log
    st0.cs_wire_log.CL.raw_sent
    st0.cs_wire_log.CL.raw_received
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received
    st1.cs_model

let lemma_legal_connection_delta_sent_seal_replay_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_sent_seal_replay_consistent st0 /\
        sent_event_nonempty_seal_projection
          st0.cs_model
          delta.delta_event
          delta.delta_raw_sent)
      (ensures connection_state_sent_seal_replay_consistent st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_wire_log.CL.raw_sent ==
    B.append st0.cs_wire_log.CL.raw_sent delta.delta_raw_sent);
  assert (st1.cs_wire_log.CL.raw_received ==
    B.append st0.cs_wire_log.CL.raw_received delta.delta_raw_received);
  lemma_conn_events_sent_seal_replay_snoc
    (initial_model st0.cs_model.model_config)
    st0.cs_event_log
    st0.cs_wire_log.CL.raw_sent
    st0.cs_wire_log.CL.raw_received
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received
    st1.cs_model

let lemma_legal_connection_delta_received_decode_replay_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_received_decode_replay_consistent st0 /\
        received_event_nonempty_decode_projection
          st0.cs_model
          delta.delta_event
          delta.delta_raw_received)
      (ensures connection_state_received_decode_replay_consistent st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_wire_log.CL.raw_sent ==
    B.append st0.cs_wire_log.CL.raw_sent delta.delta_raw_sent);
  assert (st1.cs_wire_log.CL.raw_received ==
    B.append st0.cs_wire_log.CL.raw_received delta.delta_raw_received);
  lemma_conn_events_received_decode_replay_snoc
    (initial_model st0.cs_model.model_config)
    st0.cs_event_log
    st0.cs_wire_log.CL.raw_sent
    st0.cs_wire_log.CL.raw_received
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received
    st1.cs_model

let lemma_legal_connection_delta_app_log_delta
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures model_app_log_delta st0.cs_model delta.delta_event st1.cs_model)
=
  lemma_step_model_app_log_delta
    st0.cs_model
    delta.delta_event
    st1.cs_model

let lemma_legal_connection_delta_app_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_app_log_consistent st0)
      (ensures connection_state_app_log_consistent st1)
=
  lemma_legal_connection_delta_app_log_delta st0 delta st1;
  lemma_app_sent_messages_snoc st0.cs_event_log delta.delta_event;
  lemma_app_received_messages_snoc st0.cs_event_log delta.delta_event;
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_model.model_application.app_log.CL.app_sent ==
    st0.cs_model.model_application.app_log.CL.app_sent @
      conn_event_app_sent_delta delta.delta_event);
  assert (st1.cs_model.model_application.app_log.CL.app_received ==
    st0.cs_model.model_application.app_log.CL.app_received @
      conn_event_app_received_delta delta.delta_event);
  assert (app_sent_messages st1.cs_event_log ==
    app_sent_messages st0.cs_event_log @
      conn_event_app_sent_delta delta.delta_event);
  assert (app_received_messages st1.cs_event_log ==
    app_received_messages st0.cs_event_log @
      conn_event_app_received_delta delta.delta_event)

let lemma_legal_connection_delta_event_log_consistent_with
  (cfg:connection_config)
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_event_log_consistent_with cfg st0)
      (ensures connection_state_event_log_consistent_with cfg st1)
=
  lemma_step_model_many_snoc
    (initial_model cfg)
    st0.cs_event_log
    delta.delta_event
    st0.cs_model
    st1.cs_model;
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event])

let lemma_legal_connection_delta_event_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_event_log_consistent st0)
      (ensures connection_state_event_log_consistent st1)
=
  lemma_legal_connection_delta_event_log_consistent_with
    st0.cs_model.model_config
    st0
    delta
    st1;
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config)

let lemma_legal_connection_delta_transcript_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_transcript_consistent st0)
      (ensures connection_state_transcript_consistent st1)
=
  lemma_step_model_transcript_delta st0.cs_model delta.delta_event st1.cs_model;
  lemma_transcript_bytes_snoc st0.cs_event_log delta.delta_event;
  Seq.lemma_eq_elim
    st0.cs_model.model_handshake.hs_transcript
    (transcript_bytes_of_conn_events st0.cs_event_log);
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (Seq.equal
    st1.cs_model.model_handshake.hs_transcript
    (B.append
      st0.cs_model.model_handshake.hs_transcript
      (conn_event_transcript_delta delta.delta_event)));
  assert (B.append
    st0.cs_model.model_handshake.hs_transcript
    (conn_event_transcript_delta delta.delta_event) ==
    transcript_bytes_of_conn_events st1.cs_event_log)

let lemma_legal_connection_delta_key_update_pending_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_key_update_pending_consistent st0)
      (ensures connection_state_key_update_pending_consistent st1)
=
  lemma_step_model_key_update_pending_delta st0.cs_model delta.delta_event st1.cs_model;
  lemma_key_update_response_pending_snoc st0.cs_event_log delta.delta_event;
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_model.model_application.app_key_update_response_pending ==
    key_update_response_pending_step
      st0.cs_model.model_application.app_key_update_response_pending
      delta.delta_event);
  assert (st0.cs_model.model_application.app_key_update_response_pending ==
    key_update_response_pending_of_conn_events st0.cs_event_log);
  assert (st1.cs_model.model_application.app_key_update_response_pending ==
    key_update_response_pending_step
      (key_update_response_pending_of_conn_events st0.cs_event_log)
      delta.delta_event);
  assert (key_update_response_pending_of_conn_events st1.cs_event_log ==
    key_update_response_pending_step
      (key_update_response_pending_of_conn_events st0.cs_event_log)
      delta.delta_event)

let lemma_legal_connection_delta_record_layer_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_record_layer_consistent st0)
      (ensures connection_state_record_layer_consistent st1)
=
  lemma_step_model_record_layer_delta st0.cs_model delta.delta_event st1.cs_model;
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  lemma_projected_record_layer_snoc_for_role
    st0.cs_model.model_config.config_role
    st0.cs_event_log
    delta.delta_event;
  assert (st1.cs_event_log == st0.cs_event_log @ [delta.delta_event]);
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  match st1.cs_model.model_control with
  | ControlFailed _ -> ()
  | _ ->
    assert (projected_record_layer_state_of_record st1.cs_model.model_record ==
      projected_record_layer_step_for_role
        st0.cs_model.model_config.config_role
        (projected_record_layer_state_of_record st0.cs_model.model_record)
        delta.delta_event);
    assert (projected_record_layer_state_of_record st0.cs_model.model_record ==
      projected_record_layer_of_conn_events_for_role
        st0.cs_model.model_config.config_role
        st0.cs_event_log);
    assert (projected_record_layer_state_of_record st1.cs_model.model_record ==
      projected_record_layer_step_for_role
        st0.cs_model.model_config.config_role
        (projected_record_layer_of_conn_events_for_role
          st0.cs_model.model_config.config_role
          st0.cs_event_log)
        delta.delta_event);
    assert (projected_record_layer_of_conn_events_for_role
      st0.cs_model.model_config.config_role
      st1.cs_event_log ==
      projected_record_layer_step_for_role
        st0.cs_model.model_config.config_role
        (projected_record_layer_of_conn_events_for_role
          st0.cs_model.model_config.config_role
          st0.cs_event_log)
        delta.delta_event)

let lemma_legal_connection_delta_record_keys_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_record_keys_consistent st0)
      (ensures connection_state_record_keys_consistent st1)
=
  assert (st0.cs_model.model_config.config_role == ClientEndpoint);
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  lemma_step_model_record_keys_consistent
    st0.cs_model
    delta.delta_event
    st1.cs_model

let lemma_legal_connection_delta_record_keys_consistent_for_role
  (role:endpoint_role)
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        role == st0.cs_model.model_config.config_role /\
        connection_state_record_keys_consistent_for_role role st0)
      (ensures connection_state_record_keys_consistent_for_role role st1)
=
  lemma_step_model_record_keys_consistent_for_role
    role
    st0.cs_model
    delta.delta_event
    st1.cs_model

let lemma_legal_connection_delta_pending_application_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_pending_application_consistent st0)
      (ensures connection_state_pending_application_consistent st1)
=
  lemma_step_model_pending_application_delta
    st0.cs_model
    delta.delta_event
    st1.cs_model

let lemma_legal_connection_delta_layered_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_layered_log_consistent st0)
      (ensures connection_state_layered_log_consistent st1)
=
  assert (st0.cs_model.model_config.config_role == ClientEndpoint);
  assert (step_model st0.cs_model delta.delta_event == Some st1.cs_model);
  lemma_step_model_preserves_config_for_x25519_reachable_shape
    st0.cs_model
    delta.delta_event
    st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  lemma_legal_connection_delta_event_log_consistent st0 delta st1;
  lemma_legal_connection_delta_transcript_consistent st0 delta st1;
  lemma_legal_connection_delta_key_update_pending_consistent st0 delta st1;
  lemma_legal_connection_delta_record_layer_consistent st0 delta st1;
  lemma_legal_connection_delta_record_keys_consistent st0 delta st1;
  lemma_legal_connection_delta_pending_application_consistent st0 delta st1;
  lemma_legal_connection_delta_app_log_consistent st0 delta st1

let lemma_legal_connection_delta_layered_log_consistent_for_role
  (role:endpoint_role)
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        role == st0.cs_model.model_config.config_role /\
        connection_state_layered_log_consistent_for_role role st0)
      (ensures connection_state_layered_log_consistent_for_role role st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (role == st1.cs_model.model_config.config_role);
  lemma_legal_connection_delta_event_log_consistent st0 delta st1;
  lemma_legal_connection_delta_transcript_consistent st0 delta st1;
  lemma_legal_connection_delta_key_update_pending_consistent st0 delta st1;
  lemma_legal_connection_delta_record_layer_consistent st0 delta st1;
  lemma_legal_connection_delta_record_keys_consistent_for_role role st0 delta st1;
  lemma_legal_connection_delta_pending_application_consistent st0 delta st1;
  lemma_legal_connection_delta_app_log_consistent st0 delta st1

let lemma_initial_full_log_consistent
  (cfg:connection_config)
  : Lemma
      (requires cfg.config_role == ClientEndpoint)
      (ensures connection_state_full_log_consistent (initial cfg))
=
  lemma_initial_layered_log_consistent cfg;
  lemma_connection_state_connection_log_view_consistent (initial cfg);
  lemma_initial_raw_event_replay_consistent cfg

let lemma_initial_full_log_consistent_for_role
  (role:endpoint_role)
  (cfg:connection_config)
  : Lemma (connection_state_full_log_consistent_for_role role (initial cfg))
=
  lemma_initial_layered_log_consistent_for_role role cfg;
  lemma_connection_state_connection_log_view_consistent (initial cfg);
  lemma_initial_raw_event_replay_consistent cfg

let lemma_legal_connection_delta_full_log_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        connection_state_full_log_consistent st0)
      (ensures connection_state_full_log_consistent st1)
=
  assert (st0.cs_model.model_config.config_role == ClientEndpoint);
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  lemma_legal_connection_delta_layered_log_consistent st0 delta st1;
  lemma_connection_state_connection_log_view_consistent st1;
  lemma_legal_connection_delta_raw_event_replay_consistent st0 delta st1

let lemma_legal_connection_delta_full_log_consistent_for_role
  (role:endpoint_role)
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        legal_connection_delta st0 delta st1 /\
        role == st0.cs_model.model_config.config_role /\
        connection_state_full_log_consistent_for_role role st0)
      (ensures connection_state_full_log_consistent_for_role role st1)
=
  lemma_legal_connection_delta_layered_log_consistent_for_role role st0 delta st1;
  lemma_connection_state_connection_log_view_consistent st1;
  lemma_legal_connection_delta_raw_event_replay_consistent st0 delta st1

let lemma_legal_connection_delta_protected_single_parse_record
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_single_raw_parse_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_single_parse_record
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let lemma_legal_connection_delta_protected_parse_prefix
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_parse_prefix_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_parse_prefix
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let lemma_legal_connection_delta_protected_decompose_prefix
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_decompose_prefix_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_decompose_prefix
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let lemma_legal_connection_delta_protected_segmented
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires legal_connection_delta st0 delta st1)
      (ensures event_protected_raw_segmented_success
        delta.delta_event
        delta.delta_raw_sent
        delta.delta_raw_received)
=
  lemma_event_raw_delta_legal_protected_segmented
    st0.cs_model
    delta.delta_event
    delta.delta_raw_sent
    delta.delta_raw_received

let lemma_legal_connection_delta_consistent
  (st0:connection_state)
  (delta:connection_delta)
  (st1:connection_state)
  : Lemma
      (requires
        connection_state_consistent st0 /\
        legal_connection_delta st0 delta st1)
      (ensures connection_state_consistent st1)
=
  lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
  assert (st1.cs_model.model_config == st0.cs_model.model_config);
  assert (connection_state_single_step st0 st1);
  RTC.closure_step connection_state_single_step st0 st1;
  assert (connection_state_evolves st0 st1);
  assert (connection_state_evolves (initial st0.cs_model.model_config) st0);
  assert (connection_state_evolves (initial st0.cs_model.model_config) st1)

(* ================================================================== *)
(* NON-READY x25519 key-share PROJECTION from consistency + presence.  *)
(*                                                                     *)
(* Given [connection_state_consistent] and [Some? ks_shared_secret]    *)
(* (the latter supplied non-ready by the CANONICAL-shape presence      *)
(* bricks), the model-level x25519 reachable shape yields the full     *)
(* stable per-endpoint projection.  These are the consistency-side     *)
(* ingredient of the non-ready cross-endpoint HANDSHAKE agreement      *)
(* producer.  The server form excludes the two non-stable arms of      *)
(* [server_x25519_reachable_shape] ([HsClientHelloReceived], where the *)
(* shape gives only the pre-ServerHello projection, and [ControlFailed] *)
(* where it degrades to a disjunction); at [HsServerFinishedSent] — the *)
(* only server control a client-Finished send's consumer needs — both  *)
(* exclusions hold and the stable projection follows.                  *)
(* ================================================================== *)
let lemma_consistent_shared_secret_stable_client_x25519_projection
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret)
      (ensures stable_client_x25519_key_share_projection st)
  = lemma_connection_state_consistent_client_x25519_reachable_shape st

let lemma_consistent_shared_secret_stable_server_x25519_projection
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret /\
        st.cs_model.model_control =!= ControlHandshaking HsClientHelloReceived /\
        ~(ControlFailed? st.cs_model.model_control))
      (ensures stable_server_x25519_key_share_projection st)
  = lemma_connection_state_consistent_server_x25519_reachable_shape st

(* ================================================================== *)
(* NON-READY handshake-epoch material bridge (Brick 3).               *)
(*                                                                     *)
(* Part 1: consistency -> record-keys consistency.  [stable_on_closure] *)
(* over the reachable closure, using the already-exposed initial and   *)
(* delta record-keys ingredients.  The stable predicate tracks the     *)
(* config role (preserved by every step).                              *)
(* ================================================================== *)
let record_keys_consistent_config_role_shape (st:connection_state) : prop =
  connection_state_record_keys_consistent_for_role
    st.cs_model.model_config.config_role
    st

let lemma_delta_record_keys_consistent_config_role_shape
  (st0 st1:connection_state)
  : Lemma
      (requires
        record_keys_consistent_config_role_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures record_keys_consistent_config_role_shape st1)
=
  eliminate exists delta. legal_connection_delta st0 delta st1
  with
    (lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
     assert (st1.cs_model.model_config == st0.cs_model.model_config);
     lemma_legal_connection_delta_record_keys_consistent_for_role
       st0.cs_model.model_config.config_role st0 delta st1)

let lemma_single_step_record_keys_consistent_config_role_shape (_:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern (record_keys_consistent_config_role_shape y);
                    (connection_state_single_step x y)}
          record_keys_consistent_config_role_shape x /\
          connection_state_single_step x y ==>
          record_keys_consistent_config_role_shape y)
=
  introduce forall (x:connection_state) (y:connection_state).
    record_keys_consistent_config_role_shape x /\
    connection_state_single_step x y ==>
    record_keys_consistent_config_role_shape y
  with
    introduce _ ==> _ with
    lemma_delta_record_keys_consistent_config_role_shape x y

let lemma_initial_record_keys_consistent_config_role_shape (cfg:connection_config)
  : Lemma (ensures record_keys_consistent_config_role_shape (initial cfg))
=
  lemma_initial_record_keys_consistent_for_role cfg.config_role cfg

let lemma_connection_state_consistent_record_keys_consistent_for_config_role
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures
        connection_state_record_keys_consistent_for_role
          st.cs_model.model_config.config_role
          st)
=
  lemma_initial_record_keys_consistent_config_role_shape st.cs_model.model_config;
  lemma_single_step_record_keys_consistent_config_role_shape ();
  let p = record_keys_consistent_config_role_shape in
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure connection_state_single_step p stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)

(* ================================================================== *)
(* Part 2: handshake-epoch material producer.  HANDSHAKE mirror of     *)
(* [lemma_application_record_direction_material_matches_key_schedule_for_role]. *)
(* From [model_record_keys_consistent_for_role role model] (past the   *)
(* [ControlFailed] guard) and a [Handshake]-epoch record direction, the *)
(* [R.Handshake] arm of [record_keys_match_key_schedule_for_role]       *)
(* delivers [traffic_material_matches_record_direction material st]     *)
(* (= [st.key == Some material.traffic_key /\ st.static_iv == Some ..]);*)
(* the [Seq.equal] bridge to [record_key_iv_material_agrees] is the     *)
(* SAME one proved in the application producer.  No vacuity clause on   *)
(* the handshake arm, so no installed-helper detour is needed.          *)
(* ================================================================== *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let lemma_handshake_record_direction_material_matches_key_schedule_for_role
  (role:endpoint_role)
  (dir:traffic_direction)
  (model:connection_model)
  : Lemma
      (requires
        model_record_keys_consistent_for_role role model /\
        ~(ControlFailed? model.model_control) /\
        (record_direction_for_endpoint role dir model).R.epoch == R.Handshake)
      (ensures
        record_direction_material_matches_key_schedule_for_role
          role
          dir
          (traffic_id TrafficHandshake (traffic_label_for_endpoint_direction role dir))
          model)
=
  let keys = model.model_handshake.hs_keys in
  match role, dir with
  | ClientEndpoint, TrafficWrite ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite == ClientTraffic);
    assert (record_keys_match_key_schedule_for_role
      ClientEndpoint TrafficWrite model.model_control keys model.model_record.record_write);
    (match
      traffic_material_for_label keys TrafficHandshake ClientTraffic,
      record_direction_material model.model_record.record_write
     with
     | Some material, Some record_material ->
       assert (traffic_material_matches_record_direction material model.model_record.record_write);
       assert (Seq.equal material.traffic_key record_material.record_material_key);
       assert (Seq.equal material.traffic_iv record_material.record_material_iv)
     | _, _ ->
       assert False)
  | ClientEndpoint, TrafficRead ->
    assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic);
    assert (record_keys_match_key_schedule_for_role
      ClientEndpoint TrafficRead model.model_control keys model.model_record.record_read);
    (match
      traffic_material_for_label keys TrafficHandshake ServerTraffic,
      record_direction_material model.model_record.record_read
     with
     | Some material, Some record_material ->
       assert (traffic_material_matches_record_direction material model.model_record.record_read);
       assert (Seq.equal material.traffic_key record_material.record_material_key);
       assert (Seq.equal material.traffic_iv record_material.record_material_iv)
     | _, _ ->
       assert False)
  | ServerEndpoint, TrafficRead ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic);
    assert (record_keys_match_key_schedule_for_role
      ServerEndpoint TrafficRead model.model_control keys model.model_record.record_read);
    (match
      traffic_material_for_label keys TrafficHandshake ClientTraffic,
      record_direction_material model.model_record.record_read
     with
     | Some material, Some record_material ->
       assert (traffic_material_matches_record_direction material model.model_record.record_read);
       assert (Seq.equal material.traffic_key record_material.record_material_key);
       assert (Seq.equal material.traffic_iv record_material.record_material_iv)
     | _, _ ->
       assert False)
  | ServerEndpoint, TrafficWrite ->
    assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite == ServerTraffic);
    assert (record_keys_match_key_schedule_for_role
      ServerEndpoint TrafficWrite model.model_control keys model.model_record.record_write);
    (match
      traffic_material_for_label keys TrafficHandshake ServerTraffic,
      record_direction_material model.model_record.record_write
     with
     | Some material, Some record_material ->
       assert (traffic_material_matches_record_direction material model.model_record.record_write);
       assert (Seq.equal material.traffic_key record_material.record_material_key);
       assert (Seq.equal material.traffic_iv record_material.record_material_iv)
     | _, _ ->
       assert False)
#pop-options

(* ================================================================== *)
(* Brick 3.5: handshake-epoch analogue of                              *)
(* [first_epoch_application_traffic_material_slots_match_expected].     *)
(*                                                                      *)
(* Establishes, from [connection_state_consistent] alone, that each     *)
(* installed handshake traffic slot's material equals the expected      *)
(* material derived from the (frozen) TH_SH checkpoint.  This is the     *)
(* "missing, not circular" GAP feeding                                  *)
(* [lemma_key_schedule_traffic_record_material_agrees_from_expected]     *)
(* for the handshake epoch (the application analogue already exists).    *)
(*                                                                      *)
(* Structure MIRRORS the application machinery (stage-shape +           *)
(* checkpoint-ready + slots-match, closed by [stable_on_closure]) but   *)
(* is lighter: the TH_SH checkpoint is [serialize CH ++ serialize SH]   *)
(* read from the STORED hellos (Correspondence.fst:53), hence frozen    *)
(* from HsServerHelloReceived onward, so there is no key-update and no   *)
(* late-checkpoint-drift; and no raw-event-replay is needed because     *)
(* every ingredient is model-only.  The install control is pinned by    *)
(* [traffic_install_allowed_at_stage] to exactly                        *)
(* HsServerHelloReceived / HsServerHelloSent, where the EXISTING        *)
(* checkpoint-ready table already carries [TH_SH == live transcript],   *)
(* so install-legality (which uses the live [Tr.hash hs_transcript])    *)
(* coincides with the checkpoint form used by                           *)
(* [traffic_material_matches_expected_derived_material].                 *)
(*                                                                      *)
(* Both handshake traffic slots (ClientTraffic and ServerTraffic) are   *)
(* covered: ClientTraffic is what the client-Finished flip needs, and   *)
(* ServerTraffic is the mirror obligation for the reverse-direction     *)
(* flip (StateMachine.fst:738, client read -> Application on receiving   *)
(* the server Finished).  The induction is uniform in the label, so     *)
(* both come for essentially the same cost.                             *)
(* ================================================================== *)

(* Stage-shape companion: handshake traffic slots are None before both  *)
(* CH and SH are present, i.e. before the ServerHello control.  This is  *)
(* what discharges the "slot None \/ checkpoint stable" disjunction at   *)
(* the (only) CH/SH-appending steps that move the TH_SH checkpoint.      *)
let handshake_traffic_key_slot_stage_shape_for_role
  (role:endpoint_role)
  (model:connection_model)
  : prop =
  let keys = model.model_handshake.hs_keys in
  match role, model.model_control with
  | ClientEndpoint, ControlNew
  | ClientEndpoint, ControlHandshaking HsStarted
  | ClientEndpoint, ControlHandshaking HsClientHelloSent
  | ServerEndpoint, ControlNew
  | ServerEndpoint, ControlHandshaking HsAwaitingClientHello
  | ServerEndpoint, ControlHandshaking HsClientHelloReceived ->
    keys.ks_client_handshake_traffic == None /\
    keys.ks_server_handshake_traffic == None
  | _, _ ->
    True

// Localized hardening for this whole-match `()` preservation VC: the enlarged
// application-record-epoch shape axiom shifts the module SMT context and tips this
// pre-existing single-VC proof over its budget.  `` solves it
// per step-arm (each cheap), which is robust to context shift.
#push-options "--z3rlimit 40"
let lemma_step_model_preserves_handshake_traffic_key_slot_stage_shape_for_role
  (role:endpoint_role)
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires
        model.model_config.config_role == role /\
        handshake_traffic_key_slot_stage_shape_for_role role model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures
        handshake_traffic_key_slot_stage_shape_for_role role model')
=
  ()
#pop-options

(* Companion: a present handshake secret implies a present shared secret. *)
(* [derive_shared_secret_model] (StateMachine.fst:470) sets both slots     *)
(* atomically and no other step writes [ks_handshake_secret], so this is   *)
(* preserved trivially.  It is what forces the handshake traffic slots to  *)
(* be absent at a [LocalDeriveSharedSecret] step (whose legality pins      *)
(* [ks_shared_secret == None]), the one non-install local event that moves *)
(* [ks_handshake_secret] and hence escapes the stage-shape / checkpoint    *)
(* discharge used for every other event.                                   *)
let handshake_secret_requires_shared_secret
  (model:connection_model)
  : prop =
  Some? model.model_handshake.hs_keys.ks_handshake_secret ==>
  Some? model.model_handshake.hs_keys.ks_shared_secret

#push-options "--fuel 2 --ifuel 2 --z3rlimit 400"
let lemma_step_model_preserves_handshake_secret_requires_shared_secret
  (model:connection_model)
  (ev:conn_event)
  (model':connection_model)
  : Lemma
      (requires
        handshake_secret_requires_shared_secret model /\
        legal_event model ev /\
        step_model model ev == Some model')
      (ensures
        handshake_secret_requires_shared_secret model')
=
  match ev with
  | ConnNetworkEvent _ -> ()
  | ConnProtectedHandshake _ -> ()
  | ConnLocalEvent _ -> ()
#pop-options

let first_epoch_handshake_traffic_material_slots_match_expected_model
  (model:connection_model)
  : prop =
  first_epoch_handshake_traffic_material_slots_match_expected
    (state_of_model_for_first_epoch_application_material model)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"

(* H1: single-label preservation when the slot, the handshake secret,   *)
(* and the TH_SH checkpoint are all unchanged.  Mirrors                 *)
(* [lemma_application_traffic_label_match_expected_preserved].           *)
let lemma_handshake_traffic_label_match_expected_preserved
  (label:traffic_label)
  (model0:connection_model)
  (model1:connection_model)
  : Lemma
      (requires
        traffic_material_matches_expected_derived_material
          (traffic_id TrafficHandshake label)
          (state_of_model_for_first_epoch_application_material model0) /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficHandshake
          label ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficHandshake
          label /\
        model1.model_handshake.hs_keys.ks_handshake_secret ==
        model0.model_handshake.hs_keys.ks_handshake_secret /\
        negotiated_aead_alg model1.model_handshake ==
          negotiated_aead_alg model0.model_handshake /\
        transcript_checkpoint_bytes TH_SH model1.model_handshake ==
        transcript_checkpoint_bytes TH_SH model0.model_handshake)
      (ensures
        traffic_material_matches_expected_derived_material
          (traffic_id TrafficHandshake label)
          (state_of_model_for_first_epoch_application_material model1))
=
  let st0 = state_of_model_for_first_epoch_application_material model0 in
  let st1 = state_of_model_for_first_epoch_application_material model1 in
  assert_norm (key_checkpoint_for_epoch TrafficHandshake == DeriveHandshakeTraffic);
  assert_norm (key_derivation_checkpoint_transcript DeriveHandshakeTraffic == Some TH_SH);
  assert
    (expected_traffic_secret_for_state
      (traffic_id TrafficHandshake label)
      st1 ==
     expected_traffic_secret_for_state
      (traffic_id TrafficHandshake label)
      st0);
  assert
    (expected_derived_key_material
      (TrafficKey (traffic_id TrafficHandshake label))
      st1 ==
     expected_derived_key_material
      (TrafficKey (traffic_id TrafficHandshake label))
      st0);
  assert
    (expected_derived_key_material
      (TrafficIV (traffic_id TrafficHandshake label))
      st1 ==
     expected_derived_key_material
      (TrafficIV (traffic_id TrafficHandshake label))
      st0)

(* H2: guarded single-label preservation (the slot may be absent, in    *)
(* which case the conclusion is vacuous).  Mirrors                      *)
(* [..._application_label_match_expected_preserved_when_slot_unchanged_or_checkpoint_stable]. *)
let lemma_first_epoch_handshake_label_match_expected_preserved_when_slot_unchanged_or_checkpoint_stable
  (label:traffic_label)
  (model0:connection_model)
  (model1:connection_model)
  : Lemma
      (requires
        first_epoch_handshake_traffic_material_slots_match_expected_model
          model0 /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficHandshake
          label ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficHandshake
          label /\
        (traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficHandshake
          label == None \/
         (model1.model_handshake.hs_keys.ks_handshake_secret ==
          model0.model_handshake.hs_keys.ks_handshake_secret /\
          negotiated_aead_alg model1.model_handshake ==
            negotiated_aead_alg model0.model_handshake /\
          transcript_checkpoint_bytes TH_SH model1.model_handshake ==
          transcript_checkpoint_bytes TH_SH model0.model_handshake)))
      (ensures
        Some?
          (traffic_material_for_label
            model1.model_handshake.hs_keys
            TrafficHandshake
            label) ==>
        traffic_material_matches_expected_derived_material
          (traffic_id TrafficHandshake label)
          (state_of_model_for_first_epoch_application_material model1))
=
  if Some?
      (traffic_material_for_label
        model1.model_handshake.hs_keys
        TrafficHandshake
        label)
  then begin
    assert
      (Some?
        (traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficHandshake
          label));
    match
      traffic_material_for_label
        model0.model_handshake.hs_keys
        TrafficHandshake
        label
    with
    | None ->
      assert False
    | Some _ ->
      (match label with
       | ClientTraffic ->
         assert
           (traffic_material_matches_expected_derived_material
             (traffic_id TrafficHandshake ClientTraffic)
             (state_of_model_for_first_epoch_application_material model0))
       | ServerTraffic ->
         assert
           (traffic_material_matches_expected_derived_material
             (traffic_id TrafficHandshake ServerTraffic)
             (state_of_model_for_first_epoch_application_material model0)));
      assert
        (model1.model_handshake.hs_keys.ks_handshake_secret ==
         model0.model_handshake.hs_keys.ks_handshake_secret);
      assert
        (negotiated_aead_alg model1.model_handshake ==
         negotiated_aead_alg model0.model_handshake);
      assert
        (transcript_checkpoint_bytes TH_SH model1.model_handshake ==
         transcript_checkpoint_bytes TH_SH model0.model_handshake);
      lemma_handshake_traffic_label_match_expected_preserved
        label
        model0
        model1
  end

(* H3: both-slot preservation.  Mirrors                                 *)
(* [..._application_slots_preserved_when_slots_unchanged_or_checkpoint_stable]. *)
let lemma_first_epoch_handshake_slots_preserved_when_slots_unchanged_or_checkpoint_stable
  (model0:connection_model)
  (model1:connection_model)
  : Lemma
      (requires
        first_epoch_handshake_traffic_material_slots_match_expected_model
          model0 /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficHandshake
          ClientTraffic ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficHandshake
          ClientTraffic /\
        traffic_material_for_label
          model1.model_handshake.hs_keys
          TrafficHandshake
          ServerTraffic ==
        traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficHandshake
          ServerTraffic /\
        (traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficHandshake
          ClientTraffic == None \/
         (model1.model_handshake.hs_keys.ks_handshake_secret ==
          model0.model_handshake.hs_keys.ks_handshake_secret /\
          negotiated_aead_alg model1.model_handshake ==
            negotiated_aead_alg model0.model_handshake /\
          transcript_checkpoint_bytes TH_SH model1.model_handshake ==
          transcript_checkpoint_bytes TH_SH model0.model_handshake)) /\
        (traffic_material_for_label
          model0.model_handshake.hs_keys
          TrafficHandshake
          ServerTraffic == None \/
         (model1.model_handshake.hs_keys.ks_handshake_secret ==
          model0.model_handshake.hs_keys.ks_handshake_secret /\
          negotiated_aead_alg model1.model_handshake ==
            negotiated_aead_alg model0.model_handshake /\
          transcript_checkpoint_bytes TH_SH model1.model_handshake ==
          transcript_checkpoint_bytes TH_SH model0.model_handshake)))
      (ensures
        first_epoch_handshake_traffic_material_slots_match_expected_model
          model1)
=
  lemma_first_epoch_handshake_label_match_expected_preserved_when_slot_unchanged_or_checkpoint_stable
    ClientTraffic
    model0
    model1;
  lemma_first_epoch_handshake_label_match_expected_preserved_when_slot_unchanged_or_checkpoint_stable
    ServerTraffic
    model0
    model1

(* Client-side checkpoint-ready eliminator at HsServerHelloReceived,     *)
(* mirroring [lemma_server_hs_server_hello_sent_checkpoint_ready_elim].   *)
let lemma_client_hs_server_hello_received_checkpoint_ready_elim
  (model:connection_model)
  : Lemma
      (requires
        application_traffic_install_checkpoint_ready_for_role
          ClientEndpoint
          model /\
        model.model_control == ControlHandshaking HsServerHelloReceived)
      (ensures
        transcript_checkpoint_bytes TH_SH model.model_handshake ==
        Some model.model_handshake.hs_transcript)
=
  match model.model_control with
  | ControlHandshaking HsServerHelloReceived ->
    ()
  | _ ->
    assert False

(* H4: freshly-installed handshake slot matches the expected derived     *)
(* material.  Mirrors                                                    *)
(* [lemma_application_traffic_install_for_role_material_matches_expected].*)
(* The install control is forced to HsServerHelloReceived (client) /     *)
(* HsServerHelloSent (server) by [traffic_install_allowed_at_stage],     *)
(* and at that control the checkpoint-ready table gives                 *)
(* [transcript_checkpoint_bytes TH_SH hs0 == Some hs0.hs_transcript],    *)
(* so the live-transcript install match equals the TH_SH-checkpoint one. *)
let lemma_handshake_traffic_install_for_role_material_matches_expected
  (role:endpoint_role)
  (model0:connection_model)
  (stage:handshake_stage)
  (install:traffic_key_install)
  (model1:connection_model)
  : Lemma
      (requires
        model0.model_config.config_role == role /\
        model0.model_control == ControlHandshaking stage /\
        application_traffic_install_checkpoint_ready_for_role role model0 /\
        traffic_install_allowed_at_stage_for_role role stage install /\
        traffic_install_matches_key_schedule_for_role
          role
          model0.model_handshake
          install /\
        install.install_epoch == TrafficHandshake /\
        model1.model_handshake ==
          { model0.model_handshake with
              hs_keys =
                update_key_schedule_with_install_for_role
                  role
                  model0.model_handshake.hs_keys
                  install })
      (ensures
        traffic_material_matches_expected_derived_material
          (traffic_id
            TrafficHandshake
            (traffic_label_for_endpoint_direction
              role
              install.install_direction))
          (state_of_model_for_first_epoch_application_material model1))
=
  let hs0 = model0.model_handshake in
  let hs1 = model1.model_handshake in
  assert_norm (key_checkpoint_for_epoch TrafficHandshake == DeriveHandshakeTraffic);
  assert_norm (key_derivation_checkpoint_transcript DeriveHandshakeTraffic == Some TH_SH);
  (match role with
   | ClientEndpoint ->
     assert (stage == HsServerHelloReceived);
     lemma_client_hs_server_hello_received_checkpoint_ready_elim model0
   | ServerEndpoint ->
     assert (stage == HsServerHelloSent);
     lemma_server_hs_server_hello_sent_checkpoint_ready_elim model0);
  assert (transcript_checkpoint_bytes TH_SH hs0 == Some hs0.hs_transcript);
  assert (transcript_checkpoint_bytes TH_SH hs1 == Some hs0.hs_transcript);
  (match role, install.install_direction with
   | ClientEndpoint, TrafficWrite ->
     assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficWrite ==
                  ClientTraffic)
   | ClientEndpoint, TrafficRead ->
     assert_norm (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead ==
                  ServerTraffic)
   | ServerEndpoint, TrafficWrite ->
     assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficWrite ==
                  ServerTraffic)
   | ServerEndpoint, TrafficRead ->
     assert_norm (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead ==
                  ClientTraffic));
  match
    expected_traffic_secret_for_role
      role
      hs0
      install.install_epoch
      install.install_direction
  with
  | Some secret ->
    assert (install.install_material ==
      traffic_key_material_for_secret (negotiated_aead_alg hs0) secret);
    assert (install.install_material.traffic_key ==
      K.derive_aead_key (negotiated_aead_alg hs0) secret);
    assert (install.install_material.traffic_iv == K.derive_aead_iv secret);
    Seq.lemma_eq_refl
      install.install_material.traffic_key
      (K.derive_aead_key (negotiated_aead_alg hs0) secret);
    Seq.lemma_eq_refl
      install.install_material.traffic_iv
      (K.derive_aead_iv secret)
  | None ->
    assert False

(* H5: a handshake install preserves BOTH slots-match conjuncts: the     *)
(* installed slot via H4, the other slot via H1 (guarded on presence).   *)
let lemma_first_epoch_handshake_slots_preserved_on_handshake_install
  (role:endpoint_role)
  (model0:connection_model)
  (stage:handshake_stage)
  (install:traffic_key_install)
  (model1:connection_model)
  : Lemma
      (requires
        model0.model_config.config_role == role /\
        model0.model_control == ControlHandshaking stage /\
        application_traffic_install_checkpoint_ready_for_role role model0 /\
        traffic_install_allowed_at_stage_for_role role stage install /\
        traffic_install_matches_key_schedule_for_role
          role
          model0.model_handshake
          install /\
        install.install_epoch == TrafficHandshake /\
        first_epoch_handshake_traffic_material_slots_match_expected_model
          model0 /\
        model1.model_handshake ==
          { model0.model_handshake with
              hs_keys =
                update_key_schedule_with_install_for_role
                  role
                  model0.model_handshake.hs_keys
                  install })
      (ensures
        first_epoch_handshake_traffic_material_slots_match_expected_model
          model1)
=
  let inst_label =
    traffic_label_for_endpoint_direction role install.install_direction in
  lemma_handshake_traffic_install_for_role_material_matches_expected
    role model0 stage install model1;
  (* installed slot matches; now the OTHER slot is untouched (the install  *)
  (* writes exactly one traffic slot), and the handshake secret + TH_SH    *)
  (* checkpoint are unchanged (install only rewrites one hs_keys field).   *)
  assert (model1.model_handshake.hs_keys.ks_handshake_secret ==
          model0.model_handshake.hs_keys.ks_handshake_secret);
  assert (transcript_checkpoint_bytes TH_SH model1.model_handshake ==
          transcript_checkpoint_bytes TH_SH model0.model_handshake);
  (match inst_label with
   | ClientTraffic ->
     assert (traffic_material_for_label
       model1.model_handshake.hs_keys TrafficHandshake ServerTraffic ==
             traffic_material_for_label
       model0.model_handshake.hs_keys TrafficHandshake ServerTraffic);
     if Some?
          (traffic_material_for_label
            model0.model_handshake.hs_keys TrafficHandshake ServerTraffic)
     then
       lemma_handshake_traffic_label_match_expected_preserved
         ServerTraffic model0 model1
   | ServerTraffic ->
     assert (traffic_material_for_label
       model1.model_handshake.hs_keys TrafficHandshake ClientTraffic ==
             traffic_material_for_label
       model0.model_handshake.hs_keys TrafficHandshake ClientTraffic);
     if Some?
          (traffic_material_for_label
            model0.model_handshake.hs_keys TrafficHandshake ClientTraffic)
     then
       lemma_handshake_traffic_label_match_expected_preserved
         ClientTraffic model0 model1);
  assert (first_epoch_handshake_traffic_material_slots_match_expected_model
    model1)

(* H6: model-step preservation of the slots-match invariant.            *)
let lemma_step_model_preserves_first_epoch_handshake_traffic_material_slots_match_expected_model
  (role:endpoint_role)
  (model0:connection_model)
  (ev:conn_event)
  (model1:connection_model)
  : Lemma
      (requires
        model0.model_config.config_role == role /\
        handshake_traffic_key_slot_stage_shape_for_role role model0 /\
        handshake_secret_requires_shared_secret model0 /\
        application_traffic_install_checkpoint_ready_for_role role model0 /\
        first_epoch_handshake_traffic_material_slots_match_expected_model
          model0 /\
        legal_event model0 ev /\
        step_model model0 ev == Some model1)
      (ensures
        first_epoch_handshake_traffic_material_slots_match_expected_model
          model1)
=
  let hs0 = model0.model_handshake in
  lemma_step_model_preserves_handshake_traffic_key_slot_stage_shape_for_role
    role model0 ev model1;
  lemma_step_model_preserves_application_traffic_install_checkpoint_ready_for_role
    role model0 ev model1;
  match ev with
  | ConnLocalEvent local ->
    (match local, model0.model_control with
     | LocalInstallTrafficKeys install, ControlHandshaking stage ->
       assert (role == ClientEndpoint);
       (match install.install_epoch with
        | TrafficHandshake ->
          lemma_expected_traffic_secret_client_projection
            hs0 install.install_epoch install.install_direction;
          lemma_update_key_schedule_with_install_client_projection
            hs0.hs_keys install;
          assert (model1.model_handshake ==
            { hs0 with
                hs_keys =
                  update_key_schedule_with_install_for_role
                    ClientEndpoint
                    hs0.hs_keys
                    install });
          lemma_first_epoch_handshake_slots_preserved_on_handshake_install
            ClientEndpoint model0 stage install model1
        | TrafficApplication ->
          lemma_first_epoch_handshake_slots_preserved_when_slots_unchanged_or_checkpoint_stable
            model0 model1)
     | LocalInstallTrafficKeysForRole role_install, ControlHandshaking stage ->
       let install = role_install.install_payload in
       assert (role_install.install_role == role);
       (match install.install_epoch with
        | TrafficHandshake ->
          assert (model1.model_handshake ==
            { hs0 with
                hs_keys =
                  update_key_schedule_with_install_for_role
                    role
                    hs0.hs_keys
                    install });
          lemma_first_epoch_handshake_slots_preserved_on_handshake_install
            role model0 stage install model1
        | TrafficApplication ->
          lemma_first_epoch_handshake_slots_preserved_when_slots_unchanged_or_checkpoint_stable
            model0 model1)
     | LocalDeriveSharedSecret _, _ ->
       (* The one non-install local step that moves [ks_handshake_secret]. *)
       (* Its legality pins [ks_shared_secret == None]; the companion then  *)
       (* forces [ks_handshake_secret == None], so a Some handshake slot    *)
       (* would give a None expected material, contradicting the IH match.  *)
       (* Hence both slots are absent, and they are untouched by the derive.*)
       assert (model0.model_handshake.hs_keys.ks_shared_secret == None);
       assert (model0.model_handshake.hs_keys.ks_handshake_secret == None);
       assert (model0.model_handshake.hs_keys.ks_client_handshake_traffic == None);
       assert (model0.model_handshake.hs_keys.ks_server_handshake_traffic == None);
       lemma_first_epoch_handshake_slots_preserved_when_slots_unchanged_or_checkpoint_stable
         model0 model1
     | _, _ ->
       lemma_first_epoch_handshake_slots_preserved_when_slots_unchanged_or_checkpoint_stable
         model0 model1)
  | ConnNetworkEvent msg ->
    lemma_first_epoch_handshake_slots_preserved_when_slots_unchanged_or_checkpoint_stable
      model0 model1
  | ConnProtectedHandshake step ->
    (* A protected-handshake step is a RECEIVED handshake message step, so it
       is covered by exactly the same reasoning as the `ConnNetworkEvent` arm:
       no `step_handshake_message` arm writes a first-epoch handshake traffic
       slot, `ks_handshake_secret`, or the `TH_SH` checkpoint.  The extra
       post-processing rewrites only `model_record` and
       `model_handshake.hs_buffers`, neither of which the slot/checkpoint
       predicates read. *)
    lemma_first_epoch_handshake_slots_preserved_when_slots_unchanged_or_checkpoint_stable
      model0 model1

#pop-options

(* ------------------------------------------------------------------ *)
(* Closure: [connection_state_consistent] -> handshake slots-match.    *)
(* Model-only [stable_on_closure], reusing the Brick-3-Part-1 pattern. *)
(* ------------------------------------------------------------------ *)
let handshake_slots_match_shape (st:connection_state) : prop =
  handshake_traffic_key_slot_stage_shape_for_role
    st.cs_model.model_config.config_role st.cs_model /\
  handshake_secret_requires_shared_secret st.cs_model /\
  application_traffic_install_checkpoint_ready_for_role
    st.cs_model.model_config.config_role st.cs_model /\
  first_epoch_handshake_traffic_material_slots_match_expected_model
    st.cs_model

let lemma_delta_handshake_slots_match_shape
  (st0 st1:connection_state)
  : Lemma
      (requires
        handshake_slots_match_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures handshake_slots_match_shape st1)
=
  eliminate exists delta. legal_connection_delta st0 delta st1
  with
    (let role = st0.cs_model.model_config.config_role in
     lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
     assert (st1.cs_model.model_config == st0.cs_model.model_config);
     lemma_step_model_preserves_handshake_traffic_key_slot_stage_shape_for_role
       role st0.cs_model delta.delta_event st1.cs_model;
     lemma_step_model_preserves_handshake_secret_requires_shared_secret
       st0.cs_model delta.delta_event st1.cs_model;
     lemma_step_model_preserves_application_traffic_install_checkpoint_ready_for_role
       role st0.cs_model delta.delta_event st1.cs_model;
     lemma_step_model_preserves_first_epoch_handshake_traffic_material_slots_match_expected_model
       role st0.cs_model delta.delta_event st1.cs_model)

let lemma_single_step_handshake_slots_match_shape (_:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern (handshake_slots_match_shape y);
                    (connection_state_single_step x y)}
          handshake_slots_match_shape x /\
          connection_state_single_step x y ==>
          handshake_slots_match_shape y)
=
  introduce forall (x:connection_state) (y:connection_state).
    handshake_slots_match_shape x /\
    connection_state_single_step x y ==>
    handshake_slots_match_shape y
  with
    introduce _ ==> _ with
    lemma_delta_handshake_slots_match_shape x y

let lemma_initial_handshake_slots_match_shape (cfg:connection_config)
  : Lemma (ensures handshake_slots_match_shape (initial cfg))
=
  ()

let lemma_connection_state_consistent_first_epoch_handshake_traffic_material_slots_match_expected
  (st:connection_state)
  : Lemma
      (requires connection_state_consistent st)
      (ensures
        first_epoch_handshake_traffic_material_slots_match_expected st)
=
  lemma_initial_handshake_slots_match_shape st.cs_model.model_config;
  lemma_single_step_handshake_slots_match_shape ();
  let p = handshake_slots_match_shape in
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure connection_state_single_step p stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st);
  assert
    (first_epoch_handshake_traffic_material_slots_match_expected_model
      st.cs_model);
  assert
    (first_epoch_handshake_traffic_material_slots_match_expected
      (state_of_model_for_first_epoch_application_material st.cs_model));
  assert
    (first_epoch_handshake_traffic_material_slots_match_expected st)

(* ------------------------------------------------------------------------ *)
(* Brick 3.6 : positive record-epoch lemmas.                                 *)
(*                                                                           *)
(* From bare consistency plus a RECORD-LEVEL key-presence hypothesis         *)
(* [Some? record_direction.R.key], derive [record_direction.R.epoch ==       *)
(* R.Handshake] at the client-Finished send/delivery control points.  The    *)
(* record-level hypothesis excludes [R.Initial] DIRECTLY: consistency's      *)
(* [record_keys_match_key_schedule_for_role] Initial arm forces              *)
(* [R.key == None], contradicting [Some?].  [R.Application] is excluded by    *)
(* the committed negative-epoch lemmas.  Three arms exhausted -> Handshake.   *)
(* Record-level (not key-schedule-slot) hypothesis is deliberate: it is      *)
(* exactly what the discharge sites supply (seal at send / open_record at    *)
(* delivery both yield [record.key == Some]) and it avoids any reachable-     *)
(* shape induction -- the key-schedule Initial arm says nothing about the     *)
(* slot, so a slot-level hypothesis would NOT exclude Initial without one.    *)
(* ------------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_client_finished_verified_write_epoch_handshake
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        st.cs_model.model_control == ControlHandshaking HsServerFinishedVerified /\
        Some? st.cs_model.model_record.record_write.R.key)
      (ensures
        st.cs_model.model_record.record_write.R.epoch == R.Handshake)
=
  let m = st.cs_model in
  lemma_connection_state_consistent_record_keys_consistent_for_config_role st;
  lemma_client_finished_verified_write_epoch_not_application st;
  let keys = m.model_handshake.hs_keys in
  let rw = m.model_record.record_write in
  assert (model_record_keys_consistent_for_role ClientEndpoint m);
  assert (record_keys_match_key_schedule_for_role
            ClientEndpoint TrafficWrite m.model_control keys rw);
  assert (rw.R.epoch =!= R.Application);
  match rw.R.epoch with
  | R.Handshake -> ()
  | R.Application -> ()
  | R.Initial -> assert (rw.R.key == None)

let lemma_server_finished_sent_read_epoch_handshake
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        st.cs_model.model_control == ControlHandshaking HsServerFinishedSent /\
        Some? st.cs_model.model_record.record_read.R.key)
      (ensures
        st.cs_model.model_record.record_read.R.epoch == R.Handshake)
=
  let m = st.cs_model in
  lemma_connection_state_consistent_record_keys_consistent_for_config_role st;
  lemma_handshaking_nonfinal_read_not_application st;
  let keys = m.model_handshake.hs_keys in
  let rr = m.model_record.record_read in
  assert (model_record_keys_consistent_for_role ServerEndpoint m);
  assert (record_keys_match_key_schedule_for_role
            ServerEndpoint TrafficRead m.model_control keys rr);
  assert (rr.R.epoch =!= R.Application);
  match rr.R.epoch with
  | R.Handshake -> ()
  | R.Application -> ()
  | R.Initial -> assert (rr.R.key == None)
#pop-options

(* ------------------------------------------------------------------------ *)
(* Brick 3.7 : NON-READY key-schedule lineage producer.                      *)
(*                                                                           *)
(* Exposes [connection_supported_profile_key_schedule_lineage] from bare     *)
(* consistency plus [Some? ks_shared_secret].  The committed interface only  *)
(* exposes the app-keys-GATED producer [lemma_connection_application_keys_   *)
(* supported_profile_key_schedule_lineage] (:102), whose precondition        *)
(* [application_record_keys_installed_for_role] is NOT available at the       *)
(* client-Finished send.  This producer routes instead through the INTERNAL  *)
(* reachable-shape lemma (:1171): its [supported_profile_base_lineage_or_    *)
(* empty] conjunct has only all-None / all-Some / False arms, so a present    *)
(* shared secret collapses it to the all-Some arm -- master included --        *)
(* whence [lemma_supported_profile_base_lineage_or_empty_to_lineage] gives    *)
(* the full lineage.  No readiness, no app-keys gate.                         *)
(* ------------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_connection_state_consistent_shared_secret_supported_profile_key_schedule_lineage
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret)
      (ensures
        connection_supported_profile_key_schedule_lineage st)
=
  lemma_connection_state_consistent_supported_profile_key_schedule_reachable_shape st;
  let keys = st.cs_model.model_handshake.hs_keys in
  assert (supported_profile_base_lineage_or_empty keys);
  match
    keys.ks_shared_secret,
    keys.ks_early_secret,
    keys.ks_handshake_secret,
    keys.ks_master_secret
  with
  | Some _, Some _, Some _, Some _ ->
    lemma_supported_profile_base_lineage_or_empty_to_lineage keys
  | _ -> assert False
#pop-options

(* Gate 2a: a present handshake-traffic slot forces the shared secret.  From    *)
(* [traffic_material_slots_have_base_secret] (slot ⟹ handshake_secret) and       *)
(* [supported_profile_base_lineage_or_empty] (all-four None or all-four Some),   *)
(* a [Some? ks_handshake_secret] excludes the all-None arm, so [ks_shared_secret] *)
(* is [Some].  Control-independent (reachable shape from bare consistency), hence  *)
(* usable at [ControlFailed]. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_consistent_client_handshake_traffic_slot_shared_secret
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        Some? st.cs_model.model_handshake.hs_keys.ks_client_handshake_traffic)
      (ensures Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret)
=
  lemma_connection_state_consistent_supported_profile_key_schedule_reachable_shape st;
  let keys = st.cs_model.model_handshake.hs_keys in
  assert (traffic_material_slots_have_base_secret keys);
  assert (Some? keys.ks_handshake_secret);
  assert (supported_profile_base_lineage_or_empty keys)
#pop-options

(* Gate-2a slimming: the [Some? ks_shared_secret] branch of                    *)
(* [server_x25519_reachable_shape], surfaced directly in terms of the (public) *)
(* Correspondence projections.  This is the one already-proven consequence the *)
(* ServerHelloSelectionLink module needs at a possibly-[ControlFailed] server,  *)
(* so that module no longer re-derives the x25519 reachable-shape machinery.     *)
(* Control-independent; the [ControlFailed] arm is the genuine disjunction       *)
(* (pre-ServerHello vs key-share projection). *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_consistent_server_x25519_shared_secret_projection
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        Some? st.cs_model.model_handshake.hs_keys.ks_shared_secret)
      (ensures
        (match st.cs_model.model_control with
         | ControlHandshaking HsClientHelloReceived ->
           server_x25519_pre_server_hello_projection st
         | ControlFailed _ ->
           server_x25519_pre_server_hello_projection st \/
           server_x25519_key_share_projection st
         | _ ->
           stable_server_x25519_key_share_projection st))
=
  lemma_connection_state_consistent_server_x25519_reachable_shape st
#pop-options

(* ================================================================== *)
(* PHASE 1A : PERSISTENCE of the CLIENT handshake READ record<->slot   *)
(* material link across ControlFailed.                                 *)
(*                                                                     *)
(* [model_record_keys_consistent_for_role] is VACUOUS at ControlFailed *)
(* ([ControlFailed -> True] arm), so the record<->slot link is not      *)
(* derivable from bare consistency at a failed client.  But the link   *)
(* is CONTROL-FREE (reads only [model_record] + [hs_keys]) and BOTH     *)
(* are frozen by [fail_model], so it PERSISTS: established at the live  *)
(* install/handshake control (existing consistency producer) and       *)
(* transferred verbatim across the fail step.  We prove it as a         *)
(* reachable-shape [stable_on_closure], embedding the (already stable)  *)
(* [record_keys_consistent_config_role_shape] so the NON-failed re-      *)
(* derivation has consistency available and the FAILED transfer reads    *)
(* the (control-ungated) link from the pre-state.                       *)
(* ================================================================== *)

let client_hs_read_slot_link (model:connection_model) : prop =
  record_direction_material_matches_key_schedule_for_role
    ClientEndpoint TrafficRead
    (traffic_id TrafficHandshake ServerTraffic)
    model

let client_hs_read_link_shape (st:connection_state) : prop =
  record_keys_consistent_config_role_shape st /\
  ( (st.cs_model.model_config.config_role == ClientEndpoint /\
     R.Handshake? st.cs_model.model_record.record_read.R.epoch) ==>
    client_hs_read_slot_link st.cs_model )

(* A legal step whose RESULT lands at [ControlFailed] preserves           *)
(* [model_record] and the key schedule (fail is a pure control/failure    *)
(* field update; [fail_model] at StateMachine.fst:303).                   *)
#push-options "--fuel 4 --ifuel 10 --z3rlimit 200"
let lemma_step_failed_result_preserves_record_keys
  (m m':connection_model) (ce:conn_event)
  : Lemma
      (requires
        legal_event m ce /\ step_model m ce == Some m' /\
        ControlFailed? m'.model_control)
      (ensures
        m'.model_record == m.model_record /\
        m'.model_handshake.hs_keys == m.model_handshake.hs_keys)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_delta_client_hs_read_link_shape
  (st0 st1:connection_state)
  : Lemma
      (requires
        client_hs_read_link_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures client_hs_read_link_shape st1)
=
  eliminate exists delta. legal_connection_delta st0 delta st1
  with
  (
    lemma_delta_record_keys_consistent_config_role_shape st0 st1;
    lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    introduce
      (st1.cs_model.model_config.config_role == ClientEndpoint /\
       R.Handshake? st1.cs_model.model_record.record_read.R.epoch)
      ==> client_hs_read_slot_link st1.cs_model
    with
    (
      if ControlFailed? st1.cs_model.model_control then
      (
        lemma_step_failed_result_preserves_record_keys
          st0.cs_model st1.cs_model delta.delta_event;
        assert (st1.cs_model.model_record == st0.cs_model.model_record);
        assert (st1.cs_model.model_handshake.hs_keys ==
                  st0.cs_model.model_handshake.hs_keys);
        assert (R.Handshake? st0.cs_model.model_record.record_read.R.epoch);
        assert (st0.cs_model.model_config.config_role == ClientEndpoint);
        assert (client_hs_read_slot_link st0.cs_model)
      )
      else
      (
        assert (record_keys_consistent_config_role_shape st1);
        assert (model_record_keys_consistent_for_role
                  st1.cs_model.model_config.config_role st1.cs_model);
        assert (model_record_keys_consistent_for_role ClientEndpoint st1.cs_model);
        lemma_handshake_record_direction_material_matches_key_schedule_for_role
          ClientEndpoint TrafficRead st1.cs_model;
        assert_norm
          (traffic_label_for_endpoint_direction ClientEndpoint TrafficRead == ServerTraffic)
      )
    )
  )
#pop-options

let lemma_single_step_client_hs_read_link_shape (_:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern (client_hs_read_link_shape y);
                    (connection_state_single_step x y)}
          client_hs_read_link_shape x /\
          connection_state_single_step x y ==>
          client_hs_read_link_shape y)
=
  introduce forall (x:connection_state) (y:connection_state).
    client_hs_read_link_shape x /\
    connection_state_single_step x y ==>
    client_hs_read_link_shape y
  with
    introduce _ ==> _ with
    lemma_delta_client_hs_read_link_shape x y

let lemma_initial_client_hs_read_link_shape (cfg:connection_config)
  : Lemma (ensures client_hs_read_link_shape (initial cfg))
=
  lemma_initial_record_keys_consistent_config_role_shape cfg

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_client_hs_read_slot_link_persist
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ClientEndpoint /\
        R.Handshake? st.cs_model.model_record.record_read.R.epoch)
      (ensures
        record_direction_material_matches_key_schedule_for_role
          ClientEndpoint TrafficRead
          (traffic_id TrafficHandshake ServerTraffic)
          st.cs_model)
=
  lemma_initial_client_hs_read_link_shape st.cs_model.model_config;
  lemma_single_step_client_hs_read_link_shape ();
  let p = client_hs_read_link_shape in
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure connection_state_single_step p stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)
#pop-options

(* ================================================================== *)
(* PHASE 1A MIRROR : PERSISTENCE of the SERVER handshake READ          *)
(* record<->slot material link across ControlFailed.                   *)
(*                                                                     *)
(* Exact mirror of [lemma_client_hs_read_slot_link_persist], for the   *)
(* SERVER's handshake READ direction (label [ClientTraffic]).  Same     *)
(* justification: [model_record_keys_consistent_for_role] is VACUOUS at *)
(* [ControlFailed], but the link is CONTROL-FREE (reads only            *)
(* [model_record] + [hs_keys]) and both are frozen by [fail_model], so  *)
(* it PERSISTS across the fail step.                                    *)
(*                                                                     *)
(* This is what lets the client->server faithful-decode bridge          *)
(* ([hs_channel_seal_ok]'s ToServer arm) fire at a FAILED server        *)
(* reader, exactly as the client-side lemma does for a failed client.   *)
(* ================================================================== *)

let server_hs_read_slot_link (model:connection_model) : prop =
  record_direction_material_matches_key_schedule_for_role
    ServerEndpoint TrafficRead
    (traffic_id TrafficHandshake ClientTraffic)
    model

let server_hs_read_link_shape (st:connection_state) : prop =
  record_keys_consistent_config_role_shape st /\
  ( (st.cs_model.model_config.config_role == ServerEndpoint /\
     R.Handshake? st.cs_model.model_record.record_read.R.epoch) ==>
    server_hs_read_slot_link st.cs_model )

#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_delta_server_hs_read_link_shape
  (st0 st1:connection_state)
  : Lemma
      (requires
        server_hs_read_link_shape st0 /\
        connection_state_single_step st0 st1)
      (ensures server_hs_read_link_shape st1)
=
  eliminate exists delta. legal_connection_delta st0 delta st1
  with
  (
    lemma_delta_record_keys_consistent_config_role_shape st0 st1;
    lemma_step_model_preserves_config st0.cs_model delta.delta_event st1.cs_model;
    assert (st1.cs_model.model_config == st0.cs_model.model_config);
    introduce
      (st1.cs_model.model_config.config_role == ServerEndpoint /\
       R.Handshake? st1.cs_model.model_record.record_read.R.epoch)
      ==> server_hs_read_slot_link st1.cs_model
    with
    (
      if ControlFailed? st1.cs_model.model_control then
      (
        lemma_step_failed_result_preserves_record_keys
          st0.cs_model st1.cs_model delta.delta_event;
        assert (st1.cs_model.model_record == st0.cs_model.model_record);
        assert (st1.cs_model.model_handshake.hs_keys ==
                  st0.cs_model.model_handshake.hs_keys);
        assert (R.Handshake? st0.cs_model.model_record.record_read.R.epoch);
        assert (st0.cs_model.model_config.config_role == ServerEndpoint);
        assert (server_hs_read_slot_link st0.cs_model)
      )
      else
      (
        assert (record_keys_consistent_config_role_shape st1);
        assert (model_record_keys_consistent_for_role
                  st1.cs_model.model_config.config_role st1.cs_model);
        assert (model_record_keys_consistent_for_role ServerEndpoint st1.cs_model);
        lemma_handshake_record_direction_material_matches_key_schedule_for_role
          ServerEndpoint TrafficRead st1.cs_model;
        assert_norm
          (traffic_label_for_endpoint_direction ServerEndpoint TrafficRead == ClientTraffic)
      )
    )
  )
#pop-options

let lemma_single_step_server_hs_read_link_shape (_:unit)
  : Lemma
      (ensures
        forall (x:connection_state) (y:connection_state).
          {:pattern (server_hs_read_link_shape y);
                    (connection_state_single_step x y)}
          server_hs_read_link_shape x /\
          connection_state_single_step x y ==>
          server_hs_read_link_shape y)
=
  introduce forall (x:connection_state) (y:connection_state).
    server_hs_read_link_shape x /\
    connection_state_single_step x y ==>
    server_hs_read_link_shape y
  with
    introduce _ ==> _ with
    lemma_delta_server_hs_read_link_shape x y

let lemma_initial_server_hs_read_link_shape (cfg:connection_config)
  : Lemma (ensures server_hs_read_link_shape (initial cfg))
=
  lemma_initial_record_keys_consistent_config_role_shape cfg

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
let lemma_server_hs_read_slot_link_persist
  (st:connection_state)
  : Lemma
      (requires
        connection_state_consistent st /\
        st.cs_model.model_config.config_role == ServerEndpoint /\
        R.Handshake? st.cs_model.model_record.record_read.R.epoch)
      (ensures
        record_direction_material_matches_key_schedule_for_role
          ServerEndpoint TrafficRead
          (traffic_id TrafficHandshake ClientTraffic)
          st.cs_model)
=
  lemma_initial_server_hs_read_link_shape st.cs_model.model_config;
  lemma_single_step_server_hs_read_link_shape ();
  let p = server_hs_read_link_shape in
  let stable :
    squash (
      forall (x:connection_state) (y:connection_state).
        {:pattern (p y); (connection_state_single_step x y)}
        p x /\ connection_state_single_step x y ==> p y) = () in
  RTC.stable_on_closure connection_state_single_step p stable;
  assert (p (initial st.cs_model.model_config));
  assert (connection_state_evolves (initial st.cs_model.model_config) st);
  assert (p st)
#pop-options
