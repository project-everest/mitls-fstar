module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Replay

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.StateMachine
module SMCan = TLS13.Spec.StateMachine.Canonical
module SMCorr = TLS13.Spec.StateMachine.Correspondence
module SMIds = TLS13.Spec.StateMachine.KeyIdentifiers
module SMReplay = TLS13.Spec.StateMachine.Replay
module EC = TLS13.Spec.Endpoint.Client
module ES = TLS13.Spec.Endpoint.Server
module CD = TLS13.Impl.Client.Driver
module M = TLS13.Messages
module Sem   = TLS13.Wire.Semantics
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GFin = TLS13.Wire.Generated.Finished
module Pairing = TLS13.Impl.Driver.Pairing
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTCFRE = TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality
module PNTCFRR = TLS13.Impl.Driver.PairingNoTailClientFinishedReceiverReplay
module PNTCFR = TLS13.Impl.Driver.PairingNoTailClientFinishedReplay
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTPPD = TLS13.Impl.Driver.PairingNoTailProtectedProjectionDerivation
module PNTRB = TLS13.Impl.Driver.PairingNoTailRawBridge
module PNTSFR = TLS13.Impl.Driver.PairingNoTailServerFlightReplay
module PNTSFS = TLS13.Impl.Driver.PairingNoTailServerFlightStaged
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module SD = TLS13.Impl.Server.Driver
module Tac = FStar.Tactics
module WFL = TLS13.Spec.WireFormatLemmas
module RA = TLS13.ConnectionState.ProtectedWireRecordAlignment
module PWL = TLS13.ConnectionState.ProtectedWireBase
module R = TLS13.Record.Spec
module T = TLS13.Types
module PWReplay = TLS13.ConnectionState.ProtectedWireReplay
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module X = TLS13.X509.Spec
module K = TLS13.Keys
module W = TLS13.Wire.Spec
module L = FStar.List.Tot
module CSL = TLS13.ConnectionState.Lemmas
module WRD = TLS13.Wire.Spec.RevealDecode

module Foundation = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Foundation
open TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Foundation

#push-options "--split_queries always --z3rlimit 10"

#push-options "--split_queries always --z3rlimit 10"

noextract
let step_next (m:CS.connection_model) (ev:CS.conn_event) : GTot CS.connection_model =
  match CS.step_model m ev with
  | Some m' -> m'
  | None -> m
#pop-options

// ===================================================================
// Transplanted, probe-validated helper lemmas for the pack_inputs proof
// ===================================================================

#push-options "--z3rlimit 10"
noextract
let peel_sent
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (final:CS.connection_model)
  : Lemma
      (requires (exists rs rr. SMReplay.conn_events_sent_seal_replay model (ev :: rest) rs rr final))
      (ensures
        CS.legal_event model ev /\
        CS.step_model model ev == Some (step_next model ev) /\
        (exists ts tr. SMReplay.conn_events_sent_seal_replay (step_next model ev) rest ts tr final))
=
  eliminate exists rs rr. SMReplay.conn_events_sent_seal_replay model (ev :: rest) rs rr final
  with (
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
  with
  ( introduce exists ts tr. SMReplay.conn_events_sent_seal_replay (step_next model ev) rest ts tr final
    with tail_sent tail_received and () ) )

noextract
let peel_received
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (final:CS.connection_model)
  : Lemma
      (requires (exists rs rr. SMReplay.conn_events_received_decode_replay model (ev :: rest) rs rr final))
      (ensures
        CS.legal_event model ev /\
        CS.step_model model ev == Some (step_next model ev) /\
        (exists ts tr. SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts tr final))
=
  eliminate exists rs rr. SMReplay.conn_events_received_decode_replay model (ev :: rest) rs rr final
  with (
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  with
  ( introduce exists ts tr. SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts tr final
    with tail_sent tail_received and () ) )

noextract
let peel_nil_sent (model final:CS.connection_model)
  : Lemma
      (requires (exists rs rr. SMReplay.conn_events_sent_seal_replay model [] rs rr final))
      (ensures model == final)
=
  eliminate exists rs rr. SMReplay.conn_events_sent_seal_replay model [] rs rr final
  with ( assert (SMReplay.conn_events_sent_seal_replay model [] rs rr final) )

noextract
let peel_nil_received (model final:CS.connection_model)
  : Lemma
      (requires (exists rs rr. SMReplay.conn_events_received_decode_replay model [] rs rr final))
      (ensures model == final)
=
  eliminate exists rs rr. SMReplay.conn_events_received_decode_replay model [] rs rr final
  with ( assert (SMReplay.conn_events_received_decode_replay model [] rs rr final) )
#pop-options

noextract
let peel_last_sent
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (final:CS.connection_model)
  : Lemma
      (requires
        exists rs rr.
          SMReplay.conn_events_sent_seal_replay model [ev] rs rr final)
      (ensures
        CS.step_model model ev == Some (step_next model ev) /\
        CS.step_model model ev == Some final /\
        step_next model ev == final /\
        final == step_next model ev)
=
  peel_sent model ev [] final;
  peel_nil_sent (step_next model ev) final

noextract
let peel_last_received
  (model:CS.connection_model)
  (ev:CS.conn_event)
  (final:CS.connection_model)
  : Lemma
      (requires
        exists rs rr.
          SMReplay.conn_events_received_decode_replay model [ev] rs rr final)
      (ensures
        CS.step_model model ev == Some (step_next model ev) /\
        CS.step_model model ev == Some final /\
        step_next model ev == final /\
        final == step_next model ev)
=
  peel_received model ev [] final;
  peel_nil_received (step_next model ev) final

noextract
let lemma_equal_models_preserve_control
  (model model':CS.connection_model)
  : Lemma
      (requires model == model')
      (ensures model'.CS.model_control == model.CS.model_control)
= ()

noextract
let lemma_equal_models_application_control
  (model model':CS.connection_model)
  : Lemma
      (requires
        model == model' /\
        model.CS.model_control == CS.ControlApplicationData)
      (ensures model'.CS.model_control == CS.ControlApplicationData)
= ()

noextract
let lemma_equal_models_client_finished_slot
  (model model':CS.connection_model)
  (fin:GFin.finished)
  : Lemma
      (requires
        model == model' /\
        model.CS.model_handshake.CS.hs_client_finished == Some fin)
      (ensures
        model'.CS.model_handshake.CS.hs_client_finished == Some fin)
= ()

// Keep each step-model unfolding in its own small query. The corresponding
// repository lemma is intentionally not exported by ConnectionState.Lemmas.
noextract
let lemma_step_model_transcript_delta_low_rlimit
  (model0:CS.connection_model)
  (ev:CS.conn_event)
  (model1:CS.connection_model)
  : Lemma
      (requires CS.step_model model0 ev == Some model1)
      (ensures
        (let t0 = model0.CS.model_handshake.CS.hs_transcript in
        match ev with
        | CS.ConnLocalEvent local ->
          (match local with
           | CS.LocalVerifyFinished fin ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript
               (B.append t0 (W.serialize_handshake (M.Finished fin)))
           | CS.LocalVerifyClientFinished fin ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript
               (B.append t0 (W.serialize_handshake (M.Finished fin)))
           | _ ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript t0)
        | CS.ConnNetworkEvent msg ->
          (match msg.CL.message_direction, msg.CL.message_value with
           | CL.Sent, M.TlsHandshake (M.ClientHello ch)
           | CL.Received, M.TlsHandshake (M.ClientHello ch) ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript
               (B.append t0 (W.serialize_handshake (M.ClientHello ch)))
           | CL.Received, M.TlsHandshake (M.ServerHello sh)
           | CL.Sent, M.TlsHandshake (M.ServerHello sh) ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript
               (B.append t0 (W.serialize_handshake (M.ServerHello sh)))
           | CL.Sent, M.TlsHandshake (M.EncryptedExtensions ee)
           | CL.Received, M.TlsHandshake (M.EncryptedExtensions ee) ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript
               (B.append t0 (W.serialize_handshake (M.EncryptedExtensions ee)))
           | CL.Sent, M.TlsHandshake (M.Certificate cert)
           | CL.Received, M.TlsHandshake (M.Certificate cert) ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript
               (B.append t0 (W.serialize_handshake (M.Certificate cert)))
           | CL.Sent, M.TlsHandshake (M.CertificateVerify cv)
           | CL.Received, M.TlsHandshake (M.CertificateVerify cv) ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript
               (B.append t0 (W.serialize_handshake (M.CertificateVerify cv)))
           | CL.Sent, M.TlsHandshake (M.Finished fin) ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript
               (B.append t0 (W.serialize_handshake (M.Finished fin)))
           | _, _ ->
             Seq.equal model1.CS.model_handshake.CS.hs_transcript t0)))
=
  match ev with
  | CS.ConnLocalEvent local ->
    (match local with
     | CS.LocalVerifyFinished _ -> ()
     | CS.LocalVerifyClientFinished _ -> ()
     | _ -> ())
  | CS.ConnNetworkEvent msg ->
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
     | _, _ -> ())

// Linchpin (A): transcript equality of server model5 and client model4
#push-options "--z3rlimit 10 --split_queries always"
noextract
let lemma_transcript_eq
  (server_ch:GCH.clientHello) (client_ch:GCH.clientHello)
  (server_sh:GSH.serverHello) (client_sh:GSH.serverHello)
  (selection:CS.server_handshake_selection)
  (server_shared client_shared:C.x25519_shared_secret)
  (start:CS.handshake_start)
  (server_model0 server_model1 server_model2 server_model3 server_model4 server_model5:CS.connection_model)
  (client_model0 client_model1 client_model2 client_model3 client_model4:CS.connection_model)
  : Lemma
      (requires
        FStar.Seq.equal (W.serialize_handshake (M.ClientHello client_ch)) (W.serialize_handshake (M.ClientHello server_ch)) /\
        FStar.Seq.equal (W.serialize_handshake (M.ServerHello server_sh)) (W.serialize_handshake (M.ServerHello client_sh)) /\
        CS.step_model server_model0 (CS.ConnLocalEvent CS.LocalStartServer) == Some server_model1 /\
        CS.step_model server_model1 (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ClientHello server_ch); }) == Some server_model2 /\
        CS.step_model server_model2 (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) == Some server_model3 /\
        CS.step_model server_model3 (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) == Some server_model4 /\
        CS.step_model server_model4 (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ServerHello server_sh); }) == Some server_model5 /\
        CS.step_model client_model0 (CS.ConnLocalEvent (CS.LocalStartHandshake start)) == Some client_model1 /\
        CS.step_model client_model1 (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello client_ch); }) == Some client_model2 /\
        CS.step_model client_model2 (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello client_sh); }) == Some client_model3 /\
        CS.step_model client_model3 (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) == Some client_model4 /\
        server_model0.CS.model_handshake.CS.hs_transcript == FStar.Seq.empty /\
        client_model0.CS.model_handshake.CS.hs_transcript == FStar.Seq.empty)
      (ensures
        FStar.Seq.equal
          server_model5.CS.model_handshake.CS.hs_transcript
          client_model4.CS.model_handshake.CS.hs_transcript)
=
  lemma_step_model_transcript_delta_low_rlimit
    server_model0 (CS.ConnLocalEvent CS.LocalStartServer) server_model1;
  lemma_step_model_transcript_delta_low_rlimit
    server_model1
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
    })
    server_model2;
  lemma_step_model_transcript_delta_low_rlimit
    server_model2
    (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection))
    server_model3;
  lemma_step_model_transcript_delta_low_rlimit
    server_model3
    (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared))
    server_model4;
  lemma_step_model_transcript_delta_low_rlimit
    server_model4
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
    })
    server_model5;
  lemma_step_model_transcript_delta_low_rlimit
    client_model0
    (CS.ConnLocalEvent (CS.LocalStartHandshake start))
    client_model1;
  lemma_step_model_transcript_delta_low_rlimit
    client_model1
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
    })
    client_model2;
  lemma_step_model_transcript_delta_low_rlimit
    client_model2
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
    })
    client_model3;
  lemma_step_model_transcript_delta_low_rlimit
    client_model3
    (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared))
    client_model4;
  assert (Seq.equal
    server_model5.CS.model_handshake.CS.hs_transcript
    (B.append
      (W.serialize_handshake (M.ClientHello server_ch))
      (W.serialize_handshake (M.ServerHello server_sh))));
  assert (Seq.equal
    client_model4.CS.model_handshake.CS.hs_transcript
    (B.append
      (W.serialize_handshake (M.ClientHello client_ch))
      (W.serialize_handshake (M.ServerHello client_sh))))

// Linchpin (B): handshake secret equality of server model5 and client model4
noextract
let lemma_derive_shared_secret_sets_handshake_secret
  (model model':CS.connection_model)
  (shared:C.x25519_shared_secret)
  : Lemma
      (requires
        CS.step_model model
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared)) ==
          Some model')
      (ensures
        model'.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          Some (K.handshake_secret (K.early_secret B.empty) shared))
= ()

noextract
let lemma_sent_server_hello_preserves_handshake_secret
  (model model':CS.connection_model)
  (sh:GSH.serverHello)
  : Lemma
      (requires
        CS.step_model model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ServerHello sh);
          }) ==
          Some model')
      (ensures
        model'.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          model.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
= ()

noextract
let lemma_secret_eq
  (server_ch:GCH.clientHello) (server_sh:GSH.serverHello) (client_sh:GSH.serverHello) (client_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared client_shared:C.x25519_shared_secret)
  (start:CS.handshake_start)
  (server_model0 server_model1 server_model2 server_model3 server_model4 server_model5:CS.connection_model)
  (client_model0 client_model1 client_model2 client_model3 client_model4:CS.connection_model)
  : Lemma
      (requires
        FStar.Seq.equal server_shared client_shared /\
        CS.step_model server_model0 (CS.ConnLocalEvent CS.LocalStartServer) == Some server_model1 /\
        CS.step_model server_model1 (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ClientHello server_ch); }) == Some server_model2 /\
        CS.step_model server_model2 (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) == Some server_model3 /\
        CS.step_model server_model3 (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) == Some server_model4 /\
        CS.step_model server_model4 (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ServerHello server_sh); }) == Some server_model5 /\
        CS.step_model client_model0 (CS.ConnLocalEvent (CS.LocalStartHandshake start)) == Some client_model1 /\
        CS.step_model client_model1 (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello client_ch); }) == Some client_model2 /\
        CS.step_model client_model2 (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello client_sh); }) == Some client_model3 /\
        CS.step_model client_model3 (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) == Some client_model4)
      (ensures
        (match
          server_model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client_model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
         with
         | Some s5, Some s4 -> FStar.Seq.equal s5 s4
         | _, _ -> False))
=
  lemma_derive_shared_secret_sets_handshake_secret
    server_model3 server_model4 server_shared;
  lemma_sent_server_hello_preserves_handshake_secret
    server_model4 server_model5 server_sh;
  lemma_derive_shared_secret_sets_handshake_secret
    client_model3 client_model4 client_shared;
  FStar.Seq.lemma_eq_elim server_shared client_shared
#pop-options

// Linchpin (C): server-flight handshake write/read alignment via RA + forward push
#push-options "--z3rlimit 10 --split_queries always"
noextract
let lemma_server_flight_align
  (server_pre client_pre:CS.connection_model)
  (write_material read_material:CS.traffic_key_material)
  (server_after_write client_after_read server_after_read client_after_installs:CS.connection_model)
  : Lemma
      (requires
        (match
          server_pre.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          client_pre.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
         with
         | Some ss, Some cs -> Seq.equal ss cs
         | _, _ -> False) /\
        Seq.equal
          server_pre.CS.model_handshake.CS.hs_transcript
          client_pre.CS.model_handshake.CS.hs_transcript /\
        CS.traffic_install_matches_key_schedule_for_role
          CS.ServerEndpoint server_pre.CS.model_handshake
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = write_material; } /\
        CS.traffic_install_matches_key_schedule
          client_pre.CS.model_handshake
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = read_material; } /\
        CS.step_model server_pre
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = write_material; };
          })) == Some server_after_write /\
        CS.step_model server_after_write
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = read_material; };
          })) == Some server_after_read /\
        CS.step_model client_pre
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = read_material;
          })) == Some client_after_read /\
        CS.step_model client_after_read
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
            CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = write_material;
          })) == Some client_after_installs)
      (ensures PWL.write_read_record_material_aligned server_after_read client_after_installs)
=
  RA.lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
    server_pre client_pre write_material read_material server_after_write client_after_read;
  RA.lemma_step_sender_local_event_preserves_write_read_record_material_alignment
    server_after_write
    (CS.LocalInstallTrafficKeysForRole {
       CS.install_role = CS.ServerEndpoint;
       CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = read_material; };
     })
    server_after_read client_after_read;
  RA.lemma_step_receiver_local_event_preserves_write_read_record_material_alignment
    server_after_read client_after_read
    (CS.LocalInstallTrafficKeys {
       CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = write_material;
     })
    client_after_installs
#pop-options


// ===================================================================
// Field-tracking / inversion helpers for the pack_inputs proof
// ===================================================================
// install events preserve message fields + control stage
#push-options "--z3rlimit 10 --split_queries always"
noextract
let lemma_install_preserves_msg_fields
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.ControlHandshaking? m.CS.model_control /\
        (match ev with
         | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> True
         | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> True
         | _ -> False) /\
        CS.step_model m ev == Some m')
      (ensures
        m'.CS.model_control == m.CS.model_control /\
        m'.CS.model_handshake.CS.hs_encrypted_extensions == m.CS.model_handshake.CS.hs_encrypted_extensions /\
        m'.CS.model_handshake.CS.hs_certificate == m.CS.model_handshake.CS.hs_certificate /\
        m'.CS.model_handshake.CS.hs_certificate_verify == m.CS.model_handshake.CS.hs_certificate_verify /\
        m'.CS.model_handshake.CS.hs_server_finished == m.CS.model_handshake.CS.hs_server_finished /\
        m'.CS.model_handshake.CS.hs_client_finished == m.CS.model_handshake.CS.hs_client_finished)
= ()
#pop-options

// cover ==> both e13 and e14 are application-install events (shape for preservation)
#push-options "--z3rlimit 10 --split_queries always"
noextract
let lemma_cover_both_install (e13 e14:CS.conn_event)
  : Lemma
      (requires PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures
        (match e13 with
         | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> True
         | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> True
         | _ -> False) /\
        (match e14 with
         | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> True
         | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> True
         | _ -> False))
=
  let goal =
    (match e13 with
     | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> True
     | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> True
     | _ -> False) /\
    (match e14 with
     | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys _) -> True
     | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole _) -> True
     | _ -> False) in
  PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
  eliminate
    (PNTCAS.client_no_tail_application_write_install_event e13 /\
     PNTCAS.client_no_tail_application_read_install_event e14) \/
    (PNTCAS.client_no_tail_application_read_install_event e13 /\
     PNTCAS.client_no_tail_application_write_install_event e14)
  with (
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases e13;
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases e14)
  and (
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases e13;
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases e14)
#pop-options

// ================= SERVER FLIGHT WALK =================
noextract
let lemma_role_install_preserves_control
  (model model':CS.connection_model)
  (role:CS.endpoint_role)
  (install:CS.traffic_key_install)
  : Lemma
      (requires
        CS.step_model model
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = role;
            CS.install_payload = install;
          })) ==
          Some model')
      (ensures model'.CS.model_control == model.CS.model_control)
= ()

noextract
let lemma_received_client_finished_sets_stage
  (model model':CS.connection_model)
  (fin:GFin.finished)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsServerFinishedSent /\
        CS.step_model model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished fin);
          }) ==
          Some model')
      (ensures
        model'.CS.model_control ==
          CS.ControlHandshaking CS.HsClientFinishedReceived)
= ()

noextract
let lemma_received_client_finished_updates_handshake
  (model model':CS.connection_model)
  (fin:GFin.finished)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsServerFinishedSent /\
        CS.step_model model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished fin);
          }) ==
          Some model')
      (ensures
        model'.CS.model_handshake ==
          { model.CS.model_handshake with CS.hs_client_finished = Some fin })
= ()

noextract
let lemma_verify_client_finished_preserves_handshake
  (model model':CS.connection_model)
  (fin:GFin.finished)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientFinishedReceived /\
        CS.step_model model
          (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)) ==
          Some model')
      (ensures
        model'.CS.model_handshake ==
          CS.append_handshake_to_transcript
            { model.CS.model_handshake with
                CS.hs_client_finished = Some fin
            }
            (M.Finished fin))
= ()

noextract
let lemma_verify_client_finished_sets_slot_low_rlimit
  (model model':CS.connection_model)
  (fin:GFin.finished)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsClientFinishedReceived /\
        CS.step_model model
          (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)) ==
          Some model')
      (ensures
        model'.CS.model_handshake.CS.hs_client_finished == Some fin)
= ()

noextract
let lemma_client_prefix_transcript_chain
  (m0 m1 m2 m3:CS.connection_model)
  (ch:GCH.clientHello)
  (sh:GSH.serverHello)
  : Lemma
      (requires
        m0.CS.model_handshake.CS.hs_transcript == B.empty /\
        Seq.equal
          m1.CS.model_handshake.CS.hs_transcript
          m0.CS.model_handshake.CS.hs_transcript /\
        Seq.equal
          m2.CS.model_handshake.CS.hs_transcript
          (B.append
            m1.CS.model_handshake.CS.hs_transcript
            (W.serialize_handshake (M.ClientHello ch))) /\
        Seq.equal
          m3.CS.model_handshake.CS.hs_transcript
          (B.append
            m2.CS.model_handshake.CS.hs_transcript
            (W.serialize_handshake (M.ServerHello sh))))
      (ensures
        Seq.equal
          m3.CS.model_handshake.CS.hs_transcript
          (B.append
            (W.serialize_handshake (M.ClientHello ch))
            (W.serialize_handshake (M.ServerHello sh))))
= ()

#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_server_flight_walk
  (m0:CS.connection_model)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (cv:GCV.certificateVerify)
  (sf cf:GFin.finished)
  (appw appr:CS.traffic_key_material)
  (final:CS.connection_model)
  : Lemma
      (requires
        (let ev_ee = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
         let ev_cert = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
         let ev_sign_cv = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
         let ev_cv = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
         let ev_sf = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); } in
         let ev_iaw = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = appw; }; }) in
         let ev_rcf = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); } in
         let ev_iar = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = appr; }; }) in
         let ev_vcf = CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf) in
         let rest = [ev_ee; ev_cert; ev_sign_cv; ev_cv; ev_sf; ev_iaw; ev_rcf; ev_iar; ev_vcf] in
         exists rs rr. SMReplay.conn_events_sent_seal_replay m0 rest rs rr final))
      (ensures
        (let ev_ee = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
         let ev_cert = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
         let ev_sign_cv = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
         let ev_cv = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
         let ev_sf = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); } in
         let s0 = step_next m0 ev_ee in
         let s1 = step_next s0 ev_cert in
         let sauth = step_next s1 ev_sign_cv in
         let s2 = step_next sauth ev_cv in
         let s3 = step_next s2 ev_sf in
         CS.step_model m0 ev_ee == Some s0 /\
         CS.step_model s0 ev_cert == Some s1 /\
         CS.step_model s1 ev_sign_cv == Some sauth /\
         CS.step_model sauth ev_cv == Some s2 /\
         CS.step_model s2 ev_sf == Some s3 /\
         s0.CS.model_record.CS.record_write == R.next_seq m0.CS.model_record.CS.record_write /\
         s1.CS.model_record.CS.record_write == R.next_seq s0.CS.model_record.CS.record_write /\
         s2.CS.model_record.CS.record_write == R.next_seq sauth.CS.model_record.CS.record_write /\
         s3.CS.model_record.CS.record_write == R.next_seq s2.CS.model_record.CS.record_write /\
         final.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
         final.CS.model_handshake.CS.hs_certificate == Some cert /\
         final.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
         final.CS.model_handshake.CS.hs_server_finished == Some sf /\
         final.CS.model_handshake.CS.hs_client_finished == Some cf))
=
  let ev_ee = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
  let ev_cert = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
  let ev_sign_cv = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
  let ev_cv = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
  let ev_sf = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); } in
  let ev_iaw = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = appw; }; }) in
  let ev_rcf = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); } in
  let ev_iar = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = appr; }; }) in
  let ev_vcf = CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf) in
  peel_sent m0 ev_ee [ev_cert; ev_sign_cv; ev_cv; ev_sf; ev_iaw; ev_rcf; ev_iar; ev_vcf] final;
  assert (m0.CS.model_control == CS.ControlHandshaking CS.HsServerHelloSent);
  let s0 = step_next m0 ev_ee in
  assert (s0.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (s0.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  peel_sent s0 ev_cert [ev_sign_cv; ev_cv; ev_sf; ev_iaw; ev_rcf; ev_iar; ev_vcf] final;
  let s1 = step_next s0 ev_cert in
  assert (s1.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (s1.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (s1.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  peel_sent s1 ev_sign_cv [ev_cv; ev_sf; ev_iaw; ev_rcf; ev_iar; ev_vcf] final;
  let sauth = step_next s1 ev_sign_cv in
  assert (sauth.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (sauth.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (sauth.CS.model_handshake.CS.hs_certificate == Some cert);
  peel_sent sauth ev_cv [ev_sf; ev_iaw; ev_rcf; ev_iar; ev_vcf] final;
  let s2 = step_next sauth ev_cv in
  assert (s2.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (s2.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (s2.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (s2.CS.model_handshake.CS.hs_certificate == Some cert);
  peel_sent s2 ev_sf [ev_iaw; ev_rcf; ev_iar; ev_vcf] final;
  let s3 = step_next s2 ev_sf in
  assert (s3.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent);
  assert (s3.CS.model_handshake.CS.hs_server_finished == Some sf);
  assert (s3.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (s3.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (s3.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (s3.CS.model_record.CS.record_write ==
    R.next_seq s2.CS.model_record.CS.record_write);
  peel_sent s3 ev_iaw [ev_rcf; ev_iar; ev_vcf] final;
  let s4 = step_next s3 ev_iaw in
  lemma_role_install_preserves_control
    s3
    s4
    CS.ServerEndpoint
    {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = appw;
    };
  lemma_install_preserves_msg_fields s3 ev_iaw s4;
  assert (s4.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent);
  assert (s4.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (s4.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (s4.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (s4.CS.model_handshake.CS.hs_server_finished == Some sf);
  peel_sent s4 ev_rcf [ev_iar; ev_vcf] final;
  let s5 = step_next s4 ev_rcf in
  lemma_received_client_finished_sets_stage s4 s5 cf;
  lemma_received_client_finished_updates_handshake s4 s5 cf;
  assert (s5.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (s5.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (s5.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (s5.CS.model_handshake.CS.hs_server_finished == Some sf);
  assert (s5.CS.model_handshake.CS.hs_client_finished == Some cf);
  peel_sent s5 ev_iar [ev_vcf] final;
  let s6 = step_next s5 ev_iar in
  lemma_role_install_preserves_control
    s5
    s6
    CS.ServerEndpoint
    {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = appr;
    };
    lemma_install_preserves_msg_fields s5 ev_iar s6;
    assert (s6.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
    assert (s6.CS.model_handshake.CS.hs_certificate == Some cert);
    assert (s6.CS.model_handshake.CS.hs_certificate_verify == Some cv);
    assert (s6.CS.model_handshake.CS.hs_server_finished == Some sf);
    assert (s6.CS.model_handshake.CS.hs_client_finished == Some cf);
    assert (s6.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived);
    eliminate exists rs rr.
      SMReplay.conn_events_sent_seal_replay s6 [ev_vcf] rs rr final
    with
    (
      peel_last_sent s6 ev_vcf final;
      lemma_verify_client_finished_preserves_handshake s6 final cf;
      lemma_verify_client_finished_sets_slot_low_rlimit s6 final cf;
      assert (final.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
      assert (final.CS.model_handshake.CS.hs_certificate == Some cert);
      assert (final.CS.model_handshake.CS.hs_certificate_verify == Some cv);
      assert (final.CS.model_handshake.CS.hs_server_finished == Some sf);
      assert (final.CS.model_handshake.CS.hs_client_finished == Some cf)
    )
#pop-options

// Keep the two expensive local verification transitions and the final
// ClientFinished send in separate, exact transition queries.
noextract
let lemma_verify_certificate_signature_transition
  (model model':CS.connection_model)
  (cv:GCV.certificateVerify)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsCertificateVerifyReceived /\
        CS.step_model model
          (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)) ==
          Some model')
      (ensures
        model' ==
          CS.with_handshake_stage
            model
            { model.CS.model_handshake with
                CS.hs_certificate_verify = Some cv;
                CS.hs_certificate_verify_verified = true;
            }
            CS.HsCertificateVerifyVerified)
= ()

noextract
let lemma_validate_certificate_transition
  (model model':CS.connection_model)
  (peer:X.peer_identity)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsCertificateReceived /\
        CS.step_model model
          (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)) ==
          Some model')
      (ensures
        model' ==
          CS.with_handshake_stage
            model
            { model.CS.model_handshake with
                CS.hs_validated_peer = Some peer
            }
            CS.HsCertificateValidated)
= ()

noextract
let lemma_verify_server_finished_transition
  (model model':CS.connection_model)
  (fin:GFin.finished)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsServerFinishedReceived /\
        CS.step_model model
          (CS.ConnLocalEvent (CS.LocalVerifyFinished fin)) ==
          Some model')
      (ensures
        model' ==
          CS.with_handshake_stage
            model
            (CS.append_handshake_to_transcript
              { model.CS.model_handshake with
                  CS.hs_server_finished = Some fin;
                  CS.hs_server_finished_verified = true;
              }
              (M.Finished fin))
            CS.HsServerFinishedVerified)
= ()

noextract
let lemma_sent_client_finished_transition
  (model model':CS.connection_model)
  (fin:GFin.finished)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsServerFinishedVerified /\
        CS.step_model model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished fin);
          }) ==
          Some model')
      (ensures
        model' ==
          { model with
              CS.model_control = CS.ControlApplicationData;
              CS.model_record =
                CS.install_client_application_write_after_finished
                  model.CS.model_record
                  model.CS.model_handshake.CS.hs_keys;
              CS.model_handshake =
                CS.append_handshake_to_transcript
                  { model.CS.model_handshake with
                      CS.hs_client_finished = Some fin
                  }
                  (M.Finished fin);
          } /\
        model'.CS.model_control == CS.ControlApplicationData /\
        model'.CS.model_handshake.CS.hs_client_finished == Some fin)
= ()

noextract
let lemma_sent_client_finished_sets_control
  (model model':CS.connection_model)
  (fin:GFin.finished)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsServerFinishedVerified /\
        CS.step_model model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished fin);
          }) ==
          Some model')
      (ensures model'.CS.model_control == CS.ControlApplicationData)
= ()

noextract
let lemma_sent_client_finished_sets_slot
  (model model':CS.connection_model)
  (fin:GFin.finished)
  : Lemma
      (requires
        model.CS.model_control ==
          CS.ControlHandshaking CS.HsServerFinishedVerified /\
        CS.step_model model
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished fin);
          }) ==
          Some model')
      (ensures
        model'.CS.model_handshake.CS.hs_client_finished == Some fin)
= ()

// ================= CLIENT FLIGHT WALK =================
#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_client_flight_walk
  (m0:CS.connection_model)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
  (cv:GCV.certificateVerify) (sf cf:GFin.finished)
  (e13 e14:CS.conn_event)
  (final:CS.connection_model)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        (let ev_ee = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
         let ev_cert = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
         let ev_val = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
         let ev_cv = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
         let ev_vc = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
         let ev_sf = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); } in
         let ev_vf = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
         let ev_cf = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf); } in
         let rest = [ev_ee; ev_cert; ev_val; ev_cv; ev_vc; ev_sf; ev_vf; e13; e14; ev_cf] in
         exists rs rr. SMReplay.conn_events_received_decode_replay m0 rest rs rr final))
      (ensures
        final.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
        final.CS.model_handshake.CS.hs_certificate == Some cert /\
        final.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
        final.CS.model_handshake.CS.hs_server_finished == Some sf /\
        final.CS.model_handshake.CS.hs_client_finished == Some cf)
=
  let ev_ee = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
  let ev_cert = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
  let ev_val = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
  let ev_cv = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
  let ev_vc = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
  let ev_sf = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); } in
  let ev_vf = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
  let ev_cf = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf); } in
  peel_received m0 ev_ee [ev_cert; ev_val; ev_cv; ev_vc; ev_sf; ev_vf; e13; e14; ev_cf] final;
  assert (m0.CS.model_control == CS.ControlHandshaking CS.HsServerHelloReceived);
  let c0 = step_next m0 ev_ee in
  assert (c0.CS.model_control == CS.ControlHandshaking CS.HsEncryptedExtensionsReceived);
  assert (c0.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  peel_received c0 ev_cert [ev_val; ev_cv; ev_vc; ev_sf; ev_vf; e13; e14; ev_cf] final;
  let c1 = step_next c0 ev_cert in
  assert (c1.CS.model_control == CS.ControlHandshaking CS.HsCertificateReceived);
  assert (c1.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (c1.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  peel_received c1 ev_val [ev_cv; ev_vc; ev_sf; ev_vf; e13; e14; ev_cf] final;
  let cauth = step_next c1 ev_val in
  lemma_validate_certificate_transition c1 cauth peer;
  assert (cauth.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated);
  assert (cauth.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (cauth.CS.model_handshake.CS.hs_certificate == Some cert);
  peel_received cauth ev_cv [ev_vc; ev_sf; ev_vf; e13; e14; ev_cf] final;
  let c2 = step_next cauth ev_cv in
  assert (c2.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived);
  assert (c2.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (c2.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (c2.CS.model_handshake.CS.hs_certificate == Some cert);
  peel_received c2 ev_vc [ev_sf; ev_vf; e13; e14; ev_cf] final;
  let cvfy = step_next c2 ev_vc in
  lemma_verify_certificate_signature_transition c2 cvfy cv;
  assert (cvfy.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified);
  assert (cvfy.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (cvfy.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (cvfy.CS.model_handshake.CS.hs_certificate == Some cert);
  peel_received cvfy ev_sf [ev_vf; e13; e14; ev_cf] final;
  let c3 = step_next cvfy ev_sf in
  assert (c3.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedReceived);
  assert (c3.CS.model_handshake.CS.hs_server_finished == Some sf);
  assert (c3.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (c3.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (c3.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  peel_received c3 ev_vf [e13; e14; ev_cf] final;
  let c4 = step_next c3 ev_vf in
  lemma_verify_server_finished_transition c3 c4 sf;
  assert (c4.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified);
  assert (c4.CS.model_handshake.CS.hs_server_finished == Some sf);
  assert (c4.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (c4.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (c4.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  peel_received c4 e13 [e14; ev_cf] final;
  let c5 = step_next c4 e13 in
  lemma_cover_both_install e13 e14;
  lemma_install_preserves_msg_fields c4 e13 c5;
  assert (c5.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified);
  peel_received c5 e14 [ev_cf] final;
  let c6 = step_next c5 e14 in
  lemma_install_preserves_msg_fields c5 e14 c6;
  assert (c6.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedVerified);
  assert (c6.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (c6.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (c6.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (c6.CS.model_handshake.CS.hs_server_finished == Some sf);
  let c7 = step_next c6 ev_cf in
  peel_last_received c6 ev_cf final;
  peel_received c6 ev_cf [] final;
  lemma_sent_client_finished_transition c6 c7 cf;
  assert (c7.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (c7.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (c7.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (c7.CS.model_handshake.CS.hs_server_finished == Some sf);
  assert (c7.CS.model_handshake.CS.hs_client_finished == Some cf);
  lemma_equal_models_client_finished_slot c7 final cf;
  assert (c7.CS.model_control == CS.ControlApplicationData);
  lemma_equal_models_application_control c7 final;
  assert (final.CS.model_handshake.CS.hs_encrypted_extensions == Some ee);
  assert (final.CS.model_handshake.CS.hs_certificate == Some cert);
  assert (final.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  assert (final.CS.model_handshake.CS.hs_server_finished == Some sf)
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_client_flight_step_and_record_facts
  (m0:CS.connection_model)
  (ee:GEE.encryptedExtensions)
  (cert:GCert.certificate)
  (peer:X.peer_identity)
  (cv:GCV.certificateVerify)
  (sf cf:GFin.finished)
  (e13 e14:CS.conn_event)
  (final:CS.connection_model)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        (let ev_ee = CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
         } in
         let ev_cert = CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.Certificate cert);
         } in
         let ev_val = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
         let ev_cv = CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
         } in
         let ev_vc =
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
         let ev_sf = CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.Finished sf);
         } in
         let ev_vf = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
         let ev_cf = CS.ConnNetworkEvent {
           CL.message_direction = CL.Sent;
           CL.message_value = M.TlsHandshake (M.Finished cf);
         } in
         exists rs rr.
           SMReplay.conn_events_received_decode_replay
             m0
             [ev_ee; ev_cert; ev_val; ev_cv; ev_vc; ev_sf;
              ev_vf; e13; e14; ev_cf]
             rs rr final))
      (ensures
        (let ev_ee = CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
         } in
         let ev_cert = CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.Certificate cert);
         } in
         let ev_val = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
         let ev_cv = CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
         } in
         let ev_vc =
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
         let ev_sf = CS.ConnNetworkEvent {
           CL.message_direction = CL.Received;
           CL.message_value = M.TlsHandshake (M.Finished sf);
         } in
         let c0 = step_next m0 ev_ee in
         let c1 = step_next c0 ev_cert in
         let cauth = step_next c1 ev_val in
         let c2 = step_next cauth ev_cv in
         let cvfy = step_next c2 ev_vc in
         let c3 = step_next cvfy ev_sf in
         CS.step_model m0 ev_ee == Some c0 /\
         CS.step_model c0 ev_cert == Some c1 /\
         CS.step_model c1 ev_val == Some cauth /\
         CS.step_model cauth ev_cv == Some c2 /\
         CS.step_model c2 ev_vc == Some cvfy /\
         CS.step_model cvfy ev_sf == Some c3 /\
         c0.CS.model_record.CS.record_read ==
           R.next_seq m0.CS.model_record.CS.record_read /\
         c1.CS.model_record.CS.record_read ==
           R.next_seq c0.CS.model_record.CS.record_read /\
         c2.CS.model_record.CS.record_read ==
           R.next_seq cauth.CS.model_record.CS.record_read /\
         c3.CS.model_record.CS.record_read ==
           R.next_seq cvfy.CS.model_record.CS.record_read))
=
  let ev_ee = CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
  } in
  let ev_cert = CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Certificate cert);
  } in
  let ev_val = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
  let ev_cv = CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
  } in
  let ev_vc = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
  let ev_sf = CS.ConnNetworkEvent {
    CL.message_direction = CL.Received;
    CL.message_value = M.TlsHandshake (M.Finished sf);
  } in
  let ev_vf = CS.ConnLocalEvent (CS.LocalVerifyFinished sf) in
  let ev_cf = CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished cf);
  } in
  peel_received m0 ev_ee
    [ev_cert; ev_val; ev_cv; ev_vc; ev_sf; ev_vf; e13; e14; ev_cf]
    final;
  let c0 = step_next m0 ev_ee in
  assert (c0.CS.model_record.CS.record_read ==
    R.next_seq m0.CS.model_record.CS.record_read);
  peel_received c0 ev_cert
    [ev_val; ev_cv; ev_vc; ev_sf; ev_vf; e13; e14; ev_cf]
    final;
  let c1 = step_next c0 ev_cert in
  assert (c1.CS.model_record.CS.record_read ==
    R.next_seq c0.CS.model_record.CS.record_read);
  peel_received c1 ev_val
    [ev_cv; ev_vc; ev_sf; ev_vf; e13; e14; ev_cf]
    final;
  let cauth = step_next c1 ev_val in
  peel_received cauth ev_cv
    [ev_vc; ev_sf; ev_vf; e13; e14; ev_cf]
    final;
  let c2 = step_next cauth ev_cv in
  assert (c2.CS.model_record.CS.record_read ==
    R.next_seq cauth.CS.model_record.CS.record_read);
  peel_received c2 ev_vc [ev_sf; ev_vf; e13; e14; ev_cf] final;
  let cvfy = step_next c2 ev_vc in
  peel_received cvfy ev_sf [ev_vf; e13; e14; ev_cf] final;
  let c3 = step_next cvfy ev_sf in
  assert (c3.CS.model_record.CS.record_read ==
    R.next_seq cvfy.CS.model_record.CS.record_read)
#pop-options

#push-options "--z3rlimit 10 --split_queries always --fuel 3 --ifuel 3"
noextract
let lemma_sent_finished_at_appdata_sets_client_finished (m m':CS.connection_model) (fin:GFin.finished)
  : Lemma
      (requires
        CS.step_model m (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished fin); }) == Some m' /\
        m'.CS.model_control == CS.ControlApplicationData)
      (ensures m'.CS.model_handshake.CS.hs_client_finished == Some fin)
= ()

noextract
let lemma_verify_client_finished_sets_client_finished (m m':CS.connection_model) (fin:GFin.finished)
  : Lemma
      (requires
        CS.step_model m (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)) == Some m')
      (ensures m'.CS.model_handshake.CS.hs_client_finished == Some fin)
= ()
#pop-options


// ================= CFRR SUFFIX WALK (server receiving client finished) =================
#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_cfrr_suffix_walk
  (m0:CS.connection_model) (appw appr:CS.traffic_key_material) (cf:GFin.finished) (final:CS.connection_model)
  : Lemma
      (requires
        (let ev_iaw = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = appw; }; }) in
         let ev_rcf = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); } in
         let ev_iar = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = appr; }; }) in
         let ev_vcf = CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf) in
         exists rs rr. SMReplay.conn_events_received_decode_replay m0 [ev_iaw; ev_rcf; ev_iar; ev_vcf] rs rr final))
      (ensures
        (let ev_iaw = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = appw; }; }) in
         let ev_rcf = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); } in
         let s1 = step_next m0 ev_iaw in
         CS.step_model m0 ev_iaw == Some s1 /\
         CS.step_model s1 ev_rcf == Some (step_next s1 ev_rcf) /\
         final.CS.model_handshake.CS.hs_client_finished == Some cf))
=
  let ev_iaw = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = appw; }; }) in
  let ev_rcf = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); } in
  let ev_iar = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = appr; }; }) in
  let ev_vcf = CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf) in
  peel_received m0 ev_iaw [ev_rcf; ev_iar; ev_vcf] final;
  let s1 = step_next m0 ev_iaw in
  peel_received s1 ev_rcf [ev_iar; ev_vcf] final;
  let s2 = step_next s1 ev_rcf in
  peel_received s2 ev_iar [ev_vcf] final;
  let s3 = step_next s2 ev_iar in
  peel_received s3 ev_vcf [] final;
  let s4 = step_next s3 ev_vcf in
  peel_nil_received s4 final;
  lemma_verify_client_finished_sets_client_finished s3 s4 cf
#pop-options


// ---- Hard-conjunct helper lemmas (to be discharged) ----
#push-options "--z3rlimit 10 --split_queries always --fuel 1 --ifuel 1"
noextract
let lemma_message_match
  (client server:CS.connection_state)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_s:GCV.certificateVerify) (sf_s:GFin.finished) (cf_r:GFin.finished)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (cf_f:GFin.finished)
  : Lemma
      (requires
        server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_s /\
        server.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert_s /\
        server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv_s /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf_s /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf_r /\
        client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_c /\
        client.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert_c /\
        client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv_c /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf_c /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf_f)
      (ensures
        (match
           client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
           server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions,
           client.CS.cs_model.CS.model_handshake.CS.hs_certificate,
           server.CS.cs_model.CS.model_handshake.CS.hs_certificate,
           client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
           server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify,
           client.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
           server.CS.cs_model.CS.model_handshake.CS.hs_server_finished,
           client.CS.cs_model.CS.model_handshake.CS.hs_client_finished,
           server.CS.cs_model.CS.model_handshake.CS.hs_client_finished
         with
         | Some client_ee, Some server_ee_msg,
           Some client_cert, Some server_cert_msg,
           Some client_cv, Some server_cv_msg,
           Some client_sf, Some server_sf,
           Some client_cf, Some server_cf ->
           M.EncryptedExtensions ee_s == M.EncryptedExtensions server_ee_msg /\
           M.EncryptedExtensions ee_c == M.EncryptedExtensions client_ee /\
           M.Certificate cert_s == M.Certificate server_cert_msg /\
           M.Certificate cert_c == M.Certificate client_cert /\
           M.CertificateVerify cv_s == M.CertificateVerify server_cv_msg /\
           M.CertificateVerify cv_c == M.CertificateVerify client_cv /\
           M.Finished sf_s == M.Finished server_sf /\
           M.Finished sf_c == M.Finished client_sf /\
           M.Finished cf_f == M.Finished client_cf /\
           M.Finished cf_r == M.Finished server_cf
         | _, _, _, _, _, _, _, _, _, _ -> False))
= ()
#pop-options

// ===================================================================
// Shared-secret preservation: ks_shared_secret is set exactly once
// (only LocalDeriveSharedSecret sets it, and it requires None), so any
// legal step from a state where it is already set preserves it.
// ===================================================================
#push-options "--z3rlimit 10 --fuel 1 --ifuel 1"
noextract
let lemma_step_preserves_shared_secret_when_set
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m ev /\
        CS.step_model m ev == Some m' /\
        Some? m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (ensures
        m'.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
        m.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
= match ev with
  | CS.ConnNetworkEvent _ -> ()
  | CS.ConnLocalEvent le ->
    (match le with
     | CS.LocalDeriveSharedSecret _ -> ()
     | _ -> ())
#pop-options

#push-options "--z3rlimit 10 --split_queries always"
noextract
let rec lemma_sent_replay_preserves_shared_secret
  (m0:CS.connection_model) (evs:list CS.conn_event) (final:CS.connection_model)
  : Lemma
      (requires
        (exists rs rr. SMReplay.conn_events_sent_seal_replay m0 evs rs rr final) /\
        Some? m0.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (ensures
        final.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
        m0.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (decreases evs)
=
  match evs with
  | [] -> peel_nil_sent m0 final
  | ev :: rest ->
    peel_sent m0 ev rest final;
    let m1 = step_next m0 ev in
    lemma_step_preserves_shared_secret_when_set m0 ev m1;
    lemma_sent_replay_preserves_shared_secret m1 rest final

noextract
let rec lemma_received_replay_preserves_shared_secret
  (m0:CS.connection_model) (evs:list CS.conn_event) (final:CS.connection_model)
  : Lemma
      (requires
        (exists rs rr. SMReplay.conn_events_received_decode_replay m0 evs rs rr final) /\
        Some? m0.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (ensures
        final.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
        m0.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (decreases evs)
=
  match evs with
  | [] -> peel_nil_received m0 final
  | ev :: rest ->
    peel_received m0 ev rest final;
    let m1 = step_next m0 ev in
    lemma_step_preserves_shared_secret_when_set m0 ev m1;
    lemma_received_replay_preserves_shared_secret m1 rest final
#pop-options

// ---- generic preservation of hellos over non-hello events ----
noextract
let event_not_hello (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnNetworkEvent { CL.message_value = M.TlsHandshake (M.ClientHello _) } -> false
  | CS.ConnNetworkEvent { CL.message_value = M.TlsHandshake (M.ServerHello _) } -> false
  | CS.ConnLocalEvent (CS.LocalSelectServerParameters _) -> false
  | _ -> true

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
noextract
let lemma_step_preserves_hellos_when_not_hello
  (m:CS.connection_model) (ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.step_model m ev == Some m' /\
        event_not_hello ev)
      (ensures
        m'.CS.model_handshake.CS.hs_client_hello ==
          m.CS.model_handshake.CS.hs_client_hello /\
        m'.CS.model_handshake.CS.hs_server_hello ==
          m.CS.model_handshake.CS.hs_server_hello)
= match ev with
  | CS.ConnNetworkEvent nm ->
    (match nm.CL.message_value with
     | _ -> ())
  | CS.ConnLocalEvent le ->
    (match le with
     | CS.LocalStartHandshake _ -> ()
     | CS.LocalStartServer -> ()
     | CS.LocalSelectServerParameters _ -> ()
     | CS.LocalDeriveSharedSecret _ -> ()
     | CS.LocalInstallTrafficKeys _ -> ()
     | CS.LocalInstallTrafficKeysForRole _ -> ()
     | CS.LocalValidateCertificate _ -> ()
     | CS.LocalVerifyCertificateSignature _ -> ()
     | CS.LocalSignCertificateVerify _ -> ()
     | CS.LocalVerifyFinished _ -> ()
     | CS.LocalVerifyClientFinished _ -> ()
     | CS.LocalDeliverApplicationData _ -> ()
     | CS.LocalFail _ -> ())
#pop-options

noextract
let rec all_not_hello (evs:list CS.conn_event) : bool =
  match evs with
  | [] -> true
  | ev :: rest -> event_not_hello ev && all_not_hello rest

#push-options "--z3rlimit 10 --split_queries always"
noextract
let rec lemma_sent_replay_preserves_slots
  (m0:CS.connection_model) (evs:list CS.conn_event) (final:CS.connection_model)
  : Lemma
      (requires
        (exists rs rr. SMReplay.conn_events_sent_seal_replay m0 evs rs rr final) /\
        all_not_hello evs /\
        Some? m0.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (ensures
        final.CS.model_handshake.CS.hs_client_hello ==
          m0.CS.model_handshake.CS.hs_client_hello /\
        final.CS.model_handshake.CS.hs_server_hello ==
          m0.CS.model_handshake.CS.hs_server_hello /\
        final.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
          m0.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (decreases evs)
=
  match evs with
  | [] -> peel_nil_sent m0 final
  | ev :: rest ->
    peel_sent m0 ev rest final;
    let m1 = step_next m0 ev in
    lemma_step_preserves_hellos_when_not_hello m0 ev m1;
    lemma_step_preserves_shared_secret_when_set m0 ev m1;
    lemma_sent_replay_preserves_slots m1 rest final

noextract
let rec lemma_received_replay_preserves_slots
  (m0:CS.connection_model) (evs:list CS.conn_event) (final:CS.connection_model)
  : Lemma
      (requires
        (exists rs rr. SMReplay.conn_events_received_decode_replay m0 evs rs rr final) /\
        all_not_hello evs /\
        Some? m0.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (ensures
        final.CS.model_handshake.CS.hs_client_hello ==
          m0.CS.model_handshake.CS.hs_client_hello /\
        final.CS.model_handshake.CS.hs_server_hello ==
          m0.CS.model_handshake.CS.hs_server_hello /\
        final.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret ==
          m0.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret)
      (decreases evs)
=
  match evs with
  | [] -> peel_nil_received m0 final
  | ev :: rest ->
    peel_received m0 ev rest final;
    let m1 = step_next m0 ev in
    lemma_step_preserves_hellos_when_not_hello m0 ev m1;
    lemma_step_preserves_shared_secret_when_set m0 ev m1;
    lemma_received_replay_preserves_slots m1 rest final
#pop-options

// ---- server cleartext-prefix walk: establish model5 slots ----
#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_server_prefix_slots
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (model5:CS.connection_model)
  : Lemma
      (requires
        m0.CS.model_handshake.CS.hs_client_hello == None /\
        m0.CS.model_handshake.CS.hs_server_hello == None /\
        (exists rs rr.
          SMReplay.conn_events_sent_seal_replay m0
            (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
            rs rr model5))
      (ensures
        model5.CS.model_handshake.CS.hs_client_hello == Some ch /\
        model5.CS.model_handshake.CS.hs_server_hello == Some sh /\
        model5.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared)
=
  let e0 = CS.ConnLocalEvent CS.LocalStartServer in
  let e1 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ClientHello ch); } in
  let e2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let e4 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ServerHello sh); } in
  peel_sent m0 e0 [e1;e2;e3;e4] model5;
  let m1 = step_next m0 e0 in
  peel_sent m1 e1 [e2;e3;e4] model5;
  let m2 = step_next m1 e1 in
  assert (m2.CS.model_handshake.CS.hs_client_hello == Some ch);
  peel_sent m2 e2 [e3;e4] model5;
  let m3 = step_next m2 e2 in
  peel_sent m3 e3 [e4] model5;
  let m4 = step_next m3 e3 in
  assert (m4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared);
  peel_sent m4 e4 [] model5;
  let m5 = step_next m4 e4 in
  peel_nil_sent m5 model5;
  assert (m5.CS.model_handshake.CS.hs_server_hello == Some sh)
#pop-options

// ---- client cleartext-prefix walk: establish model4 slots ----
#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_client_prefix_slots
  (m0:CS.connection_model)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (model4:CS.connection_model)
  : Lemma
      (requires
        m0.CS.model_handshake.CS.hs_client_hello == None /\
        m0.CS.model_handshake.CS.hs_server_hello == None /\
        (exists rs rr.
          SMReplay.conn_events_received_decode_replay m0
            (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
            rs rr model4))
      (ensures
        model4.CS.model_handshake.CS.hs_client_hello == Some ch /\
        model4.CS.model_handshake.CS.hs_server_hello == Some sh /\
        model4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared)
=
  let e0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let e1 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); } in
  let e2 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); } in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
  peel_received m0 e0 [e1;e2;e3] model4;
  let m1 = step_next m0 e0 in
  peel_received m1 e1 [e2;e3] model4;
  let m2 = step_next m1 e1 in
  assert (m2.CS.model_handshake.CS.hs_client_hello == Some ch);
  peel_received m2 e2 [e3] model4;
  let m3 = step_next m2 e2 in
  assert (m3.CS.model_handshake.CS.hs_server_hello == Some sh);
  peel_received m3 e3 [] model4;
  let m4 = step_next m3 e3 in
  peel_nil_received m4 model4;
  assert (m4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared)
#pop-options

// ---- combined reconciliation: final-model handshake slots equal the cleartext-prefix hellos ----
#push-options "--z3rlimit 10 --split_queries always"
noextract
let lemma_server_final_slots
  (server:CS.connection_state)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (model5:CS.connection_model) (suffix:list CS.conn_event)
  : Lemma
      (requires
        (exists rs rr. SMReplay.conn_events_sent_seal_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
           rs rr model5) /\
        (exists rs rr. SMReplay.conn_events_sent_seal_replay model5 suffix rs rr server.CS.cs_model) /\
        all_not_hello suffix)
      (ensures
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared)
=
  let m0 = CS.initial_model server.CS.cs_model.CS.model_config in
  assert (m0.CS.model_handshake.CS.hs_client_hello == None);
  assert (m0.CS.model_handshake.CS.hs_server_hello == None);
  lemma_server_prefix_slots m0 ch selection server_shared sh model5;
  lemma_sent_replay_preserves_slots model5 suffix server.CS.cs_model

noextract
let lemma_client_final_slots
  (client:CS.connection_state)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (model4:CS.connection_model) (suffix:list CS.conn_event)
  : Lemma
      (requires
        (exists rs rr. SMReplay.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
           rs rr model4) /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay model4 suffix rs rr client.CS.cs_model) /\
        all_not_hello suffix)
      (ensures
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
        client.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some client_shared)
=
  let m0 = CS.initial_model client.CS.cs_model.CS.model_config in
  assert (m0.CS.model_handshake.CS.hs_client_hello == None);
  assert (m0.CS.model_handshake.CS.hs_server_hello == None);
  lemma_client_prefix_slots m0 start ch sh client_shared model4;
  lemma_received_replay_preserves_slots model4 suffix client.CS.cs_model
#pop-options

// ===== transplanted hole-closing helpers =====
// H1: shared secret equality from FACT3 + final slots
#push-options "--z3rlimit 10 --split_queries always"
noextract
let lemma_shared_secret_eq
  (client server:CS.connection_state)
  (ch_s:GCH.clientHello) (selection_s:CS.server_handshake_selection)
  (server_shared_s:C.x25519_shared_secret) (sh_s:GSH.serverHello)
  (model5_s:CS.connection_model) (server_suffix:list CS.conn_event)
  (start_c:CS.handshake_start) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (client_shared_c:C.x25519_shared_secret)
  (model4_c:CS.connection_model) (client_suffix:list CS.conn_event)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        (exists rs rr. SMReplay.conn_events_sent_seal_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch_s selection_s server_shared_s sh_s)
           rs rr model5_s) /\
        (exists rs rr. SMReplay.conn_events_sent_seal_replay model5_s server_suffix rs rr server.CS.cs_model) /\
        all_not_hello server_suffix /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
           rs rr model4_c) /\
        (exists rs rr. SMReplay.conn_events_received_decode_replay model4_c client_suffix rs rr client.CS.cs_model) /\
        all_not_hello client_suffix)
      (ensures Seq.equal server_shared_s client_shared_c)
=
  lemma_server_final_slots server ch_s selection_s server_shared_s sh_s model5_s server_suffix;
  lemma_client_final_slots client start_c ch_c sh_c client_shared_c model4_c client_suffix;
  Pairing.lemma_client_server_driver_paired_x25519_key_shares_from_key_share_projection_inputs
    client server;
  CSL.lemma_paired_x25519_key_shares_shared_secret_agree client server;
  assert (Seq.equal client_shared_c server_shared_s)
#pop-options

// H: same_transcript_checkpoint TH_SH from the cleartext final-hello milestone
#push-options "--z3rlimit 10 --split_queries always"
noextract
let lemma_checkpoint_th_sh_from_milestone
  (client server:CS.connection_state)
  : Lemma
      (requires clean16_cleartext_final_hello_slot_milestone client server)
      (ensures
        SMCorr.same_transcript_checkpoint SMIds.TH_CH client server /\
        SMCorr.same_transcript_checkpoint SMIds.TH_SH client server)
=
  eliminate exists client_start client_ch client_sh client_shared client_rest
                   server_ch selection server_shared server_sh server_rest.
    PNTRB.role_local_cleartext_prefix_shape client server
      client_start client_ch client_sh client_shared client_rest
      server_ch selection server_shared server_sh server_rest /\
    WFL.supported_client_hello_wire_profile client_ch /\
    B.length (W.serialize_handshake (M.ServerHello server_sh)) <= 16640 /\
    PNTRB.normalized_cleartext_raw_wire_bridge client_ch server_ch client_sh server_sh /\
    client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
    client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
    server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
    server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh
  with (
    eliminate exists (client_ch_raw server_ch_raw client_sh_raw server_sh_raw:B.bytes).
      Seq.equal client_ch_raw server_ch_raw /\
      Seq.equal server_sh_raw client_sh_raw /\
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) client_ch_raw /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) server_ch_raw /\
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) server_sh_raw /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) client_sh_raw
    with (
      WFL.lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
        client server client_ch server_ch client_sh server_sh
        client_ch_raw server_ch_raw client_sh_raw server_sh_raw
    )
  )
#pop-options

// H: server prefix -> handshake_secret and transcript of model5
#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_server_prefix_secret_transcript
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (model5:CS.connection_model)
  : Lemma
      (requires
        m0.CS.model_handshake.CS.hs_transcript == B.empty /\
        m0.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None /\
        (exists rs rr.
          SMReplay.conn_events_sent_seal_replay m0
            (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
            rs rr model5))
      (ensures
        model5.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          Some (K.handshake_secret (K.early_secret B.empty) server_shared) /\
        Seq.equal
          model5.CS.model_handshake.CS.hs_transcript
          (B.append (W.serialize_handshake (M.ClientHello ch))
                    (W.serialize_handshake (M.ServerHello sh))))
=
  let e0 = CS.ConnLocalEvent CS.LocalStartServer in
  let e1 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ClientHello ch); } in
  let e2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
  let e4 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ServerHello sh); } in
  peel_sent m0 e0 [e1;e2;e3;e4] model5;
  let m1 = step_next m0 e0 in
  peel_sent m1 e1 [e2;e3;e4] model5;
  let m2 = step_next m1 e1 in
  peel_sent m2 e2 [e3;e4] model5;
  let m3 = step_next m2 e2 in
  peel_sent m3 e3 [e4] model5;
  let m4 = step_next m3 e3 in
  assert (m4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          Some (K.handshake_secret (K.early_secret B.empty) server_shared));
  peel_sent m4 e4 [] model5;
  let m5 = step_next m4 e4 in
  peel_nil_sent m5 model5;
  assert (Seq.equal m1.CS.model_handshake.CS.hs_transcript B.empty);
  assert (Seq.equal m2.CS.model_handshake.CS.hs_transcript (W.serialize_handshake (M.ClientHello ch)))
#pop-options

// H: client prefix -> handshake_secret and transcript of model4
#push-options "--z3rlimit 10 --split_queries always --fuel 2 --ifuel 2"
noextract
let lemma_client_prefix_secret_transcript
  (m0:CS.connection_model)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (model4:CS.connection_model)
  : Lemma
      (requires
        m0.CS.model_handshake.CS.hs_transcript == B.empty /\
        m0.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None /\
        (exists rs rr.
          SMReplay.conn_events_received_decode_replay m0
            (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
            rs rr model4))
      (ensures
        model4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          Some (K.handshake_secret (K.early_secret B.empty) client_shared) /\
        Seq.equal
          model4.CS.model_handshake.CS.hs_transcript
          (B.append (W.serialize_handshake (M.ClientHello ch))
                    (W.serialize_handshake (M.ServerHello sh))))
=
  let e0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let e1 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); } in
  let e2 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); } in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
  peel_received m0 e0 [e1;e2;e3] model4;
  let m1 = step_next m0 e0 in
  lemma_step_model_transcript_delta_low_rlimit m0 e0 m1;
  peel_received m1 e1 [e2;e3] model4;
  let m2 = step_next m1 e1 in
  lemma_step_model_transcript_delta_low_rlimit m1 e1 m2;
  peel_received m2 e2 [e3] model4;
  let m3 = step_next m2 e2 in
  lemma_step_model_transcript_delta_low_rlimit m2 e2 m3;
  lemma_client_prefix_transcript_chain m0 m1 m2 m3 ch sh;
  peel_received m3 e3 [] model4;
  let m4 = step_next m3 e3 in
  peel_nil_received m4 model4
#pop-options

// H: transcript equality of model5_s / model4_c from checkpoint + prefix transcripts + slots
#push-options "--z3rlimit 10 --split_queries always"
noextract
let lemma_transcript_eq_from_checkpoint
  (client server:CS.connection_state)
  (model5_s model4_c:CS.connection_model)
  (ch_s:GCH.clientHello) (sh_s:GSH.serverHello)
  (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  : Lemma
      (requires
        SMCorr.same_transcript_checkpoint SMIds.TH_SH client server /\
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch_s /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh_s /\
        client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch_c /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh_c /\
        Seq.equal model5_s.CS.model_handshake.CS.hs_transcript
          (B.append (W.serialize_handshake (M.ClientHello ch_s))
                    (W.serialize_handshake (M.ServerHello sh_s))) /\
        Seq.equal model4_c.CS.model_handshake.CS.hs_transcript
          (B.append (W.serialize_handshake (M.ClientHello ch_c))
                    (W.serialize_handshake (M.ServerHello sh_c))))
      (ensures
        Seq.equal model5_s.CS.model_handshake.CS.hs_transcript
                  model4_c.CS.model_handshake.CS.hs_transcript)
=
  assert (SMCorr.transcript_checkpoint_bytes SMIds.TH_SH server.CS.cs_model.CS.model_handshake ==
          Some (B.append (W.serialize_handshake (M.ClientHello ch_s))
                         (W.serialize_handshake (M.ServerHello sh_s))));
  assert (SMCorr.transcript_checkpoint_bytes SMIds.TH_SH client.CS.cs_model.CS.model_handshake ==
          Some (B.append (W.serialize_handshake (M.ClientHello ch_c))
                         (W.serialize_handshake (M.ServerHello sh_c))))
#pop-options

// H: normalize a client handshake READ install (plain or ForRole) to a plain install
//    with traffic_install_matches
#push-options "--z3rlimit 10 --split_queries always --ifuel 2"
noextract
let lemma_client_read_install_normalize
  (m m':CS.connection_model) (ev:CS.conn_event)
  : Lemma
      (requires
        PCPS.client_no_tail_handshake_read_install_event ev /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures
        (exists (mat:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule m.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; } /\
          CS.step_model m
            (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
              { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; }))
            == Some m'))
=
  PCPS.lemma_client_no_tail_handshake_read_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    introduce exists (mat:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule m.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; } /\
      CS.step_model m
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; }))
        == Some m'
    with install.CS.install_material and ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    introduce exists (mat:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule m.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; } /\
      CS.step_model m
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; }))
        == Some m'
    with role_install.CS.install_payload.CS.install_material and ()
#pop-options

// I: a handshake WRITE install event (plain or ForRole) preserves ks_handshake_secret & hs_transcript
#push-options "--z3rlimit 10 --ifuel 2 --fuel 1"
noextract
let lemma_write_install_preserves_hs_secret_transcript
  (m m':CS.connection_model) (ev:CS.conn_event)
  : Lemma
      (requires
        PCPS.client_no_tail_handshake_write_install_event ev /\
        CS.step_model m ev == Some m')
      (ensures
        m'.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript /\
        m'.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
          == m.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
=
  PCPS.lemma_client_no_tail_handshake_write_install_event_cases ev

noextract
let lemma_read_install_preserves_hs_secret_transcript
  (m m':CS.connection_model) (ev:CS.conn_event)
  : Lemma
      (requires
        PCPS.client_no_tail_handshake_read_install_event ev /\
        CS.step_model m ev == Some m')
      (ensures
        m'.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript /\
        m'.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
          == m.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
=
  PCPS.lemma_client_no_tail_handshake_read_install_event_cases ev
#pop-options

// J: Seq.equal shared secrets -> Seq.equal handshake secrets
#push-options "--z3rlimit 10"
noextract
let lemma_hs_secret_seq_eq (a b:B.bytes)
  : Lemma
      (requires Seq.equal a b)
      (ensures
        Seq.equal
          (K.handshake_secret (K.early_secret B.empty) a)
          (K.handshake_secret (K.early_secret B.empty) b))
=
  Seq.lemma_eq_elim a b
#pop-options

// K: abstract handshake install events (cover) are not-hello
#push-options "--z3rlimit 10 --ifuel 2 --split_queries always"
noextract
let lemma_hs_install_events_not_hello (e4 e5:CS.conn_event)
  : Lemma
      (requires PCPS.client_no_tail_two_handshake_install_cover e4 e5)
      (ensures event_not_hello e4 /\ event_not_hello e5)
=
  PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4 e5;
  eliminate
    (PCPS.client_no_tail_handshake_write_install_event e4 /\
     PCPS.client_no_tail_handshake_read_install_event e5) \/
    (PCPS.client_no_tail_handshake_read_install_event e4 /\
     PCPS.client_no_tail_handshake_write_install_event e5)
  with
    (PCPS.lemma_client_no_tail_handshake_write_install_event_cases e4;
     PCPS.lemma_client_no_tail_handshake_read_install_event_cases e5)
  and
    (PCPS.lemma_client_no_tail_handshake_read_install_event_cases e4;
     PCPS.lemma_client_no_tail_handshake_write_install_event_cases e5)

noextract
let lemma_app_install_events_not_hello (e13 e14:CS.conn_event)
  : Lemma
      (requires PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures event_not_hello e13 /\ event_not_hello e14)
=
  PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
  eliminate
    (PNTCAS.client_no_tail_application_write_install_event e13 /\
     PNTCAS.client_no_tail_application_read_install_event e14) \/
    (PNTCAS.client_no_tail_application_read_install_event e13 /\
     PNTCAS.client_no_tail_application_write_install_event e14)
  with
    (PNTCAS.lemma_client_no_tail_application_write_install_event_cases e13;
     PNTCAS.lemma_client_no_tail_application_read_install_event_cases e14)
  and
    (PNTCAS.lemma_client_no_tail_application_read_install_event_cases e13;
     PNTCAS.lemma_client_no_tail_application_write_install_event_cases e14)
#pop-options

// K: full client-suffix all_not_hello (abstract installs handled via covers)
#push-options "--z3rlimit 10 --fuel 16 --ifuel 2 --split_queries always"
noextract
let lemma_client_suffix_all_not_hello
  (e4 e5 e13 e14:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
  (cv:GCV.certificateVerify) (sf:GFin.finished) (cf:GFin.finished)
  : Lemma
      (requires
        PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures
        all_not_hello
          (e4 :: e5 ::
            [
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate cert);
              };
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
              };
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished sf);
              };
              CS.ConnLocalEvent (CS.LocalVerifyFinished sf);
              e13;
              e14;
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished cf);
              }
            ]))
=
  lemma_hs_install_events_not_hello e4 e5;
  lemma_app_install_events_not_hello e13 e14
#pop-options
#pop-options
