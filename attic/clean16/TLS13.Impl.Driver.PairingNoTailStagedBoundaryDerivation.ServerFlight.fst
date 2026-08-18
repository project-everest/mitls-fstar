module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.ServerFlight

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
module Replay = TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Replay
open TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation.Replay

#push-options "--z3rlimit 10"

#push-options "--z3rlimit 10 --ifuel 2"
noextract
let lemma_hole1_alignment
  (model5_s server_after_write_s server_after_read_s:CS.connection_model)
  (server_material_s server_read_material_s:CS.traffic_key_material)
  (model4_c client_after_e4_c client_after_installs_c:CS.connection_model)
  (e4_c e5_c:CS.conn_event)
  : Lemma
      (requires
        (match
          model5_s.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          model4_c.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
         with
         | Some ss, Some cs -> Seq.equal ss cs
         | _, _ -> False) /\
        Seq.equal
          model5_s.CS.model_handshake.CS.hs_transcript
          model4_c.CS.model_handshake.CS.hs_transcript /\
        CS.legal_event model5_s
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = server_material_s; };
          })) /\
        CS.step_model model5_s
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = server_material_s; };
          })) == Some server_after_write_s /\
        CS.step_model server_after_write_s
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = server_read_material_s; };
          })) == Some server_after_read_s /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        CS.legal_event model4_c e4_c /\
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.legal_event client_after_e4_c e5_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c)
      (ensures PWL.write_read_record_material_aligned server_after_read_s client_after_installs_c)
=
  let server_read_install_le =
    CS.LocalInstallTrafficKeysForRole {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = server_read_material_s; };
    } in
  PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4_c e5_c;
  eliminate
    (PCPS.client_no_tail_handshake_write_install_event e4_c /\
     PCPS.client_no_tail_handshake_read_install_event e5_c) \/
    (PCPS.client_no_tail_handshake_read_install_event e4_c /\
     PCPS.client_no_tail_handshake_write_install_event e5_c)
  with
  (
    // write-first: e4_c = write, e5_c = read
    lemma_write_install_preserves_hs_secret_transcript model4_c client_after_e4_c e4_c;
    lemma_client_read_install_normalize client_after_e4_c client_after_installs_c e5_c;
    eliminate exists (mat_r:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule client_after_e4_c.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; } /\
      CS.step_model client_after_e4_c
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; }))
        == Some client_after_installs_c
    with
    (
      RA.lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
        model5_s client_after_e4_c server_material_s mat_r server_after_write_s client_after_installs_c;
      RA.lemma_step_sender_local_event_preserves_write_read_record_material_alignment
        server_after_write_s server_read_install_le server_after_read_s client_after_installs_c
    )
  )
  and
  (
    // read-first: e4_c = read, e5_c = write
    lemma_client_read_install_normalize model4_c client_after_e4_c e4_c;
    eliminate exists (mat_r:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule model4_c.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; } /\
      CS.step_model model4_c
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; }))
        == Some client_after_e4_c
    with
    (
      RA.lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
        model5_s model4_c server_material_s mat_r server_after_write_s client_after_e4_c;
      RA.lemma_step_sender_local_event_preserves_write_read_record_material_alignment
        server_after_write_s server_read_install_le server_after_read_s client_after_e4_c;
      PCPS.lemma_client_no_tail_handshake_write_install_event_cases e5_c;
      (match e5_c with
       | CS.ConnLocalEvent le ->
         RA.lemma_step_receiver_local_event_preserves_write_read_record_material_alignment
           server_after_read_s client_after_e4_c le client_after_installs_c)
    )
  )
#pop-options

// K: server-suffix all_not_hello (fully concrete, high fuel)
#push-options "--z3rlimit 10 --fuel 16 --ifuel 2"
noextract
let lemma_server_suffix_all_not_hello
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (cv:GCV.certificateVerify)
  (sf:GFin.finished) (cf:GFin.finished)
  (server_material server_read_material server_app_write_material server_app_read_material:CS.traffic_key_material)
  : Lemma
      (ensures
        all_not_hello
          (CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = server_material; };
            }) ::
           CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = server_read_material; };
            }) ::
          [
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material; };
              });
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); };
            CS.ConnLocalEvent
              (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material; };
              });
            CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
          ]))
=
  ()
#pop-options




// ===== HOLE 1 bundled: single-ensures alignment (keeps caller context clean) =====
#push-options "--z3rlimit 10 --fuel 16 --ifuel 2"
noextract
let lemma_pack_server_flight_align_real
  (client server:CS.connection_state)
  (ch_s:GCH.clientHello) (selection_s:CS.server_handshake_selection)
  (server_shared_s:C.x25519_shared_secret) (sh_s:GSH.serverHello)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_s:GCV.certificateVerify)
  (sf_s:GFin.finished) (cf_s:GFin.finished)
  (server_material_s server_read_material_s server_app_write_material_s server_app_read_material_s:CS.traffic_key_material)
  (model5_s server_after_write_s server_after_read_s:CS.connection_model)
  (start_c:CS.handshake_start) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (client_shared_c:C.x25519_shared_secret)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (cf_c:GFin.finished)
  (e4_c e5_c e13_c e14_c:CS.conn_event)
  (model4_c client_after_e4_c client_after_installs_c:CS.connection_model)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        clean16_cleartext_final_hello_slot_milestone client server /\
        // server prefix replay
        (exists rs rr. SMReplay.conn_events_sent_seal_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch_s selection_s server_shared_s sh_s)
           rs rr model5_s) /\
        // server suffix replay + steps + legal
        (exists rs rr. SMReplay.conn_events_sent_seal_replay model5_s
           (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = server_material_s; }; }) ::
            CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = server_read_material_s; }; }) ::
            [
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_s); };
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert_s); };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_s);
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_s); };
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf_s); };
              CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material_s; }; });
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf_s); };
              CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material_s; }; });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)
            ])
           rs rr server.CS.cs_model) /\
        CS.legal_event model5_s
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = server_material_s; }; })) /\
        CS.step_model model5_s
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = server_material_s; }; })) == Some server_after_write_s /\
        CS.step_model server_after_write_s
          (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = server_read_material_s; }; })) == Some server_after_read_s /\
        // client prefix replay
        (exists rs rr. SMReplay.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
           rs rr model4_c) /\
        // client suffix replay + covers + steps + legal
        (exists rs rr. SMReplay.conn_events_received_decode_replay model4_c
           (e4_c :: e5_c ::
            [
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
              CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
              e13_c;
              e14_c;
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
            ])
           rs rr client.CS.cs_model) /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        PNTCAS.client_no_tail_application_install_cover e13_c e14_c /\
        CS.legal_event model4_c e4_c /\
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.legal_event client_after_e4_c e5_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c)
      (ensures PWL.write_read_record_material_aligned server_after_read_s client_after_installs_c)
=
  let server_suffix =
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = server_material_s; }; }) ::
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = server_read_material_s; }; }) ::
    [
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_s); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert_s); };
      CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_s);
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_s); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf_s); };
      CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material_s; }; });
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf_s); };
      CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material_s; }; });
      CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)
    ] in
  let client_suffix =
    e4_c :: e5_c ::
    [
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
      CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
      e13_c;
      e14_c;
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
    ] in
  lemma_server_suffix_all_not_hello ee_s cert_s cv_s sf_s cf_s
    server_material_s server_read_material_s server_app_write_material_s server_app_read_material_s;
  lemma_client_suffix_all_not_hello e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c;
  lemma_shared_secret_eq client server ch_s selection_s server_shared_s sh_s model5_s
    server_suffix start_c ch_c sh_c client_shared_c model4_c client_suffix;
  lemma_server_prefix_secret_transcript
    (CS.initial_model server.CS.cs_model.CS.model_config)
    ch_s selection_s server_shared_s sh_s model5_s;
  lemma_client_prefix_secret_transcript
    (CS.initial_model client.CS.cs_model.CS.model_config)
    start_c ch_c sh_c client_shared_c model4_c;
  lemma_hs_secret_seq_eq server_shared_s client_shared_c;
  lemma_server_final_slots server ch_s selection_s server_shared_s sh_s model5_s server_suffix;
  lemma_client_final_slots client start_c ch_c sh_c client_shared_c model4_c client_suffix;
  lemma_checkpoint_th_sh_from_milestone client server;
  lemma_transcript_eq_from_checkpoint client server model5_s model4_c ch_s sh_s ch_c sh_c;
  assert (Seq.equal server_shared_s client_shared_c);
  assert (model5_s.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          Some (K.handshake_secret (K.early_secret B.empty) server_shared_s));
  assert (model4_c.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          Some (K.handshake_secret (K.early_secret B.empty) client_shared_c));
  assert (match
            model5_s.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
            model4_c.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
          with
          | Some ss, Some cs -> Seq.equal ss cs
          | _, _ -> False);
  assert (Seq.equal model5_s.CS.model_handshake.CS.hs_transcript
                    model4_c.CS.model_handshake.CS.hs_transcript);
  lemma_hole1_alignment model5_s server_after_write_s server_after_read_s
    server_material_s server_read_material_s
    model4_c client_after_e4_c client_after_installs_c e4_c e5_c
#pop-options


// ===================================================================
// HOLE 2: server-sent / client-received post-cleartext suffix bytes equal
// ===================================================================

// Byte-preserving (on raw_sent) peel of an event with empty sent-delta
// (local events OR received network events).
#push-options "--z3rlimit 10"
noextract
let peel_sent_empty_dsent
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        (CS.ConnLocalEvent? ev \/
         (CS.ConnNetworkEvent? ev /\
          (CS.ConnNetworkEvent?._0 ev).CL.message_direction == CL.Received)) /\
        SMReplay.conn_events_sent_seal_replay model (ev :: rest) rs rr final)
      (ensures
        CS.step_model model ev == Some (step_next model ev) /\
        (exists (tr:B.bytes).
          SMReplay.conn_events_sent_seal_replay (step_next model ev) rest rs tr final))
=
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
  with
  (
    assert (Seq.equal delta_sent B.empty);
    Seq.append_empty_l tail_sent;
    assert (Seq.equal rs tail_sent);
    Seq.lemma_eq_elim rs tail_sent;
    assert (step_next model ev == model1);
    introduce exists (tr:B.bytes).
      SMReplay.conn_events_sent_seal_replay (step_next model ev) rest rs tr final
    with tail_received
    and ()
  )
#pop-options

// The single Sent ServerHello event: raw_sent == serialize(ServerHello sh)
#push-options "--z3rlimit 10"
noextract
let peel_sent_server_hello_bytes
  (model:CS.connection_model) (sh:GSH.serverHello)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay model
          [CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello sh);
           })] rs rr final)
      (ensures
        Seq.equal rs (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
=
  let ev = CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello sh);
           }) in
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev [] rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_sent_seal_replay model1 [] tail_sent tail_received final
  with
  (
    assert (Seq.equal tail_sent B.empty);
    Seq.append_empty_r delta_sent;
    assert (Seq.equal rs delta_sent);
    assert (Seq.equal delta_sent (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))));
    Seq.lemma_eq_elim rs (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh)))
  )
#pop-options

// ---- received-decode side ----
#push-options "--z3rlimit 10"
noextract
let peel_received_empty_drecv
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        (CS.ConnLocalEvent? ev \/
         (CS.ConnNetworkEvent? ev /\
          (CS.ConnNetworkEvent?._0 ev).CL.message_direction == CL.Sent)) /\
        SMReplay.conn_events_received_decode_replay model (ev :: rest) rs rr final)
      (ensures
        CS.step_model model ev == Some (step_next model ev) /\
        (exists (ts:B.bytes).
          SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts rr final))
=
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  with
  (
    assert (Seq.equal delta_received B.empty);
    Seq.append_empty_l tail_received;
    assert (Seq.equal rr tail_received);
    Seq.lemma_eq_elim rr tail_received;
    assert (step_next model ev == model1);
    introduce exists (ts:B.bytes).
      SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts rr final
    with tail_sent
    and ()
  )
#pop-options

// A single local event: received-decode replay => raw_received empty
#push-options "--z3rlimit 10"
noextract
let received_local_singleton_rr_empty
  (model:CS.connection_model) (lev:CS.local_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay model [CS.ConnLocalEvent lev] rs rr final)
      (ensures Seq.equal rr B.empty)
=
  let ev = CS.ConnLocalEvent lev in
  PWReplay.lemma_conn_events_received_decode_replay_head model ev [] rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_received_decode_replay model1 [] tail_sent tail_received final
  with
  (
    assert (Seq.equal delta_received B.empty);
    assert (Seq.equal tail_received B.empty);
    Seq.append_empty_l tail_received;
    assert (Seq.equal rr tail_received)
  )
#pop-options

// The RecvSH followed by a single local event: raw_received == serialize(ServerHello sh)
#push-options "--z3rlimit 10"
noextract
let peel_received_server_hello_then_local_bytes
  (model:CS.connection_model) (sh:GSH.serverHello) (lev:CS.local_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay model
          [ CS.ConnNetworkEvent ({
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.ServerHello sh);
            });
            CS.ConnLocalEvent lev ] rs rr final)
      (ensures
        Seq.equal rr (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
=
  let ev = CS.ConnNetworkEvent ({
             CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ServerHello sh);
           }) in
  let rest = [CS.ConnLocalEvent lev] in
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  with
  (
    assert (Seq.equal delta_received (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))));
    received_local_singleton_rr_empty model1 lev tail_sent tail_received final;
    assert (Seq.equal tail_received B.empty);
    Seq.append_empty_r delta_received;
    assert (Seq.equal rr delta_received);
    Seq.lemma_eq_elim rr (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh)))
  )
#pop-options

// ==== Full prefix byte characterizations ====
#push-options "--z3rlimit 10"
noextract
let lemma_server_prefix_sent_bytes
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (sel:CS.server_handshake_selection)
  (shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (ps pr:B.bytes) (m5:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay m0
          (PWSeg.server_cleartext_handshake_prefix_events ch sel shared sh)
          ps pr m5)
      (ensures
        Seq.equal ps (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
=
  let e0 = CS.ConnLocalEvent CS.LocalStartServer in
  let e1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
  let e2 = CS.ConnLocalEvent (CS.LocalSelectServerParameters sel) in
  let e3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared) in
  let e4 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ServerHello sh); }) in
  peel_sent_empty_dsent m0 e0 [e1;e2;e3;e4] ps pr m5;
  let m1 = step_next m0 e0 in
  eliminate exists (tr1:B.bytes). SMReplay.conn_events_sent_seal_replay m1 [e1;e2;e3;e4] ps tr1 m5
  with (
    peel_sent_empty_dsent m1 e1 [e2;e3;e4] ps tr1 m5;
    let m2 = step_next m1 e1 in
    eliminate exists (tr2:B.bytes). SMReplay.conn_events_sent_seal_replay m2 [e2;e3;e4] ps tr2 m5
    with (
      peel_sent_empty_dsent m2 e2 [e3;e4] ps tr2 m5;
      let m3 = step_next m2 e2 in
      eliminate exists (tr3:B.bytes). SMReplay.conn_events_sent_seal_replay m3 [e3;e4] ps tr3 m5
      with (
        peel_sent_empty_dsent m3 e3 [e4] ps tr3 m5;
        let m4 = step_next m3 e3 in
        eliminate exists (tr4:B.bytes). SMReplay.conn_events_sent_seal_replay m4 [e4] ps tr4 m5
        with (
          peel_sent_server_hello_bytes m4 sh ps tr4 m5
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 10"
noextract
let lemma_client_prefix_received_bytes
  (m0:CS.connection_model)
  (start:CS.handshake_start) (ch:GCH.clientHello)
  (sh:GSH.serverHello) (shared:C.x25519_shared_secret)
  (ps pr:B.bytes) (m4:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay m0
          (PWSeg.client_cleartext_handshake_prefix_events start ch sh shared)
          ps pr m4)
      (ensures
        Seq.equal pr (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
=
  let f0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let f1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
  let f2 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ServerHello sh); }) in
  let f3 = CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared) in
  peel_received_empty_drecv m0 f0 [f1;f2;f3] ps pr m4;
  let m1 = step_next m0 f0 in
  eliminate exists (ts1:B.bytes). SMReplay.conn_events_received_decode_replay m1 [f1;f2;f3] ts1 pr m4
  with (
    peel_received_empty_drecv m1 f1 [f2;f3] ts1 pr m4;
    let m2 = step_next m1 f1 in
    eliminate exists (ts2:B.bytes). SMReplay.conn_events_received_decode_replay m2 [f2;f3] ts2 pr m4
    with (
      peel_received_server_hello_then_local_bytes m2 sh (CS.LocalDeriveSharedSecret shared) ts2 pr m4
    )
  )
#pop-options

// Byte-PRESERVING peel of a local (empty-delta) event from a sent-seal replay.
#push-options "--z3rlimit 10"
noextract
let peel_sent_bp
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.ConnLocalEvent? ev /\
        SMReplay.conn_events_sent_seal_replay model (ev :: rest) rs rr final)
      (ensures
        CS.legal_event model ev /\
        CS.step_model model ev == Some (step_next model ev) /\
        SMReplay.conn_events_sent_seal_replay (step_next model ev) rest rs rr final)
=
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
  with
  (
    assert (Seq.equal delta_sent B.empty);
    assert (Seq.equal delta_received B.empty);
    Seq.append_empty_l tail_sent;
    Seq.append_empty_l tail_received;
    Seq.lemma_eq_elim rs tail_sent;
    Seq.lemma_eq_elim rr tail_received;
    assert (step_next model ev == model1)
  )
#pop-options

#push-options "--z3rlimit 10"
noextract
let peel_received_bp
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.ConnLocalEvent? ev /\
        SMReplay.conn_events_received_decode_replay model (ev :: rest) rs rr final)
      (ensures
        CS.legal_event model ev /\
        CS.step_model model ev == Some (step_next model ev) /\
        SMReplay.conn_events_received_decode_replay (step_next model ev) rest rs rr final)
=
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  with
  (
    assert (Seq.equal delta_sent B.empty);
    assert (Seq.equal delta_received B.empty);
    Seq.append_empty_l tail_sent;
    Seq.append_empty_l tail_received;
    Seq.lemma_eq_elim rs tail_sent;
    Seq.lemma_eq_elim rr tail_received;
    assert (step_next model ev == model1)
  )
#pop-options

// SH serialize equality from the cleartext final-hello milestone + slot identification
#push-options "--z3rlimit 10"
noextract
let lemma_sh_serialize_eq_from_milestone
  (client server:CS.connection_state)
  (sh_s sh_c:GSH.serverHello)
  : Lemma
      (requires
        clean16_cleartext_final_hello_slot_milestone client server /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh_s /\
        client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh_c)
      (ensures
        Seq.equal
          (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_s)))
          (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_c))))
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
    assert (server_sh == sh_s);
    assert (client_sh == sh_c);
    eliminate exists (client_ch_raw server_ch_raw client_sh_raw server_sh_raw:B.bytes).
      Seq.equal client_ch_raw server_ch_raw /\
      Seq.equal server_sh_raw client_sh_raw /\
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) client_ch_raw /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) server_ch_raw /\
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) server_sh_raw /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) client_sh_raw
    with (
      assert (Seq.equal server_sh_raw
                (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello server_sh))));
      assert (Seq.equal client_sh_raw
                (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello client_sh))));
      assert (Seq.equal server_sh_raw client_sh_raw);
      Seq.lemma_eq_elim
        (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_s)))
        (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_c)))
    )
  )
#pop-options

// Append left-cancellation on Seq.equal
#push-options "--z3rlimit 10"
noextract
let lemma_append_left_cancel
  (a b p1 s1 p2 s2:B.bytes)
  : Lemma
      (requires
        Seq.equal a (B.append p1 s1) /\
        Seq.equal b (B.append p2 s2) /\
        Seq.equal a b /\
        Seq.equal p1 p2)
      (ensures Seq.equal s1 s2)
=
  Seq.lemma_eq_elim p1 p2;
  Seq.lemma_append_inj p1 s1 p2 s2
#pop-options

// The two covered client handshake-install events are local events.
#push-options "--z3rlimit 10 --ifuel 2"
noextract
let lemma_two_install_events_are_local
  (e4 e5:CS.conn_event)
  : Lemma
      (requires PCPS.client_no_tail_two_handshake_install_cover e4 e5)
      (ensures CS.ConnLocalEvent? e4 /\ CS.ConnLocalEvent? e5)
=
  PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4 e5;
  eliminate
    (PCPS.client_no_tail_handshake_write_install_event e4 /\
     PCPS.client_no_tail_handshake_read_install_event e5) \/
    (PCPS.client_no_tail_handshake_read_install_event e4 /\
     PCPS.client_no_tail_handshake_write_install_event e5)
  with (
    PCPS.lemma_client_no_tail_handshake_write_install_event_cases e4;
    PCPS.lemma_client_no_tail_handshake_read_install_event_cases e5
  )
  and (
    PCPS.lemma_client_no_tail_handshake_read_install_event_cases e4;
    PCPS.lemma_client_no_tail_handshake_write_install_event_cases e5
  )
#pop-options


// ===== HOLE 2 bundled: server-sent / client-received suffix byte equality =====
#push-options "--z3rlimit 10"
noextract
let lemma_pack_server_bytes_real
  (client server:CS.connection_state)
  (ch_s:GCH.clientHello) (selection_s:CS.server_handshake_selection)
  (server_shared_s:C.x25519_shared_secret) (sh_s:GSH.serverHello)
  (ee_s:GEE.encryptedExtensions) (cert_s:GCert.certificate) (cv_s:GCV.certificateVerify)
  (sf_s:GFin.finished) (cf_s:GFin.finished)
  (server_material_s server_read_material_s server_app_write_material_s server_app_read_material_s:CS.traffic_key_material)
  (model5_s:CS.connection_model)
  (prefix_sent_s prefix_received_s suffix_sent_s suffix_received_s:B.bytes)
  (start_c:CS.handshake_start) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (client_shared_c:C.x25519_shared_secret)
  (e4_c e5_c:CS.conn_event)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (e13_c e14_c:CS.conn_event) (cf_c:GFin.finished)
  (model4_c:CS.connection_model)
  (prefix_sent_c prefix_received_c suffix_received_c:B.bytes)
  : Lemma
      (requires
        clean16_cleartext_final_hello_slot_milestone client server /\
        SMCorr.paired_wire_logs client server /\
        // server prefix concrete sent replay
        SMReplay.conn_events_sent_seal_replay
          (CS.initial_model server.CS.cs_model.CS.model_config)
          (PWSeg.server_cleartext_handshake_prefix_events ch_s selection_s server_shared_s sh_s)
          prefix_sent_s prefix_received_s model5_s /\
        // server suffix replay (existential) reaching final
        (exists rs rr. SMReplay.conn_events_sent_seal_replay model5_s
           (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = server_material_s; }; }) ::
            CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = server_read_material_s; }; }) ::
            [
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_s); };
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert_s); };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_s);
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_s); };
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf_s); };
              CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material_s; }; });
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf_s); };
              CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
                CS.install_role = CS.ServerEndpoint;
                CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material_s; }; });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)
            ])
           rs rr server.CS.cs_model) /\
        // server byte split
        Seq.equal server.CS.cs_wire_log.CL.raw_sent (B.append prefix_sent_s suffix_sent_s) /\
        // client prefix concrete received replay
        SMReplay.conn_events_received_decode_replay
          (CS.initial_model client.CS.cs_model.CS.model_config)
          (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
          prefix_sent_c prefix_received_c model4_c /\
        // client suffix replay (existential) reaching final
        (exists rs rr. SMReplay.conn_events_received_decode_replay model4_c
           (e4_c :: e5_c ::
            [
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
              CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
              CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
              e13_c;
              e14_c;
              CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
            ])
           rs rr client.CS.cs_model) /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        PNTCAS.client_no_tail_application_install_cover e13_c e14_c /\
        // client byte split
        Seq.equal client.CS.cs_wire_log.CL.raw_received (B.append prefix_received_c suffix_received_c))
      (ensures Seq.equal suffix_sent_s suffix_received_c)
=
  let server_suffix =
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = server_material_s; }; }) ::
    CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
      CS.install_role = CS.ServerEndpoint;
      CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = server_read_material_s; }; }) ::
    [
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_s); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert_s); };
      CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_s);
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_s); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf_s); };
      CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material_s; }; });
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf_s); };
      CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material_s; }; });
      CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)
    ] in
  let client_suffix =
    e4_c :: e5_c ::
    [
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
      CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
      e13_c;
      e14_c;
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
    ] in
  lemma_server_suffix_all_not_hello ee_s cert_s cv_s sf_s cf_s
    server_material_s server_read_material_s server_app_write_material_s server_app_read_material_s;
  lemma_client_suffix_all_not_hello e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c;
  lemma_server_final_slots server ch_s selection_s server_shared_s sh_s model5_s server_suffix;
  lemma_client_final_slots client start_c ch_c sh_c client_shared_c model4_c client_suffix;
  lemma_sh_serialize_eq_from_milestone client server sh_s sh_c;
  lemma_server_prefix_sent_bytes
    (CS.initial_model server.CS.cs_model.CS.model_config)
    ch_s selection_s server_shared_s sh_s prefix_sent_s prefix_received_s model5_s;
  lemma_client_prefix_received_bytes
    (CS.initial_model client.CS.cs_model.CS.model_config)
    start_c ch_c sh_c client_shared_c prefix_sent_c prefix_received_c model4_c;
  Seq.lemma_eq_elim prefix_sent_s
    (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_s)));
  Seq.lemma_eq_elim
    (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_s)))
    (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_c)));
  Seq.lemma_eq_elim prefix_received_c
    (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_c)));
  assert (Seq.equal prefix_sent_s prefix_received_c);
  lemma_append_left_cancel
    server.CS.cs_wire_log.CL.raw_sent client.CS.cs_wire_log.CL.raw_received
    prefix_sent_s suffix_sent_s prefix_received_c suffix_received_c
#pop-options


// ===================================================================
// HOLE 4 support: client-sent / server-received client-finished suffix
// byte equality via wire-record uniqueness.
// ===================================================================

#push-options "--z3rlimit 10"
noextract
let lemma_slice_prefix_append_h4 (p r:B.bytes)
  : Lemma (Seq.equal (Seq.slice (B.append p r) 0 (B.length p)) p)
=
  Seq.lemma_len_append p r;
  introduce forall (i:nat{i < B.length p}).
      Seq.index (Seq.slice (B.append p r) 0 (B.length p)) i == Seq.index p i
  with (
    Seq.lemma_index_slice (B.append p r) 0 (B.length p) i;
    Seq.lemma_index_app1 p r i
  );
  Seq.lemma_eq_intro (Seq.slice (B.append p r) 0 (B.length p)) p
#pop-options

#push-options "--z3rlimit 10"
noextract
let lemma_parse_record_wire_stable_append_h4
  (p x:B.bytes) (ct:T.content_type) (frag:B.bytes)
  : Lemma
      (requires W.parse_record_wire p == Some (ct, frag, B.length p))
      (ensures W.parse_record_wire (B.append p x) == Some (ct, frag, B.length p))
=
  let s = B.append p x in
  Seq.lemma_len_append p x;
  lemma_slice_prefix_append_h4 p x;
  assert (Seq.slice s 0 (B.length p) == p);
  WRD.lemma_parse_record_wire_from_prefix s ct frag (B.length p)
#pop-options

#push-options "--z3rlimit 10"
noextract
let lemma_first_wire_record_unique_split_h4
  (s p1 r1 p2 r2:B.bytes) (o1 o2:T.content_type) (f1 f2:B.bytes)
  : Lemma
      (requires
        Seq.equal s (B.append p1 r1) /\
        Seq.equal s (B.append p2 r2) /\
        W.parse_record_wire p1 == Some (o1, f1, B.length p1) /\
        W.parse_record_wire p2 == Some (o2, f2, B.length p2))
      (ensures Seq.equal p1 p2 /\ Seq.equal r1 r2)
=
  lemma_parse_record_wire_stable_append_h4 p1 r1 o1 f1;
  lemma_parse_record_wire_stable_append_h4 p2 r2 o2 f2;
  Seq.lemma_eq_elim s (B.append p1 r1);
  Seq.lemma_eq_elim s (B.append p2 r2);
  assert (W.parse_record_wire s == Some (o1, f1, B.length p1));
  assert (W.parse_record_wire s == Some (o2, f2, B.length p2));
  assert (B.length p1 == B.length p2);
  Seq.lemma_len_append p1 r1;
  Seq.lemma_len_append p2 r2;
  introduce forall (i:nat{i < B.length p1}). Seq.index p1 i == Seq.index p2 i
  with (
    Seq.lemma_index_app1 p1 r1 i;
    Seq.lemma_index_app1 p2 r2 i
  );
  Seq.lemma_eq_intro p1 p2;
  let n = B.length p1 in
  introduce forall (i:nat{i < B.length r1}). Seq.index r1 i == Seq.index r2 i
  with (
    Seq.lemma_index_app2 p1 r1 (n + i);
    Seq.lemma_index_app2 p2 r2 (n + i)
  );
  Seq.lemma_eq_intro r1 r2
#pop-options

#push-options "--z3rlimit 10 --ifuel 1"
noextract
let lemma_client_hello_sent_is_wire_h4 (ch:GCH.clientHello) (raw:B.bytes)
  : Lemma
      (requires
        WFL.supported_client_hello_wire_profile ch /\
        Seq.equal raw (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))))
      (ensures exists frag. W.parse_record_wire raw == Some (T.Handshake, frag, B.length raw))
=
  let frag = W.serialize_handshake (M.ClientHello ch) in
  WFL.lemma_serialize_handshake_client_hello_record_bound ch;
  WFL.lemma_parse_record_wire_serialize_record T.Handshake frag;
  W.lemma_serialize_tls_message_handshake (M.ClientHello ch);
  assert (W.serialize_tls_message (M.TlsHandshake (M.ClientHello ch)) == (T.Handshake, frag));
  assert (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))
          == W.serialize_record T.Handshake frag);
  Seq.lemma_eq_elim raw (W.serialize_record T.Handshake frag);
  assert (W.parse_record_wire raw == Some (T.Handshake, frag, B.length raw))
#pop-options

#push-options "--z3rlimit 10 --ifuel 1"
noextract
let lemma_received_client_hello_is_wire_h4 (ch:GCH.clientHello) (raw:B.bytes)
  : Lemma
      (requires CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) raw)
      (ensures exists frag. W.parse_record_wire raw == Some (T.Handshake, frag, B.length raw))
= ()
#pop-options

#push-options "--z3rlimit 10"
noextract
let peel_sent_cleartext_ch_head
  (model:CS.connection_model) (ch:GCH.clientHello) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay model
          (CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) :: rest) rs rr final)
      (ensures
        (let ev = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
         CS.step_model model ev == Some (step_next model ev) /\
         (exists (ts tr:B.bytes).
            Seq.equal rs (B.append (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))) ts) /\
            SMReplay.conn_events_sent_seal_replay (step_next model ev) rest ts tr final)))
=
  let ev = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
  with
  (
    assert (Seq.equal delta_sent (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))));
    assert (step_next model ev == model1);
    introduce exists (ts tr:B.bytes).
        Seq.equal rs (B.append (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))) ts) /\
        SMReplay.conn_events_sent_seal_replay (step_next model ev) rest ts tr final
    with tail_sent tail_received
    and (
      Seq.lemma_eq_elim rs (B.append (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))) tail_sent)
    )
  )
#pop-options

#push-options "--z3rlimit 10"
noextract
let peel_received_ch_recv_head
  (model:CS.connection_model) (ch:GCH.clientHello) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay model
          (CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) :: rest) rs rr final)
      (ensures
        (let ev = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
         CS.step_model model ev == Some (step_next model ev) /\
         (exists (ds ts tr:B.bytes).
            Seq.equal rr (B.append ds tr) /\
            CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) ds /\
            SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts tr final)))
=
  let ev = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    SMCan.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    SMReplay.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  with
  (
    assert (CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) delta_received);
    assert (step_next model ev == model1);
    introduce exists (ds ts tr:B.bytes).
        Seq.equal rr (B.append ds tr) /\
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) ds /\
        SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts tr final
    with delta_received tail_sent tail_received
    and ()
  )
#pop-options

#push-options "--z3rlimit 10 --ifuel 2"
noextract
let lemma_two_server_install_events_are_local
  (e5 e6:CS.conn_event)
  : Lemma
      (requires PNTSS.server_no_tail_two_handshake_install_cover e5 e6)
      (ensures CS.ConnLocalEvent? e5 /\ CS.ConnLocalEvent? e6)
=
  PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e5 e6
#pop-options

noextract
let is_empty_sent_ev (ev:CS.conn_event) : bool =
  CS.ConnLocalEvent? ev ||
  (CS.ConnNetworkEvent? ev &&
   (CS.ConnNetworkEvent?._0 ev).CL.message_direction = CL.Received)

noextract
let is_empty_recv_ev (ev:CS.conn_event) : bool =
  CS.ConnLocalEvent? ev ||
  (CS.ConnNetworkEvent? ev &&
   (CS.ConnNetworkEvent?._0 ev).CL.message_direction = CL.Sent)

#push-options "--z3rlimit 10 --ifuel 1"
noextract
let rec lemma_empty_sent_tail_collapses
  (model:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay model evs rs rr final /\
        FStar.List.Tot.for_all is_empty_sent_ev evs)
      (ensures Seq.equal rs B.empty)
      (decreases evs)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    peel_sent_empty_dsent model ev rest rs rr final;
    eliminate exists (tr:B.bytes). SMReplay.conn_events_sent_seal_replay (step_next model ev) rest rs tr final
    with (
      lemma_empty_sent_tail_collapses (step_next model ev) rest rs tr final
    )
#pop-options

#push-options "--z3rlimit 10 --ifuel 1"
noextract
let rec lemma_empty_recv_tail_collapses
  (model:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay model evs rs rr final /\
        FStar.List.Tot.for_all is_empty_recv_ev evs)
      (ensures Seq.equal rr B.empty)
      (decreases evs)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    peel_received_empty_drecv model ev rest rs rr final;
    eliminate exists (ts:B.bytes). SMReplay.conn_events_received_decode_replay (step_next model ev) rest ts rr final
    with (
      lemma_empty_recv_tail_collapses (step_next model ev) rest ts rr final
    )
#pop-options

#push-options "--z3rlimit 10 --fuel 12 --ifuel 2"
noextract
let lemma_client_exact_prefix_sent_ch
  (m0:CS.connection_model)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (e4 e5:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  (ps pr:B.bytes) (m12:CS.connection_model)
  : Lemma
      (requires
        PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        SMReplay.conn_events_sent_seal_replay m0
          (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
           e4 :: e5 ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
           CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.Finished sf); }) :: [])
          ps pr m12)
      (ensures
        Seq.equal ps (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))))
=
  let ev0 = CS.ConnLocalEvent (CS.LocalStartHandshake start) in
  let ev1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
  let tail10 =
    [ CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello sh); });
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared);
      e4; e5;
      CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); });
      CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert); });
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
      CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv); });
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
      CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf); }) ] in
  let serialized_ch = CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch)) in
  peel_sent_empty_dsent m0 ev0 (ev1 :: tail10) ps pr m12;
  let m1 = step_next m0 ev0 in
  eliminate exists (tr0:B.bytes). SMReplay.conn_events_sent_seal_replay m1 (ev1 :: tail10) ps tr0 m12
  with (
    peel_sent_cleartext_ch_head m1 ch tail10 ps tr0 m12;
    let m2 = step_next m1 ev1 in
    eliminate exists (ts trx:B.bytes).
        Seq.equal ps (B.append serialized_ch ts) /\
        SMReplay.conn_events_sent_seal_replay m2 tail10 ts trx m12
    with (
      lemma_two_install_events_are_local e4 e5;
      assert (FStar.List.Tot.for_all is_empty_sent_ev tail10);
      lemma_empty_sent_tail_collapses m2 tail10 ts trx m12;
      assert (Seq.equal ts B.empty);
      Seq.append_empty_r serialized_ch;
      Seq.lemma_eq_elim ps serialized_ch
    )
  )
#pop-options

#push-options "--z3rlimit 10 --fuel 12 --ifuel 2"
noextract
let lemma_server_prefix_received_ch
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (sel:CS.server_handshake_selection)
  (shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (ps pr:B.bytes) (m5:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay m0
          (PWSeg.server_cleartext_handshake_prefix_events ch sel shared sh)
          ps pr m5)
      (ensures CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) pr)
=
  let e0 = CS.ConnLocalEvent CS.LocalStartServer in
  let e1 = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
  let tail3 =
    [ CS.ConnLocalEvent (CS.LocalSelectServerParameters sel);
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared);
      CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ] in
  assert (PWSeg.server_cleartext_handshake_prefix_events ch sel shared sh
          == e0 :: e1 :: tail3);
  peel_received_bp m0 e0 (e1 :: tail3) ps pr m5;
  let m1 = step_next m0 e0 in
  peel_received_ch_recv_head m1 ch tail3 ps pr m5;
  let m2 = step_next m1 e1 in
  eliminate exists (ds ts tr:B.bytes).
      Seq.equal pr (B.append ds tr) /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) ds /\
      SMReplay.conn_events_received_decode_replay m2 tail3 ts tr m5
  with (
    assert (FStar.List.Tot.for_all is_empty_recv_ev tail3);
    lemma_empty_recv_tail_collapses m2 tail3 ts tr m5;
    assert (Seq.equal tr B.empty);
    Seq.append_empty_r ds;
    Seq.lemma_eq_elim pr ds
  )
#pop-options

#push-options "--z3rlimit 10 --fuel 12 --ifuel 2"
noextract
let lemma_server_flight_received_empty
  (m0:CS.connection_model)
  (e5 e6:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  (ps pr:B.bytes) (mf:CS.connection_model)
  : Lemma
      (requires
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
        SMReplay.conn_events_received_decode_replay m0
          [ e5; e6;
            CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); });
            CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Certificate cert); });
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv); });
            CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished sf); }) ]
          ps pr mf)
      (ensures Seq.equal pr B.empty)
=
  let evs =
    [ e5; e6;
      CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); });
      CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Certificate cert); });
      CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
      CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv); });
      CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished sf); }) ] in
  lemma_two_server_install_events_are_local e5 e6;
  assert (FStar.List.Tot.for_all is_empty_recv_ev evs);
  lemma_empty_recv_tail_collapses m0 evs ps pr mf
#pop-options
#pop-options
