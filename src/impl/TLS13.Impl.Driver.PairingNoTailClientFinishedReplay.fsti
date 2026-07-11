module TLS13.Impl.Driver.PairingNoTailClientFinishedReplay

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module GFin  = TLS13.Wire.Generated.Finished
module PCB = TLS13.Impl.Driver.PairingCleanBoundary
module PCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PNTCFRE = TLS13.Impl.Driver.PairingNoTailClientFinishedRawEquality
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedStaged
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module PWL = TLS13.ConnectionState.ProtectedWireBase
module Seq = FStar.Seq
module T = TLS13.Types

(**
  A narrow package for exactly the ClientFinished part of
  [PairingStagedNormalizedBoundary.paired_supported_normalized_staged_replay_boundary_inputs].

  The sender replay starts at the explicit client-handshake-write installed
  model, runs local server-Finished verification, the canonical client
  application write/read installs, and the protected client Finished send.  The
  receiver replay starts at the explicit server-handshake-read installed model,
  runs the server application write install, and receives the protected client
  Finished.
**)
noeq
type client_finished_replay_witnesses = {
  cfr_client_finished_write_install_source: CS.connection_model;
  cfr_client_finished_read_install_source: CS.connection_model;
  cfr_client_finished_client_write_material: CS.traffic_key_material;
  cfr_client_finished_server_read_material: CS.traffic_key_material;
  cfr_client_finished_sender: CS.connection_model;
  cfr_client_finished_receiver: CS.connection_model;
  cfr_client_finished_raw_sent: B.bytes;
  cfr_client_finished_raw_received: B.bytes;
  cfr_server_finished_raw_sent: B.bytes;
  cfr_server_finished_raw_received: B.bytes;
  cfr_client_finished_final: CS.connection_model;
  cfr_server_finished_final: CS.connection_model;
}

noextract
let client_finished_staged_replay_fragment
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (r:client_finished_replay_witnesses)
  : prop =
  CS.record_key_iv_material_agrees
    (CS.record_material_of_traffic_material
      r.cfr_client_finished_client_write_material)
    (CS.record_material_of_traffic_material
      r.cfr_client_finished_server_read_material) /\
  CS.step_model
    r.cfr_client_finished_write_install_source
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficHandshake;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = r.cfr_client_finished_client_write_material;
      })) == Some r.cfr_client_finished_sender /\
  CS.step_model
    r.cfr_client_finished_read_install_source
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = r.cfr_client_finished_server_read_material;
        };
      })) == Some r.cfr_client_finished_receiver /\
  Seq.equal
    r.cfr_client_finished_raw_sent
    r.cfr_server_finished_raw_received /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_sent_msg4 /\
  PWL.protected_handshake_wire_round_trip_message w.PCB.hcb_received_msg4 /\
  CS.step_model
    r.cfr_client_finished_sender
    (CS.ConnLocalEvent (CS.LocalVerifyFinished w.PCB.hcb_verified_server_finished)) ==
    Some w.PCB.hcb_cf_client_after_verify /\
  CS.step_model
    w.PCB.hcb_cf_client_after_verify
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficWrite;
        CS.install_material = w.PCB.hcb_client_app_write_material;
      })) == Some w.PCB.hcb_cf_client_after_app_write /\
  CS.step_model
    w.PCB.hcb_cf_client_after_app_write
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeys {
        CS.install_epoch = CS.TrafficApplication;
        CS.install_direction = CS.TrafficRead;
        CS.install_material = w.PCB.hcb_client_app_read_material;
      })) == Some w.PCB.hcb_cf_client_after_app_read /\
  CS.step_model
    r.cfr_client_finished_receiver
    (CS.ConnLocalEvent
      (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = w.PCB.hcb_server_app_write_material;
        };
      })) == Some w.PCB.hcb_cf_server_after_app_write /\
  CS.step_model
    w.PCB.hcb_cf_client_after_app_read
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Sent;
      CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg4;
    }) == Some w.PCB.hcb_cf_client_after_finished /\
  CS.step_model
    w.PCB.hcb_cf_server_after_app_write
    (CS.ConnNetworkEvent {
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg4;
    }) == Some w.PCB.hcb_cf_server_after_finished /\
  CS.conn_events_sent_seal_replay
    r.cfr_client_finished_sender
    (CS.ConnLocalEvent (CS.LocalVerifyFinished w.PCB.hcb_verified_server_finished) ::
     CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeys {
         CS.install_epoch = CS.TrafficApplication;
         CS.install_direction = CS.TrafficWrite;
         CS.install_material = w.PCB.hcb_client_app_write_material;
       }) ::
     CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeys {
         CS.install_epoch = CS.TrafficApplication;
         CS.install_direction = CS.TrafficRead;
         CS.install_material = w.PCB.hcb_client_app_read_material;
       }) ::
     CS.ConnNetworkEvent {
       CL.message_direction = CL.Sent;
       CL.message_value = M.TlsHandshake w.PCB.hcb_sent_msg4;
     } :: w.PCB.hcb_client_finished_rest)
    r.cfr_client_finished_raw_sent
    r.cfr_client_finished_raw_received
    r.cfr_client_finished_final /\
  CS.conn_events_received_decode_replay
    r.cfr_client_finished_receiver
    (CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeysForRole {
         CS.install_role = CS.ServerEndpoint;
         CS.install_payload = {
           CS.install_epoch = CS.TrafficApplication;
           CS.install_direction = CS.TrafficWrite;
           CS.install_material = w.PCB.hcb_server_app_write_material;
         };
       }) ::
     CS.ConnNetworkEvent {
       CL.message_direction = CL.Received;
       CL.message_value = M.TlsHandshake w.PCB.hcb_received_msg4;
     } :: w.PCB.hcb_server_finished_rest)
    r.cfr_server_finished_raw_sent
    r.cfr_server_finished_raw_received
    r.cfr_server_finished_final

(**
  The exact clean16 fact still needed for the ClientFinished side of the staged
  boundary.
**)
noextract
let clean16_client_finished_semantic_replay_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : prop =
  PNB.paired_supported_normalized_replay_boundary_inputs client server w /\
  PNTCFS.paired_no_tail_client_finished_staged_milestone client server /\
  PNTCFRE.paired_client_finished_raw_record_equality client server ==>
  exists r.
    client_finished_staged_replay_fragment client server w r

(**
  A concrete semantic ClientFinished sender-side slice that is derivable from
  replay consistency plus the no-tail ClientFinished event-log shape.

  This deliberately does not mention an arbitrary boundary witness [w]: it only
  exposes the verified split of the client's whole sent/seal replay at the
  no-tail prefix, leaving the later boundary-witness/model-identification step
  explicit.
**)
noextract
let client_finished_exact_suffix_sent_seal_replay_slice
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf
    (model12:CS.connection_model)
    prefix_sent
    prefix_received
    suffix_sent
    suffix_received.
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
      e5 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) ::
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
      e13 ::
      e14 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) ::
      [] /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_sent_seal_replay
      (CS.initial_model client.CS.cs_model.CS.model_config)
      (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
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
       e5 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.Certificate cert);
       }) ::
       CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
       }) ::
       CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.Finished sf);
       }) ::
       [])
      prefix_sent
      prefix_received
      model12 /\
    CS.conn_events_sent_seal_replay
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
       e13 ::
       e14 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.Finished cf);
       }) ::
       [])
      suffix_sent
      suffix_received
      client.CS.cs_model

noextract
let client_finished_exact_suffix_sent_seal_raw_record_slice
  (client:CS.connection_state)
  : prop =
  exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf
    (model12:CS.connection_model)
    prefix_sent
    prefix_received
    suffix_sent
    suffix_received.
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
      e5 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Certificate cert);
      }) ::
      CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.Finished sf);
      }) ::
      CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
      e13 ::
      e14 ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) ::
      [] /\
    PCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append prefix_sent suffix_sent) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append prefix_received suffix_received) /\
    CS.conn_events_sent_seal_replay
      (CS.initial_model client.CS.cs_model.CS.model_config)
      (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
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
       e5 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.Certificate cert);
       }) ::
       CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
       }) ::
       CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.Finished sf);
       }) ::
       [])
      prefix_sent
      prefix_received
      model12 /\
    CS.conn_events_sent_seal_replay
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
       e13 ::
       e14 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.Finished cf);
       }) ::
       [])
      suffix_sent
      suffix_received
      client.CS.cs_model /\
    CS.raw_records_exactly suffix_sent T.Application_data 1

noextract
let client_finished_sent_seal_suffix_head_steps
  (model12:CS.connection_model)
  (sf:GFin.finished)
  (e13 e14:CS.conn_event)
  (cf:GFin.finished)
  (final_model:CS.connection_model)
  : prop =
  exists
    (after_verify:CS.connection_model)
    (after_e13:CS.connection_model)
    (after_e14:CS.connection_model).
    CS.step_model
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf)) ==
      Some after_verify /\
    CS.step_model after_verify e13 == Some after_e13 /\
    CS.step_model after_e13 e14 == Some after_e14 /\
    CS.step_model
      after_e14
      (CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      })) == Some final_model

noextract
let client_finished_exact_suffix_sent_seal_head_step_slice
  (client:CS.connection_state)
  : prop =
  exists
    (sf:GFin.finished)
    (e13 e14:CS.conn_event)
    (cf:GFin.finished)
    (model12:CS.connection_model)
    suffix_sent
    suffix_received.
    PNTCAS.client_no_tail_application_install_cover e13 e14 /\
    CS.conn_events_sent_seal_replay
      model12
      (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
       e13 ::
       e14 ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.Finished cf);
       }) ::
       [])
      suffix_sent
      suffix_received
      client.CS.cs_model /\
    client_finished_sent_seal_suffix_head_steps
      model12
      sf
      e13
      e14
      cf
      client.CS.cs_model /\
    CS.raw_records_exactly suffix_sent T.Application_data 1

noextract
let client_finished_canonical_sent_seal_replay_slice
  (client:CS.connection_state)
  : prop =
  exists
    (sf:GFin.finished)
    (cf:GFin.finished)
    (model12:CS.connection_model)
    (after_verify:CS.connection_model)
    (after_app_write:CS.connection_model)
    (after_app_read:CS.connection_model)
    (client_app_write_material:CS.traffic_key_material)
    (client_app_read_material:CS.traffic_key_material)
    suffix_sent
    suffix_received.
    CS.conn_events_sent_seal_replay
     model12
     (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = client_app_write_material;
        }) ::
      CS.ConnLocalEvent
        (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = client_app_read_material;
        }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.Finished cf);
      }) ::
      [])
     suffix_sent
     suffix_received
     client.CS.cs_model /\
    CS.step_model
     model12
     (CS.ConnLocalEvent (CS.LocalVerifyFinished sf)) == Some after_verify /\
    CS.step_model
     after_verify
     (CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeys {
         CS.install_epoch = CS.TrafficApplication;
         CS.install_direction = CS.TrafficWrite;
         CS.install_material = client_app_write_material;
       })) == Some after_app_write /\
    CS.step_model
     after_app_write
     (CS.ConnLocalEvent
       (CS.LocalInstallTrafficKeys {
         CS.install_epoch = CS.TrafficApplication;
         CS.install_direction = CS.TrafficRead;
         CS.install_material = client_app_read_material;
       })) == Some after_app_read /\
    CS.step_model
     after_app_read
     (CS.ConnNetworkEvent ({
       CL.message_direction = CL.Sent;
       CL.message_value = M.TlsHandshake (M.Finished cf);
     })) == Some      client.CS.cs_model /\
    CS.raw_records_exactly suffix_sent T.Application_data 1

val lemma_client_finished_exact_suffix_sent_seal_replay_slice_from_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTCFS.paired_no_tail_client_finished_staged_milestone client server /\
        CS.connection_state_sent_seal_replay_consistent client)
      (ensures
        client_finished_exact_suffix_sent_seal_replay_slice client)

val lemma_client_finished_exact_suffix_sent_seal_raw_record_slice_from_replay_slice
  (client:CS.connection_state)
  : Lemma
      (requires client_finished_exact_suffix_sent_seal_replay_slice client)
      (ensures client_finished_exact_suffix_sent_seal_raw_record_slice client)

val lemma_client_finished_sent_seal_suffix_head_steps
  (model12:CS.connection_model)
  (sf:GFin.finished)
  (e13 e14:CS.conn_event)
  (cf:GFin.finished)
  (suffix_sent:B.bytes)
  (suffix_received:B.bytes)
  (final_model:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay
          model12
          (CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
           e13 ::
           e14 ::
           CS.ConnNetworkEvent ({
             CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.Finished cf);
           }) ::
           [])
          suffix_sent
          suffix_received
          final_model)
      (ensures
        client_finished_sent_seal_suffix_head_steps
          model12
          sf
          e13
          e14
          cf
          final_model)

val lemma_client_finished_exact_suffix_sent_seal_head_step_slice_from_replay_slice
  (client:CS.connection_state)
  : Lemma
      (requires client_finished_exact_suffix_sent_seal_replay_slice client)
      (ensures client_finished_exact_suffix_sent_seal_head_step_slice client)

val lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_sent_seal_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        client_finished_exact_suffix_sent_seal_replay_slice client)

val lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_sent_seal_raw_record_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        client_finished_exact_suffix_sent_seal_raw_record_slice client)

val lemma_clean16_no_tail_valid_byte_traces_client_finished_exact_suffix_sent_seal_head_step_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        PNTN.paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        client_finished_exact_suffix_sent_seal_head_step_slice client)

val lemma_client_finished_canonical_sent_seal_replay_slice_from_head_step_slice
  (client:CS.connection_state)
  : Lemma
      (requires client_finished_exact_suffix_sent_seal_head_step_slice client)
      (ensures client_finished_canonical_sent_seal_replay_slice client)

val lemma_clean16_no_tail_valid_byte_traces_client_finished_canonical_sent_seal_replay_slice
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
       (requires
         PNTN.paired_supported_no_tail_valid_byte_traces_clean16
           client_initial
           server_initial
           client
           server
           client_received
           client_sent
           server_received
           server_sent)
       (ensures
            client_finished_canonical_sent_seal_replay_slice client)

val lemma_client_finished_staged_replay_fragment_from_staged_boundary_inputs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (s:PSNB.staged_replay_witnesses)
  : Lemma
      (requires
        PSNB.paired_supported_normalized_staged_replay_boundary_inputs
          client
          server
          w
          s)
      (ensures
        exists r.
          client_finished_staged_replay_fragment client server w r)

val lemma_clean16_client_finished_staged_replay_fragment_from_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w /\
        PNTCFS.paired_no_tail_client_finished_staged_milestone client server /\
        PNTCFRE.paired_client_finished_raw_record_equality client server /\
        clean16_client_finished_semantic_replay_completion client server w)
      (ensures
        exists r.
          client_finished_staged_replay_fragment client server w r)

val lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_replay_fragment_from_completion
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
       PNTN.paired_supported_no_tail_valid_byte_traces_clean16
         client_initial
         server_initial
         client
         server
         client_received
         client_sent
         server_received
         server_sent /\
       PNB.paired_supported_normalized_replay_boundary_inputs
         client
         server
         w /\
       clean16_client_finished_semantic_replay_completion client server w)
      (ensures
       exists r.
         client_finished_staged_replay_fragment client server w r)
