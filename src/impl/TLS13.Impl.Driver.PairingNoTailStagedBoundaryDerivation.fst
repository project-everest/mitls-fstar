module TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
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

#push-options "--split_queries always --z3rlimit 10"

let lemma_clean16_no_tail_valid_byte_traces_cleartext_final_hello_slot_milestone
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
        clean16_cleartext_final_hello_slot_milestone client server)
=
  PNTN.lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_replay_suffixes
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (TLS13.Impl.Client.Types.client_end_to_end_invariant client);
  assert (TLS13.Impl.Server.Types.server_end_to_end_invariant server);
  assert (CS.connection_state_raw_event_replay_consistent client);
  assert (CS.connection_state_raw_event_replay_consistent server);
  eliminate exists
    client_start
    client_ch
    client_sh
    client_shared
    client_rest
    server_ch
    selection
    server_shared
    server_sh
    server_rest
    server_mid
    client_mid
    server_suffix_sent
    server_suffix_received
    client_suffix_sent
    client_suffix_received.
    PNTRB.role_local_cleartext_prefix_shape
      client
      server
      client_start
      client_ch
      client_sh
      client_shared
      client_rest
      server_ch
      selection
      server_shared
      server_sh
      server_rest /\
    WFL.supported_client_hello_wire_profile client_ch /\
    PNTRB.normalized_cleartext_raw_wire_bridge
      client_ch
      server_ch
      client_sh
      server_sh /\
    FStar.List.Tot.append
      (TLS13.ConnectionState.ProtectedWireSegmentation.server_cleartext_handshake_prefix_events
        server_ch
        selection
        server_shared
        server_sh)
      server_rest == server.CS.cs_event_log /\
    FStar.List.Tot.append
      (TLS13.ConnectionState.ProtectedWireSegmentation.client_cleartext_handshake_prefix_events
        client_start
        client_ch
        client_sh
        client_shared)
      client_rest == client.CS.cs_event_log /\
    FStar.Seq.equal server_suffix_sent client_suffix_received /\
    FStar.Seq.equal client_suffix_sent server_suffix_received /\
    CS.conn_events_sent_seal_replay
      server_mid
      server_rest
      server_suffix_sent
      server_suffix_received
      server.CS.cs_model /\
    CS.conn_events_received_decode_replay
      server_mid
      server_rest
      server_suffix_sent
      server_suffix_received
      server.CS.cs_model /\
    CS.conn_events_sent_seal_replay
      client_mid
      client_rest
      client_suffix_sent
      client_suffix_received
      client.CS.cs_model /\
    CS.conn_events_received_decode_replay
      client_mid
      client_rest
      client_suffix_sent
      client_suffix_received
      client.CS.cs_model
  returns clean16_cleartext_final_hello_slot_milestone client server
  with _.
  (
    let client_model0 =
      CS.initial_model client.CS.cs_model.CS.model_config in
    let server_model0 =
      CS.initial_model server.CS.cs_model.CS.model_config in
    assert (client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
      }) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
      client_rest);
    assert (server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
      }) ::
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
      }) ::
      server_rest);
    assert (CS.conn_events_raw_replay
      client_model0
      (CS.ConnLocalEvent (CS.LocalStartHandshake client_start) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
       }) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
       client_rest)
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      client.CS.cs_model);
    assert (CS.conn_events_raw_replay
      server_model0
      (CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
       }) ::
       CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
       CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
       }) ::
       server_rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    PNTRB.lemma_client_cleartext_prefix_final_hello_slots_from_raw_replay
      client_model0
      client_start
      client_ch
      client_sh
      client_shared
      client_rest
      client.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received
      client.CS.cs_model;
    PNTRB.lemma_server_cleartext_prefix_final_hello_slots_from_raw_replay
      server_model0
      server_ch
      selection
      server_shared
      server_sh
      server_rest
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    assert (clean16_cleartext_final_hello_slot_milestone client server)
  )

let lemma_clean16_no_tail_valid_byte_traces_staged_boundary_derivation_milestones
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
        clean16_staged_boundary_derivation_milestones client server)
=
  PNTN.lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_replay_suffixes
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_clean16_no_tail_valid_byte_traces_cleartext_final_hello_slot_milestone
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (CD.client_driver_application_ready client);
  assert (SD.server_driver_application_ready server);
  assert (Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server);
  PNTSFS.lemma_clean16_no_tail_valid_byte_traces_server_encrypted_flight_staged_milestone
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTPH.lemma_clean16_no_tail_valid_byte_traces_server_post_two_handshake_installs_tail_order
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSFR.lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_sent_seal_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSFR.lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_ordered_sent_seal_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSFR.lemma_server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice
    server;
  PNTSFR.lemma_server_after_handshake_installs_sent_seal_replay_slice
    server;
  PNTSFR.lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_received_decode_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSFR.lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_ordered_received_decode_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCFRR.lemma_clean16_no_tail_valid_byte_traces_server_client_finished_received_decode_suffix_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSFR.lemma_clean16_no_tail_valid_byte_traces_client_post_derive_received_decode_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSFR.lemma_clean16_no_tail_valid_byte_traces_client_post_derive_ordered_received_decode_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSFR.lemma_clean16_no_tail_valid_byte_traces_client_after_handshake_installs_received_decode_replay_slice
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCFS.lemma_clean16_no_tail_valid_byte_traces_client_finished_staged_milestone
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCFRE.lemma_clean16_no_tail_valid_byte_traces_client_finished_raw_record_equality
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_preserve_connection_state_replay_consistent
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (clean16_staged_boundary_derivation_milestones client server)

let lemma_clean16_staged_boundary_derivation_milestones_client_finished_canonical_sent_seal_replay_slice
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires clean16_staged_boundary_derivation_milestones client server)
      (ensures PNTCFR.client_finished_canonical_sent_seal_replay_slice client)
=
  PNTCFR.lemma_client_finished_exact_suffix_sent_seal_replay_slice_from_staged_milestone
    client
    server;
  PNTCFR.lemma_client_finished_exact_suffix_sent_seal_head_step_slice_from_replay_slice
    client;
  PNTCFR.lemma_client_finished_canonical_sent_seal_replay_slice_from_head_step_slice
    client

let lemma_normalized_replay_boundary_inputs_with_staged_fragments
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  (server_fragment:PNTSFR.server_flight_replay_witnesses)
  (client_fragment:PNTCFR.client_finished_replay_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w /\
        PNTSFR.server_encrypted_flight_staged_replay_fragment
          client
          server
          w
          server_fragment /\
        PNTCFR.client_finished_staged_replay_fragment
          client
          server
          w
          client_fragment)
      (ensures
        PSNB.paired_supported_normalized_staged_replay_boundary client server)
=
  let s = {
    PSNB.snb_server_flight_rest =
      server_fragment.PNTSFR.sfr_server_flight_rest;
    PSNB.snb_client_flight_rest =
      server_fragment.PNTSFR.sfr_client_flight_rest;
    PSNB.snb_server_raw_sent =
      server_fragment.PNTSFR.sfr_server_raw_sent;
    PSNB.snb_server_raw_received =
      server_fragment.PNTSFR.sfr_server_raw_received;
    PSNB.snb_client_raw_sent =
      server_fragment.PNTSFR.sfr_client_raw_sent;
    PSNB.snb_client_raw_received =
      server_fragment.PNTSFR.sfr_client_raw_received;
    PSNB.snb_server_final =
      server_fragment.PNTSFR.sfr_server_final;
    PSNB.snb_client_final =
      server_fragment.PNTSFR.sfr_client_final;
    PSNB.snb_client_finished_write_install_source =
      client_fragment.PNTCFR.cfr_client_finished_write_install_source;
    PSNB.snb_client_finished_read_install_source =
      client_fragment.PNTCFR.cfr_client_finished_read_install_source;
    PSNB.snb_client_finished_client_write_material =
      client_fragment.PNTCFR.cfr_client_finished_client_write_material;
    PSNB.snb_client_finished_server_read_material =
      client_fragment.PNTCFR.cfr_client_finished_server_read_material;
    PSNB.snb_client_finished_sender =
      client_fragment.PNTCFR.cfr_client_finished_sender;
    PSNB.snb_client_finished_receiver =
      client_fragment.PNTCFR.cfr_client_finished_receiver;
    PSNB.snb_client_finished_raw_sent =
      client_fragment.PNTCFR.cfr_client_finished_raw_sent;
    PSNB.snb_client_finished_raw_received =
      client_fragment.PNTCFR.cfr_client_finished_raw_received;
    PSNB.snb_server_finished_raw_sent =
      client_fragment.PNTCFR.cfr_server_finished_raw_sent;
    PSNB.snb_server_finished_raw_received =
      client_fragment.PNTCFR.cfr_server_finished_raw_received;
    PSNB.snb_client_finished_final =
      client_fragment.PNTCFR.cfr_client_finished_final;
    PSNB.snb_server_finished_final =
      client_fragment.PNTCFR.cfr_server_finished_final;
  } in
  assert (PSNB.paired_supported_normalized_staged_replay_boundary_inputs client server w s)
  by (
    Tac.norm
      [delta_only
        [`%PNB.paired_supported_normalized_replay_boundary_inputs;
         `%PSNB.paired_supported_normalized_staged_replay_boundary_inputs;
         `%PNTSFR.server_encrypted_flight_staged_replay_fragment;
         `%PNTCFR.client_finished_staged_replay_fragment]];
    Tac.smt ());
  introduce exists (w':PCB.handshake_complete_boundary_witnesses)
                   (s':PSNB.staged_replay_witnesses).
    PSNB.paired_supported_normalized_staged_replay_boundary_inputs
      client
      server
      w'
      s'
  with w s and ()

let lemma_normalized_replay_boundary_inputs_with_clean16_fragment_completions
  (client:CS.connection_state)
  (server:CS.connection_state)
  (w:PCB.handshake_complete_boundary_witnesses)
  : Lemma
      (requires
        PNB.paired_supported_normalized_replay_boundary_inputs
          client
          server
          w /\
        clean16_staged_boundary_derivation_milestones client server /\
        PNTSFR.clean16_server_encrypted_flight_semantic_replay_completion
          client
          server
          w /\
        PNTCFR.clean16_client_finished_semantic_replay_completion
          client
          server
          w)
      (ensures
        PSNB.paired_supported_normalized_staged_replay_boundary client server)
=
  PNTSFR.lemma_clean16_server_encrypted_flight_staged_replay_fragment_from_completion
    client
    server
    w;
  PNTCFR.lemma_clean16_client_finished_staged_replay_fragment_from_completion
    client
    server
    w;
  eliminate exists server_fragment.
    PNTSFR.server_encrypted_flight_staged_replay_fragment
      client
      server
      w
      server_fragment
  returns PSNB.paired_supported_normalized_staged_replay_boundary client server
  with _.
  (
    eliminate exists client_fragment.
      PNTCFR.client_finished_staged_replay_fragment
        client
        server
        w
        client_fragment
    returns PSNB.paired_supported_normalized_staged_replay_boundary client server
    with _.
    (
      lemma_normalized_replay_boundary_inputs_with_staged_fragments
        client
        server
        w
        server_fragment
        client_fragment
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_normalized_staged_replay_boundary_from_completion
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
          server_sent /\
        clean16_staged_boundary_completion client server)
      (ensures
        PSNB.paired_supported_normalized_staged_replay_boundary client server)
=
  lemma_clean16_no_tail_valid_byte_traces_staged_boundary_derivation_milestones
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (clean16_staged_boundary_derivation_milestones client server);
  assert (PSNB.paired_supported_normalized_staged_replay_boundary client server)

let lemma_clean16_no_tail_valid_byte_traces_normalized_projection_boundary_from_completion
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
          server_sent /\
        clean16_projection_boundary_completion client server)
      (ensures
        PSNB.paired_supported_normalized_projection_boundary_core client server)
=
  lemma_clean16_no_tail_valid_byte_traces_staged_boundary_derivation_milestones
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (clean16_staged_boundary_derivation_milestones client server);
  assert (PSNB.paired_supported_normalized_projection_boundary_core client server)

let lemma_clean16_projection_boundary_completion_from_split_completions
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        clean16_projection_cleartext_boundary_completion client server /\
        clean16_protected_projection_witnesses_completion client server)
      (ensures clean16_projection_boundary_completion client server)
=
  assert (clean16_projection_boundary_completion client server)

let lemma_clean16_projection_cleartext_boundary_completion_from_key_shares_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires clean16_cleartext_key_shares_completion client server)
      (ensures clean16_projection_cleartext_boundary_completion client server)
=
  assert_norm
    (clean16_projection_cleartext_boundary_completion client server ==
     (clean16_staged_boundary_derivation_milestones client server ==>
      PSNB.paired_supported_normalized_projection_boundary_cleartext_core
        client
        server));
  let prove
    (_:clean16_staged_boundary_derivation_milestones client server)
    : Lemma
        (PSNB.paired_supported_normalized_projection_boundary_cleartext_core
          client
          server)
    =
    assert (WFL.paired_cleartext_hello_key_shares client server);
    eliminate exists
      client_start
      client_ch
      client_sh
      client_shared
      client_rest
      server_ch
      selection
      server_shared
      server_sh
      server_rest.
      PNTRB.role_local_cleartext_prefix_shape
        client
        server
        client_start
        client_ch
        client_sh
        client_shared
        client_rest
        server_ch
        selection
        server_shared
        server_sh
        server_rest /\
      WFL.supported_client_hello_wire_profile client_ch /\
      PNTRB.normalized_cleartext_raw_wire_bridge
        client_ch
        server_ch
        client_sh
        server_sh /\
      client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some client_ch /\
      client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        Some client_sh /\
      server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some server_ch /\
      server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        Some server_sh
    returns
      PSNB.paired_supported_normalized_projection_boundary_cleartext_core
        client
        server
    with _.
    (
      assert (exists
        (client_ch_raw:B.bytes)
        (server_ch_raw:B.bytes)
        (client_sh_raw:B.bytes)
        (server_sh_raw:B.bytes).
        FStar.Seq.equal client_ch_raw server_ch_raw /\
        FStar.Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw);
      eliminate exists
        (client_ch_raw:B.bytes)
        (server_ch_raw:B.bytes)
        (client_sh_raw:B.bytes)
        (server_sh_raw:B.bytes).
        FStar.Seq.equal client_ch_raw server_ch_raw /\
        FStar.Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw
      returns
        PSNB.paired_supported_normalized_projection_boundary_cleartext_core
          client
          server
      with _.
      (
        let w:PSNB.normalized_projection_boundary_witnesses = {
          PSNB.npb_client_ch = client_ch;
          PSNB.npb_server_ch = server_ch;
          PSNB.npb_client_sh = client_sh;
          PSNB.npb_server_sh = server_sh;
          PSNB.npb_client_ch_raw = client_ch_raw;
          PSNB.npb_server_ch_raw = server_ch_raw;
          PSNB.npb_client_sh_raw = client_sh_raw;
          PSNB.npb_server_sh_raw = server_sh_raw;
        } in
        assert (PSNB.paired_supported_normalized_projection_boundary_cleartext_core_inputs
          client
          server
          w);
        assert (PSNB.paired_supported_normalized_projection_boundary_cleartext_core
          client
          server)
      )
    ) in
  FStar.Classical.impl_intro
    #(clean16_staged_boundary_derivation_milestones client server)
    #(PSNB.paired_supported_normalized_projection_boundary_cleartext_core
        client
        server)
    prove

#push-options "--z3rlimit 30"
let lemma_clean16_cleartext_key_shares_completion_from_server_hello_key_shares_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires clean16_server_hello_key_shares_completion client server)
      (ensures clean16_cleartext_key_shares_completion client server)
=
  assert_norm
    (clean16_cleartext_key_shares_completion client server ==
     (clean16_staged_boundary_derivation_milestones client server ==>
      WFL.paired_cleartext_hello_key_shares client server));
  let prove
    (_:clean16_staged_boundary_derivation_milestones client server)
    : Lemma (WFL.paired_cleartext_hello_key_shares client server)
    =
    eliminate exists
      client_start
      client_ch
      client_sh
      client_shared
      client_rest
      server_ch
      selection
      server_shared
      server_sh
      server_rest.
      PNTRB.role_local_cleartext_prefix_shape
        client
        server
        client_start
        client_ch
        client_sh
        client_shared
        client_rest
        server_ch
        selection
        server_shared
        server_sh
        server_rest /\
      WFL.supported_client_hello_wire_profile client_ch /\
      PNTRB.normalized_cleartext_raw_wire_bridge
        client_ch
        server_ch
        client_sh
        server_sh /\
      client.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some client_ch /\
      client.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        Some client_sh /\
      server.CS.cs_model.CS.model_handshake.CS.hs_client_hello ==
        Some server_ch /\
      server.CS.cs_model.CS.model_handshake.CS.hs_server_hello ==
        Some server_sh
    returns WFL.paired_cleartext_hello_key_shares client server
    with _.
    (
      assert (PNTRB.normalized_cleartext_raw_wire_bridge
        client_ch
        server_ch
        client_sh
        server_sh);
      assert (exists
        (client_ch_raw:B.bytes)
        (server_ch_raw:B.bytes)
        (client_sh_raw:B.bytes)
        (server_sh_raw:B.bytes).
        FStar.Seq.equal client_ch_raw server_ch_raw /\
        FStar.Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw);
      eliminate exists
        (client_ch_raw:B.bytes)
        (server_ch_raw:B.bytes)
        (client_sh_raw:B.bytes)
        (server_sh_raw:B.bytes).
        FStar.Seq.equal client_ch_raw server_ch_raw /\
        FStar.Seq.equal server_sh_raw client_sh_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello client_ch))
          client_ch_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ClientHello server_ch))
          server_ch_raw /\
        CS.cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello server_sh))
          server_sh_raw /\
        CS.received_cleartext_tls_message_raw
          (M.TlsHandshake (M.ServerHello client_sh))
          client_sh_raw
      returns WFL.paired_cleartext_hello_key_shares client server
      with _.
      (
        assert (WFL.supported_client_hello_wire_profile client_ch);
        WFL.lemma_client_hello_wire_equivalent_from_sent_cleartext_and_received_parse
          client_ch
          server_ch
          client_ch_raw
          server_ch_raw;
        WFL.lemma_paired_cleartext_hello_key_shares_from_cleartext_raw_and_supported_server_hello_parse
          client
          server
          client_ch
          server_ch
          client_sh
          server_sh
          client_ch_raw
          server_ch_raw
          client_sh_raw
          server_sh_raw;
        assert (WFL.paired_cleartext_hello_key_shares client server)
      )
    ) in
  FStar.Classical.impl_intro
    #(clean16_staged_boundary_derivation_milestones client server)
    #(WFL.paired_cleartext_hello_key_shares client server)
    prove
#pop-options

let lemma_clean16_protected_projection_witnesses_completion_from_installed_replay_completion
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        clean16_installed_protected_projection_replay_completion
          client
          server)
      (ensures
        clean16_protected_projection_witnesses_completion
          client
          server)
=
  assert_norm
    (clean16_protected_projection_witnesses_completion client server ==
     (clean16_staged_boundary_derivation_milestones client server ==>
      Pairing.paired_protected_handshake_event_projection_pair_witnesses
        client
        server));
  let prove
    (_:clean16_staged_boundary_derivation_milestones client server)
    : Lemma
        (Pairing.paired_protected_handshake_event_projection_pair_witnesses
          client
          server)
    =
    assert (PNTPPD.installed_protected_projection_replay_witnesses
      client
      server);
    PNTPPD.lemma_pairing_protected_projection_witnesses_from_installed_replay_witnesses
      client
      server in
  FStar.Classical.impl_intro
    #(clean16_staged_boundary_derivation_milestones client server)
    #(Pairing.paired_protected_handshake_event_projection_pair_witnesses
        client
        server)
    prove

let lemma_clean16_projection_boundary_completion_from_cleartext_and_installed_replay_completions
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        clean16_projection_cleartext_boundary_completion
          client
          server /\
        clean16_installed_protected_projection_replay_completion
          client
          server)
      (ensures
        clean16_projection_boundary_completion
          client
          server)
=
  lemma_clean16_protected_projection_witnesses_completion_from_installed_replay_completion
    client
    server;
  lemma_clean16_projection_boundary_completion_from_split_completions
    client
    server

let lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_projection_boundary_completion
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
          server_sent /\
        clean16_projection_boundary_completion client server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_clean16_no_tail_valid_byte_traces_normalized_projection_boundary_from_completion
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PSNB.lemma_client_server_application_record_material_agrees_from_normalized_projection_boundary_core
    client
    server

let lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_staged_boundary_completion
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
          server_sent /\
        clean16_staged_boundary_completion client server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)
=
  lemma_clean16_no_tail_valid_byte_traces_normalized_staged_replay_boundary_from_completion
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PSNB.lemma_client_server_application_record_material_agrees_from_normalized_staged_replay_boundary
    client
    server

#pop-options

#push-options "--split_queries always --z3rlimit 60"

let step_next (m:CS.connection_model) (ev:CS.conn_event) : GTot CS.connection_model =
  match CS.step_model m ev with
  | Some m' -> m'
  | None -> m
#pop-options

// ===================================================================
// Transplanted, probe-validated helper lemmas for the pack_inputs proof
// ===================================================================

#push-options "--z3rlimit 20"
let peel_sent
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (final:CS.connection_model)
  : Lemma
      (requires (exists rs rr. CS.conn_events_sent_seal_replay model (ev :: rest) rs rr final))
      (ensures
        CS.legal_event model ev /\
        CS.step_model model ev == Some (step_next model ev) /\
        (exists ts tr. CS.conn_events_sent_seal_replay (step_next model ev) rest ts tr final))
=
  eliminate exists rs rr. CS.conn_events_sent_seal_replay model (ev :: rest) rs rr final
  returns
    (CS.legal_event model ev /\ CS.step_model model ev == Some (step_next model ev) /\
     (exists ts tr. CS.conn_events_sent_seal_replay (step_next model ev) rest ts tr final))
  with _. (
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    CS.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
  returns
    (CS.legal_event model ev /\ CS.step_model model ev == Some (step_next model ev) /\
     (exists ts tr. CS.conn_events_sent_seal_replay (step_next model ev) rest ts tr final))
  with _.
  ( introduce exists ts tr. CS.conn_events_sent_seal_replay (step_next model ev) rest ts tr final
    with tail_sent tail_received and () ) )

let peel_received
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (final:CS.connection_model)
  : Lemma
      (requires (exists rs rr. CS.conn_events_received_decode_replay model (ev :: rest) rs rr final))
      (ensures
        CS.legal_event model ev /\
        CS.step_model model ev == Some (step_next model ev) /\
        (exists ts tr. CS.conn_events_received_decode_replay (step_next model ev) rest ts tr final))
=
  eliminate exists rs rr. CS.conn_events_received_decode_replay model (ev :: rest) rs rr final
  returns
    (CS.legal_event model ev /\ CS.step_model model ev == Some (step_next model ev) /\
     (exists ts tr. CS.conn_events_received_decode_replay (step_next model ev) rest ts tr final))
  with _. (
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    CS.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  returns
    (CS.legal_event model ev /\ CS.step_model model ev == Some (step_next model ev) /\
     (exists ts tr. CS.conn_events_received_decode_replay (step_next model ev) rest ts tr final))
  with _.
  ( introduce exists ts tr. CS.conn_events_received_decode_replay (step_next model ev) rest ts tr final
    with tail_sent tail_received and () ) )

let peel_nil_sent (model final:CS.connection_model)
  : Lemma
      (requires (exists rs rr. CS.conn_events_sent_seal_replay model [] rs rr final))
      (ensures model == final)
=
  eliminate exists rs rr. CS.conn_events_sent_seal_replay model [] rs rr final
  returns (model == final)
  with _. ( assert (CS.conn_events_sent_seal_replay model [] rs rr final) )

let peel_nil_received (model final:CS.connection_model)
  : Lemma
      (requires (exists rs rr. CS.conn_events_received_decode_replay model [] rs rr final))
      (ensures model == final)
=
  eliminate exists rs rr. CS.conn_events_received_decode_replay model [] rs rr final
  returns (model == final)
  with _. ( assert (CS.conn_events_received_decode_replay model [] rs rr final) )
#pop-options

// Linchpin (A): transcript equality of server model5 and client model4
#push-options "--z3rlimit 40 --split_queries always"
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
= ()

// Linchpin (B): handshake secret equality of server model5 and client model4
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
= FStar.Seq.lemma_eq_elim server_shared client_shared
#pop-options

// Linchpin (C): server-flight handshake write/read alignment via RA + forward push
#push-options "--z3rlimit 30 --split_queries always"
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
#push-options "--z3rlimit 30 --split_queries always"
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
#push-options "--z3rlimit 30 --split_queries always"
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
  returns goal
  with _. (
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases e13;
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases e14)
  and _. (
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases e13;
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases e14)
#pop-options

// ================= SERVER FLIGHT WALK =================
#push-options "--z3rlimit 60 --split_queries always --fuel 2 --ifuel 2"
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
         exists rs rr. CS.conn_events_sent_seal_replay m0 rest rs rr final))
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
  peel_sent s1 ev_sign_cv [ev_cv; ev_sf; ev_iaw; ev_rcf; ev_iar; ev_vcf] final;
  let sauth = step_next s1 ev_sign_cv in
  assert (sauth.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  peel_sent sauth ev_cv [ev_sf; ev_iaw; ev_rcf; ev_iar; ev_vcf] final;
  let s2 = step_next sauth ev_cv in
  assert (s2.CS.model_control == CS.ControlHandshaking CS.HsServerEncryptedFlightSent);
  assert (s2.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  peel_sent s2 ev_sf [ev_iaw; ev_rcf; ev_iar; ev_vcf] final;
  let s3 = step_next s2 ev_sf in
  assert (s3.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent);
  assert (s3.CS.model_handshake.CS.hs_server_finished == Some sf);
  peel_sent s3 ev_iaw [ev_rcf; ev_iar; ev_vcf] final;
  let s4 = step_next s3 ev_iaw in
  assert (s4.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedSent);
  peel_sent s4 ev_rcf [ev_iar; ev_vcf] final;
  let s5 = step_next s4 ev_rcf in
  assert (s5.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived);
  assert (s5.CS.model_handshake.CS.hs_client_finished == Some cf);
  peel_sent s5 ev_iar [ev_vcf] final;
  let s6 = step_next s5 ev_iar in
  assert (s6.CS.model_control == CS.ControlHandshaking CS.HsClientFinishedReceived);
  peel_sent s6 ev_vcf [] final;
  let s7 = step_next s6 ev_vcf in
  peel_nil_sent s7 final;
  assert (final == s7)
#pop-options

// ================= CLIENT FLIGHT WALK =================
#push-options "--z3rlimit 80 --split_queries always --fuel 2 --ifuel 2"
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
         exists rs rr. CS.conn_events_received_decode_replay m0 rest rs rr final))
      (ensures
        (let ev_ee = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
         let ev_cert = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
         let ev_val = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
         let ev_cv = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
         let ev_vc = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
         let ev_sf = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); } in
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
         c0.CS.model_record.CS.record_read == R.next_seq m0.CS.model_record.CS.record_read /\
         c1.CS.model_record.CS.record_read == R.next_seq c0.CS.model_record.CS.record_read /\
         c2.CS.model_record.CS.record_read == R.next_seq cauth.CS.model_record.CS.record_read /\
         c3.CS.model_record.CS.record_read == R.next_seq cvfy.CS.model_record.CS.record_read /\
         final.CS.model_handshake.CS.hs_encrypted_extensions == Some ee /\
         final.CS.model_handshake.CS.hs_certificate == Some cert /\
         final.CS.model_handshake.CS.hs_certificate_verify == Some cv /\
         final.CS.model_handshake.CS.hs_server_finished == Some sf /\
         final.CS.model_handshake.CS.hs_client_finished == Some cf /\
         final.CS.model_control == CS.ControlApplicationData))
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
  peel_received c1 ev_val [ev_cv; ev_vc; ev_sf; ev_vf; e13; e14; ev_cf] final;
  let cauth = step_next c1 ev_val in
  assert (cauth.CS.model_control == CS.ControlHandshaking CS.HsCertificateValidated);
  peel_received cauth ev_cv [ev_vc; ev_sf; ev_vf; e13; e14; ev_cf] final;
  let c2 = step_next cauth ev_cv in
  assert (c2.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyReceived);
  assert (c2.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  peel_received c2 ev_vc [ev_sf; ev_vf; e13; e14; ev_cf] final;
  let cvfy = step_next c2 ev_vc in
  assert (cvfy.CS.model_control == CS.ControlHandshaking CS.HsCertificateVerifyVerified);
  assert (cvfy.CS.model_handshake.CS.hs_certificate_verify == Some cv);
  peel_received cvfy ev_sf [ev_vf; e13; e14; ev_cf] final;
  let c3 = step_next cvfy ev_sf in
  assert (c3.CS.model_control == CS.ControlHandshaking CS.HsServerFinishedReceived);
  assert (c3.CS.model_handshake.CS.hs_server_finished == Some sf);
  peel_received c3 ev_vf [e13; e14; ev_cf] final;
  let c4 = step_next c3 ev_vf in
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
  peel_received c6 ev_cf [] final;
  let c7 = step_next c6 ev_cf in
  peel_nil_received c7 final;
  assert (c7.CS.model_handshake.CS.hs_client_finished == Some cf);
  assert (c7.CS.model_control == CS.ControlApplicationData)
#pop-options

#push-options "--z3rlimit 40 --split_queries always --fuel 3 --ifuel 3"
let lemma_sent_finished_at_appdata_sets_client_finished (m m':CS.connection_model) (fin:GFin.finished)
  : Lemma
      (requires
        CS.step_model m (CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished fin); }) == Some m' /\
        m'.CS.model_control == CS.ControlApplicationData)
      (ensures m'.CS.model_handshake.CS.hs_client_finished == Some fin)
= ()

let lemma_verify_client_finished_sets_client_finished (m m':CS.connection_model) (fin:GFin.finished)
  : Lemma
      (requires
        CS.step_model m (CS.ConnLocalEvent (CS.LocalVerifyClientFinished fin)) == Some m')
      (ensures m'.CS.model_handshake.CS.hs_client_finished == Some fin)
= ()
#pop-options


// ================= CFRR SUFFIX WALK (server receiving client finished) =================
#push-options "--z3rlimit 60 --split_queries always --fuel 2 --ifuel 2"
let lemma_cfrr_suffix_walk
  (m0:CS.connection_model) (appw appr:CS.traffic_key_material) (cf:GFin.finished) (final:CS.connection_model)
  : Lemma
      (requires
        (let ev_iaw = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = appw; }; }) in
         let ev_rcf = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); } in
         let ev_iar = CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole { CS.install_role = CS.ServerEndpoint; CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = appr; }; }) in
         let ev_vcf = CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf) in
         exists rs rr. CS.conn_events_received_decode_replay m0 [ev_iaw; ev_rcf; ev_iar; ev_vcf] rs rr final))
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
#push-options "--z3rlimit 20 --split_queries always --fuel 1 --ifuel 1"
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
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
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

#push-options "--z3rlimit 20 --split_queries always"
let rec lemma_sent_replay_preserves_shared_secret
  (m0:CS.connection_model) (evs:list CS.conn_event) (final:CS.connection_model)
  : Lemma
      (requires
        (exists rs rr. CS.conn_events_sent_seal_replay m0 evs rs rr final) /\
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

let rec lemma_received_replay_preserves_shared_secret
  (m0:CS.connection_model) (evs:list CS.conn_event) (final:CS.connection_model)
  : Lemma
      (requires
        (exists rs rr. CS.conn_events_received_decode_replay m0 evs rs rr final) /\
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
let event_not_hello (ev:CS.conn_event) : bool =
  match ev with
  | CS.ConnNetworkEvent { CL.message_value = M.TlsHandshake (M.ClientHello _) } -> false
  | CS.ConnNetworkEvent { CL.message_value = M.TlsHandshake (M.ServerHello _) } -> false
  | CS.ConnLocalEvent (CS.LocalSelectServerParameters _) -> false
  | _ -> true

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1 --split_queries always"
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

let rec all_not_hello (evs:list CS.conn_event) : bool =
  match evs with
  | [] -> true
  | ev :: rest -> event_not_hello ev && all_not_hello rest

#push-options "--z3rlimit 20 --split_queries always"
let rec lemma_sent_replay_preserves_slots
  (m0:CS.connection_model) (evs:list CS.conn_event) (final:CS.connection_model)
  : Lemma
      (requires
        (exists rs rr. CS.conn_events_sent_seal_replay m0 evs rs rr final) /\
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

let rec lemma_received_replay_preserves_slots
  (m0:CS.connection_model) (evs:list CS.conn_event) (final:CS.connection_model)
  : Lemma
      (requires
        (exists rs rr. CS.conn_events_received_decode_replay m0 evs rs rr final) /\
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
#push-options "--z3rlimit 60 --split_queries always --fuel 2 --ifuel 2"
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
          CS.conn_events_sent_seal_replay m0
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
#push-options "--z3rlimit 60 --split_queries always --fuel 2 --ifuel 2"
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
          CS.conn_events_received_decode_replay m0
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
#push-options "--z3rlimit 40 --split_queries always"
let lemma_server_final_slots
  (server:CS.connection_state)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (model5:CS.connection_model) (suffix:list CS.conn_event)
  : Lemma
      (requires
        (exists rs rr. CS.conn_events_sent_seal_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
           rs rr model5) /\
        (exists rs rr. CS.conn_events_sent_seal_replay model5 suffix rs rr server.CS.cs_model) /\
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

let lemma_client_final_slots
  (client:CS.connection_state)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (model4:CS.connection_model) (suffix:list CS.conn_event)
  : Lemma
      (requires
        (exists rs rr. CS.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
           rs rr model4) /\
        (exists rs rr. CS.conn_events_received_decode_replay model4 suffix rs rr client.CS.cs_model) /\
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
#push-options "--z3rlimit 30 --split_queries always"
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
        (exists rs rr. CS.conn_events_sent_seal_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch_s selection_s server_shared_s sh_s)
           rs rr model5_s) /\
        (exists rs rr. CS.conn_events_sent_seal_replay model5_s server_suffix rs rr server.CS.cs_model) /\
        all_not_hello server_suffix /\
        (exists rs rr. CS.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
           rs rr model4_c) /\
        (exists rs rr. CS.conn_events_received_decode_replay model4_c client_suffix rs rr client.CS.cs_model) /\
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
#push-options "--z3rlimit 30 --split_queries always"
let lemma_checkpoint_th_sh_from_milestone
  (client server:CS.connection_state)
  : Lemma
      (requires clean16_cleartext_final_hello_slot_milestone client server)
      (ensures
        CS.same_transcript_checkpoint CS.TH_CH client server /\
        CS.same_transcript_checkpoint CS.TH_SH client server)
=
  eliminate exists client_start client_ch client_sh client_shared client_rest
                   server_ch selection server_shared server_sh server_rest.
    PNTRB.role_local_cleartext_prefix_shape client server
      client_start client_ch client_sh client_shared client_rest
      server_ch selection server_shared server_sh server_rest /\
    WFL.supported_client_hello_wire_profile client_ch /\
    PNTRB.normalized_cleartext_raw_wire_bridge client_ch server_ch client_sh server_sh /\
    client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
    client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
    server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
    server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh
  returns
    (CS.same_transcript_checkpoint CS.TH_CH client server /\
     CS.same_transcript_checkpoint CS.TH_SH client server)
  with _. (
    eliminate exists (client_ch_raw server_ch_raw client_sh_raw server_sh_raw:B.bytes).
      Seq.equal client_ch_raw server_ch_raw /\
      Seq.equal server_sh_raw client_sh_raw /\
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) client_ch_raw /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) server_ch_raw /\
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) server_sh_raw /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) client_sh_raw
    returns
      (CS.same_transcript_checkpoint CS.TH_CH client server /\
       CS.same_transcript_checkpoint CS.TH_SH client server)
    with _. (
      WFL.lemma_paired_cleartext_hello_handshake_checkpoint_from_cleartext_raw
        client server client_ch server_ch client_sh server_sh
        client_ch_raw server_ch_raw client_sh_raw server_sh_raw
    )
  )
#pop-options

// H: server prefix -> handshake_secret and transcript of model5
#push-options "--z3rlimit 60 --split_queries always --fuel 2 --ifuel 2"
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
          CS.conn_events_sent_seal_replay m0
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
#push-options "--z3rlimit 60 --split_queries always --fuel 2 --ifuel 2"
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
          CS.conn_events_received_decode_replay m0
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
  peel_received m1 e1 [e2;e3] model4;
  let m2 = step_next m1 e1 in
  peel_received m2 e2 [e3] model4;
  let m3 = step_next m2 e2 in
  assert (Seq.equal m3.CS.model_handshake.CS.hs_transcript
            (B.append (W.serialize_handshake (M.ClientHello ch))
                      (W.serialize_handshake (M.ServerHello sh))));
  peel_received m3 e3 [] model4;
  let m4 = step_next m3 e3 in
  peel_nil_received m4 model4
#pop-options

// H: transcript equality of model5_s / model4_c from checkpoint + prefix transcripts + slots
#push-options "--z3rlimit 30 --split_queries always"
let lemma_transcript_eq_from_checkpoint
  (client server:CS.connection_state)
  (model5_s model4_c:CS.connection_model)
  (ch_s:GCH.clientHello) (sh_s:GSH.serverHello)
  (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  : Lemma
      (requires
        CS.same_transcript_checkpoint CS.TH_SH client server /\
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
  assert (CS.transcript_checkpoint_bytes CS.TH_SH server.CS.cs_model.CS.model_handshake ==
          Some (B.append (W.serialize_handshake (M.ClientHello ch_s))
                         (W.serialize_handshake (M.ServerHello sh_s))));
  assert (CS.transcript_checkpoint_bytes CS.TH_SH client.CS.cs_model.CS.model_handshake ==
          Some (B.append (W.serialize_handshake (M.ClientHello ch_c))
                         (W.serialize_handshake (M.ServerHello sh_c))))
#pop-options

// H: normalize a client handshake READ install (plain or ForRole) to a plain install
//    with traffic_install_matches
#push-options "--z3rlimit 30 --split_queries always --ifuel 2"
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
#push-options "--z3rlimit 30 --ifuel 2 --fuel 1"
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
#push-options "--z3rlimit 20"
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
#push-options "--z3rlimit 30 --ifuel 2 --split_queries always"
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
  returns event_not_hello e4 /\ event_not_hello e5
  with _.
    (PCPS.lemma_client_no_tail_handshake_write_install_event_cases e4;
     PCPS.lemma_client_no_tail_handshake_read_install_event_cases e5)
  and _.
    (PCPS.lemma_client_no_tail_handshake_read_install_event_cases e4;
     PCPS.lemma_client_no_tail_handshake_write_install_event_cases e5)

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
  returns event_not_hello e13 /\ event_not_hello e14
  with _.
    (PNTCAS.lemma_client_no_tail_application_write_install_event_cases e13;
     PNTCAS.lemma_client_no_tail_application_read_install_event_cases e14)
  and _.
    (PNTCAS.lemma_client_no_tail_application_read_install_event_cases e13;
     PNTCAS.lemma_client_no_tail_application_write_install_event_cases e14)
#pop-options

// K: full client-suffix all_not_hello (abstract installs handled via covers)
#push-options "--z3rlimit 30 --fuel 16 --ifuel 2 --split_queries always"
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

// ===== HOLE 1: server-handshake-write / client-handshake-read alignment =====
#push-options "--z3rlimit 30 --ifuel 2 --split_queries always"
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
  returns PWL.write_read_record_material_aligned server_after_read_s client_after_installs_c
  with _.
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
    returns PWL.write_read_record_material_aligned server_after_read_s client_after_installs_c
    with _.
    (
      RA.lemma_server_handshake_write_client_handshake_read_install_aligned_from_key_schedule
        model5_s client_after_e4_c server_material_s mat_r server_after_write_s client_after_installs_c;
      RA.lemma_step_sender_local_event_preserves_write_read_record_material_alignment
        server_after_write_s server_read_install_le server_after_read_s client_after_installs_c
    )
  )
  and _.
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
    returns PWL.write_read_record_material_aligned server_after_read_s client_after_installs_c
    with _.
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
#push-options "--z3rlimit 30 --fuel 16 --ifuel 2 --split_queries always"
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
#push-options "--z3rlimit 30 --fuel 16 --ifuel 2 --split_queries always"
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
        (exists rs rr. CS.conn_events_sent_seal_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch_s selection_s server_shared_s sh_s)
           rs rr model5_s) /\
        // server suffix replay + steps + legal
        (exists rs rr. CS.conn_events_sent_seal_replay model5_s
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
        (exists rs rr. CS.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
           rs rr model4_c) /\
        // client suffix replay + covers + steps + legal
        (exists rs rr. CS.conn_events_received_decode_replay model4_c
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
#push-options "--z3rlimit 20"
let peel_sent_empty_dsent
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        (CS.ConnLocalEvent? ev \/
         (CS.ConnNetworkEvent? ev /\
          (CS.ConnNetworkEvent?._0 ev).CL.message_direction == CL.Received)) /\
        CS.conn_events_sent_seal_replay model (ev :: rest) rs rr final)
      (ensures
        CS.step_model model ev == Some (step_next model ev) /\
        (exists (tr:B.bytes).
          CS.conn_events_sent_seal_replay (step_next model ev) rest rs tr final))
=
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    CS.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
  returns
    (CS.step_model model ev == Some (step_next model ev) /\
     (exists (tr:B.bytes).
       CS.conn_events_sent_seal_replay (step_next model ev) rest rs tr final))
  with _.
  (
    assert (Seq.equal delta_sent B.empty);
    Seq.append_empty_l tail_sent;
    assert (Seq.equal rs tail_sent);
    Seq.lemma_eq_elim rs tail_sent;
    assert (step_next model ev == model1);
    introduce exists (tr:B.bytes).
      CS.conn_events_sent_seal_replay (step_next model ev) rest rs tr final
    with tail_received
    and ()
  )
#pop-options

// The single Sent ServerHello event: raw_sent == serialize(ServerHello sh)
#push-options "--z3rlimit 20"
let peel_sent_server_hello_bytes
  (model:CS.connection_model) (sh:GSH.serverHello)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay model
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
    CS.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_sent_seal_replay model1 [] tail_sent tail_received final
  returns
    (Seq.equal rs (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
  with _.
  (
    assert (Seq.equal tail_sent B.empty);
    Seq.append_empty_r delta_sent;
    assert (Seq.equal rs delta_sent);
    assert (Seq.equal delta_sent (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))));
    Seq.lemma_eq_elim rs (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh)))
  )
#pop-options

// ---- received-decode side ----
#push-options "--z3rlimit 20"
let peel_received_empty_drecv
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        (CS.ConnLocalEvent? ev \/
         (CS.ConnNetworkEvent? ev /\
          (CS.ConnNetworkEvent?._0 ev).CL.message_direction == CL.Sent)) /\
        CS.conn_events_received_decode_replay model (ev :: rest) rs rr final)
      (ensures
        CS.step_model model ev == Some (step_next model ev) /\
        (exists (ts:B.bytes).
          CS.conn_events_received_decode_replay (step_next model ev) rest ts rr final))
=
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    CS.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  returns
    (CS.step_model model ev == Some (step_next model ev) /\
     (exists (ts:B.bytes).
       CS.conn_events_received_decode_replay (step_next model ev) rest ts rr final))
  with _.
  (
    assert (Seq.equal delta_received B.empty);
    Seq.append_empty_l tail_received;
    assert (Seq.equal rr tail_received);
    Seq.lemma_eq_elim rr tail_received;
    assert (step_next model ev == model1);
    introduce exists (ts:B.bytes).
      CS.conn_events_received_decode_replay (step_next model ev) rest ts rr final
    with tail_sent
    and ()
  )
#pop-options

// A single local event: received-decode replay => raw_received empty
#push-options "--z3rlimit 20"
let received_local_singleton_rr_empty
  (model:CS.connection_model) (lev:CS.local_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay model [CS.ConnLocalEvent lev] rs rr final)
      (ensures Seq.equal rr B.empty)
=
  let ev = CS.ConnLocalEvent lev in
  PWReplay.lemma_conn_events_received_decode_replay_head model ev [] rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    CS.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_received_decode_replay model1 [] tail_sent tail_received final
  returns (Seq.equal rr B.empty)
  with _.
  (
    assert (Seq.equal delta_received B.empty);
    assert (Seq.equal tail_received B.empty);
    Seq.append_empty_l tail_received;
    assert (Seq.equal rr tail_received)
  )
#pop-options

// The RecvSH followed by a single local event: raw_received == serialize(ServerHello sh)
#push-options "--z3rlimit 20"
let peel_received_server_hello_then_local_bytes
  (model:CS.connection_model) (sh:GSH.serverHello) (lev:CS.local_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay model
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
    CS.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  returns
    (Seq.equal rr (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
  with _.
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
#push-options "--z3rlimit 30"
let lemma_server_prefix_sent_bytes
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (sel:CS.server_handshake_selection)
  (shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (ps pr:B.bytes) (m5:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay m0
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
  eliminate exists (tr1:B.bytes). CS.conn_events_sent_seal_replay m1 [e1;e2;e3;e4] ps tr1 m5
  returns (Seq.equal ps (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
  with _. (
    peel_sent_empty_dsent m1 e1 [e2;e3;e4] ps tr1 m5;
    let m2 = step_next m1 e1 in
    eliminate exists (tr2:B.bytes). CS.conn_events_sent_seal_replay m2 [e2;e3;e4] ps tr2 m5
    returns (Seq.equal ps (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
    with _. (
      peel_sent_empty_dsent m2 e2 [e3;e4] ps tr2 m5;
      let m3 = step_next m2 e2 in
      eliminate exists (tr3:B.bytes). CS.conn_events_sent_seal_replay m3 [e3;e4] ps tr3 m5
      returns (Seq.equal ps (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
      with _. (
        peel_sent_empty_dsent m3 e3 [e4] ps tr3 m5;
        let m4 = step_next m3 e3 in
        eliminate exists (tr4:B.bytes). CS.conn_events_sent_seal_replay m4 [e4] ps tr4 m5
        returns (Seq.equal ps (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
        with _. (
          peel_sent_server_hello_bytes m4 sh ps tr4 m5
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 30"
let lemma_client_prefix_received_bytes
  (m0:CS.connection_model)
  (start:CS.handshake_start) (ch:GCH.clientHello)
  (sh:GSH.serverHello) (shared:C.x25519_shared_secret)
  (ps pr:B.bytes) (m4:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay m0
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
  eliminate exists (ts1:B.bytes). CS.conn_events_received_decode_replay m1 [f1;f2;f3] ts1 pr m4
  returns (Seq.equal pr (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
  with _. (
    peel_received_empty_drecv m1 f1 [f2;f3] ts1 pr m4;
    let m2 = step_next m1 f1 in
    eliminate exists (ts2:B.bytes). CS.conn_events_received_decode_replay m2 [f2;f3] ts2 pr m4
    returns (Seq.equal pr (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh))))
    with _. (
      peel_received_server_hello_then_local_bytes m2 sh (CS.LocalDeriveSharedSecret shared) ts2 pr m4
    )
  )
#pop-options

// Byte-PRESERVING peel of a local (empty-delta) event from a sent-seal replay.
#push-options "--z3rlimit 20"
let peel_sent_bp
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.ConnLocalEvent? ev /\
        CS.conn_events_sent_seal_replay model (ev :: rest) rs rr final)
      (ensures
        CS.legal_event model ev /\
        CS.step_model model ev == Some (step_next model ev) /\
        CS.conn_events_sent_seal_replay (step_next model ev) rest rs rr final)
=
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    CS.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
  returns
    (CS.legal_event model ev /\
     CS.step_model model ev == Some (step_next model ev) /\
     CS.conn_events_sent_seal_replay (step_next model ev) rest rs rr final)
  with _.
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

#push-options "--z3rlimit 20"
let peel_received_bp
  (model:CS.connection_model) (ev:CS.conn_event) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.ConnLocalEvent? ev /\
        CS.conn_events_received_decode_replay model (ev :: rest) rs rr final)
      (ensures
        CS.legal_event model ev /\
        CS.step_model model ev == Some (step_next model ev) /\
        CS.conn_events_received_decode_replay (step_next model ev) rest rs rr final)
=
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    CS.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  returns
    (CS.legal_event model ev /\
     CS.step_model model ev == Some (step_next model ev) /\
     CS.conn_events_received_decode_replay (step_next model ev) rest rs rr final)
  with _.
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
#push-options "--z3rlimit 30 --split_queries always"
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
    PNTRB.normalized_cleartext_raw_wire_bridge client_ch server_ch client_sh server_sh /\
    client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
    client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
    server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
    server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh
  returns
    (Seq.equal
      (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_s)))
      (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_c))))
  with _. (
    assert (server_sh == sh_s);
    assert (client_sh == sh_c);
    eliminate exists (client_ch_raw server_ch_raw client_sh_raw server_sh_raw:B.bytes).
      Seq.equal client_ch_raw server_ch_raw /\
      Seq.equal server_sh_raw client_sh_raw /\
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello client_ch)) client_ch_raw /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello server_ch)) server_ch_raw /\
      CS.cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello server_sh)) server_sh_raw /\
      CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ServerHello client_sh)) client_sh_raw
    returns
      (Seq.equal
        (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_s)))
        (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ServerHello sh_c))))
    with _. (
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
#push-options "--z3rlimit 20"
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
#push-options "--z3rlimit 20 --ifuel 2"
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
  returns (CS.ConnLocalEvent? e4 /\ CS.ConnLocalEvent? e5)
  with _. (
    PCPS.lemma_client_no_tail_handshake_write_install_event_cases e4;
    PCPS.lemma_client_no_tail_handshake_read_install_event_cases e5
  )
  and _. (
    PCPS.lemma_client_no_tail_handshake_read_install_event_cases e4;
    PCPS.lemma_client_no_tail_handshake_write_install_event_cases e5
  )
#pop-options


// ===== HOLE 2 bundled: server-sent / client-received suffix byte equality =====
#push-options "--z3rlimit 30 --split_queries always"
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
        CS.paired_wire_logs client server /\
        // server prefix concrete sent replay
        CS.conn_events_sent_seal_replay
          (CS.initial_model server.CS.cs_model.CS.model_config)
          (PWSeg.server_cleartext_handshake_prefix_events ch_s selection_s server_shared_s sh_s)
          prefix_sent_s prefix_received_s model5_s /\
        // server suffix replay (existential) reaching final
        (exists rs rr. CS.conn_events_sent_seal_replay model5_s
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
        CS.conn_events_received_decode_replay
          (CS.initial_model client.CS.cs_model.CS.model_config)
          (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
          prefix_sent_c prefix_received_c model4_c /\
        // client suffix replay (existential) reaching final
        (exists rs rr. CS.conn_events_received_decode_replay model4_c
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

#push-options "--z3rlimit 20"
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

#push-options "--z3rlimit 30 --split_queries always"
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

#push-options "--z3rlimit 30 --split_queries always"
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

#push-options "--z3rlimit 20 --ifuel 1"
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

#push-options "--z3rlimit 20 --ifuel 1"
let lemma_received_client_hello_is_wire_h4 (ch:GCH.clientHello) (raw:B.bytes)
  : Lemma
      (requires CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) raw)
      (ensures exists frag. W.parse_record_wire raw == Some (T.Handshake, frag, B.length raw))
= ()
#pop-options

#push-options "--z3rlimit 20"
let peel_sent_cleartext_ch_head
  (model:CS.connection_model) (ch:GCH.clientHello) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay model
          (CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) :: rest) rs rr final)
      (ensures
        (let ev = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
         CS.step_model model ev == Some (step_next model ev) /\
         (exists (ts tr:B.bytes).
            Seq.equal rs (B.append (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))) ts) /\
            CS.conn_events_sent_seal_replay (step_next model ev) rest ts tr final)))
=
  let ev = CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
  PWReplay.lemma_conn_events_sent_seal_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    CS.sent_event_nonempty_seal_projection model ev delta_sent /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_sent_seal_replay model1 rest tail_sent tail_received final
  returns
    (CS.step_model model ev == Some (step_next model ev) /\
     (exists (ts tr:B.bytes).
        Seq.equal rs (B.append (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))) ts) /\
        CS.conn_events_sent_seal_replay (step_next model ev) rest ts tr final))
  with _.
  (
    assert (Seq.equal delta_sent (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))));
    assert (step_next model ev == model1);
    introduce exists (ts tr:B.bytes).
        Seq.equal rs (B.append (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))) ts) /\
        CS.conn_events_sent_seal_replay (step_next model ev) rest ts tr final
    with tail_sent tail_received
    and (
      Seq.lemma_eq_elim rs (B.append (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello ch))) tail_sent)
    )
  )
#pop-options

#push-options "--z3rlimit 20"
let peel_received_ch_recv_head
  (model:CS.connection_model) (ch:GCH.clientHello) (rest:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay model
          (CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) :: rest) rs rr final)
      (ensures
        (let ev = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
         CS.step_model model ev == Some (step_next model ev) /\
         (exists (ds ts tr:B.bytes).
            Seq.equal rr (B.append ds tr) /\
            CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) ds /\
            CS.conn_events_received_decode_replay (step_next model ev) rest ts tr final)))
=
  let ev = CS.ConnNetworkEvent ({ CL.message_direction = CL.Received;
             CL.message_value = M.TlsHandshake (M.ClientHello ch); }) in
  PWReplay.lemma_conn_events_received_decode_replay_head model ev rest rs rr final;
  eliminate exists (model1:CS.connection_model) (delta_sent delta_received tail_sent tail_received:B.bytes).
    CS.legal_event model ev /\ CS.step_model model ev == Some model1 /\
    CS.event_raw_delta_legal model ev delta_sent delta_received /\
    CS.received_event_nonempty_decode_projection model ev delta_received /\
    Seq.equal rs (B.append delta_sent tail_sent) /\
    Seq.equal rr (B.append delta_received tail_received) /\
    CS.conn_events_received_decode_replay model1 rest tail_sent tail_received final
  returns
    (CS.step_model model ev == Some (step_next model ev) /\
     (exists (ds ts tr:B.bytes).
        Seq.equal rr (B.append ds tr) /\
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) ds /\
        CS.conn_events_received_decode_replay (step_next model ev) rest ts tr final))
  with _.
  (
    assert (CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) delta_received);
    assert (step_next model ev == model1);
    introduce exists (ds ts tr:B.bytes).
        Seq.equal rr (B.append ds tr) /\
        CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) ds /\
        CS.conn_events_received_decode_replay (step_next model ev) rest ts tr final
    with delta_received tail_sent tail_received
    and ()
  )
#pop-options

#push-options "--z3rlimit 20 --ifuel 2"
let lemma_two_server_install_events_are_local
  (e5 e6:CS.conn_event)
  : Lemma
      (requires PNTSS.server_no_tail_two_handshake_install_cover e5 e6)
      (ensures CS.ConnLocalEvent? e5 /\ CS.ConnLocalEvent? e6)
=
  PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e5 e6
#pop-options

let is_empty_sent_ev (ev:CS.conn_event) : bool =
  CS.ConnLocalEvent? ev ||
  (CS.ConnNetworkEvent? ev &&
   (CS.ConnNetworkEvent?._0 ev).CL.message_direction = CL.Received)

let is_empty_recv_ev (ev:CS.conn_event) : bool =
  CS.ConnLocalEvent? ev ||
  (CS.ConnNetworkEvent? ev &&
   (CS.ConnNetworkEvent?._0 ev).CL.message_direction = CL.Sent)

#push-options "--z3rlimit 20 --ifuel 1"
let rec lemma_empty_sent_tail_collapses
  (model:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay model evs rs rr final /\
        FStar.List.Tot.for_all is_empty_sent_ev evs)
      (ensures Seq.equal rs B.empty)
      (decreases evs)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    peel_sent_empty_dsent model ev rest rs rr final;
    eliminate exists (tr:B.bytes). CS.conn_events_sent_seal_replay (step_next model ev) rest rs tr final
    returns Seq.equal rs B.empty
    with _. (
      lemma_empty_sent_tail_collapses (step_next model ev) rest rs tr final
    )
#pop-options

#push-options "--z3rlimit 20 --ifuel 1"
let rec lemma_empty_recv_tail_collapses
  (model:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay model evs rs rr final /\
        FStar.List.Tot.for_all is_empty_recv_ev evs)
      (ensures Seq.equal rr B.empty)
      (decreases evs)
=
  match evs with
  | [] -> ()
  | ev :: rest ->
    peel_received_empty_drecv model ev rest rs rr final;
    eliminate exists (ts:B.bytes). CS.conn_events_received_decode_replay (step_next model ev) rest ts rr final
    returns Seq.equal rr B.empty
    with _. (
      lemma_empty_recv_tail_collapses (step_next model ev) rest ts rr final
    )
#pop-options

#push-options "--z3rlimit 30 --fuel 12 --ifuel 2"
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
        CS.conn_events_sent_seal_replay m0
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
  eliminate exists (tr0:B.bytes). CS.conn_events_sent_seal_replay m1 (ev1 :: tail10) ps tr0 m12
  returns (Seq.equal ps serialized_ch)
  with _. (
    peel_sent_cleartext_ch_head m1 ch tail10 ps tr0 m12;
    let m2 = step_next m1 ev1 in
    eliminate exists (ts trx:B.bytes).
        Seq.equal ps (B.append serialized_ch ts) /\
        CS.conn_events_sent_seal_replay m2 tail10 ts trx m12
    returns (Seq.equal ps serialized_ch)
    with _. (
      lemma_two_install_events_are_local e4 e5;
      assert (FStar.List.Tot.for_all is_empty_sent_ev tail10);
      lemma_empty_sent_tail_collapses m2 tail10 ts trx m12;
      assert (Seq.equal ts B.empty);
      Seq.append_empty_r serialized_ch;
      Seq.lemma_eq_elim ps serialized_ch
    )
  )
#pop-options

#push-options "--z3rlimit 30 --fuel 12 --ifuel 2"
let lemma_server_prefix_received_ch
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (sel:CS.server_handshake_selection)
  (shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (ps pr:B.bytes) (m5:CS.connection_model)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay m0
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
      CS.conn_events_received_decode_replay m2 tail3 ts tr m5
  returns (CS.received_cleartext_tls_message_raw (M.TlsHandshake (M.ClientHello ch)) pr)
  with _. (
    assert (FStar.List.Tot.for_all is_empty_recv_ev tail3);
    lemma_empty_recv_tail_collapses m2 tail3 ts tr m5;
    assert (Seq.equal tr B.empty);
    Seq.append_empty_r ds;
    Seq.lemma_eq_elim pr ds
  )
#pop-options

#push-options "--z3rlimit 30 --fuel 12 --ifuel 2"
let lemma_server_flight_received_empty
  (m0:CS.connection_model)
  (e5 e6:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  (ps pr:B.bytes) (mf:CS.connection_model)
  : Lemma
      (requires
        PNTSS.server_no_tail_two_handshake_install_cover e5 e6 /\
        CS.conn_events_received_decode_replay m0
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


// ===== HOLE-4 reconstruction machinery (cover -> canonical self-install replay) =====
let iaw (cawm:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeys {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficWrite;
      CS.install_material = cawm;
    })

let iar (carm:CS.traffic_key_material) : CS.conn_event =
  CS.ConnLocalEvent
    (CS.LocalInstallTrafficKeys {
      CS.install_epoch = CS.TrafficApplication;
      CS.install_direction = CS.TrafficRead;
      CS.install_material = carm;
    })

let append_empty_left (rs:B.bytes) : Lemma (Seq.equal (B.append B.empty rs) rs) =
  Seq.lemma_len_append B.empty rs;
  Seq.lemma_eq_intro (B.append B.empty rs) rs

// Peel a local (empty-delta) event off the front of a sent-seal replay.
#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
let peel_local_deconstruct
  (m:CS.connection_model)
  (lev:CS.conn_event)
  (rest:list CS.conn_event)
  (rs rr:B.bytes)
  (final m1:CS.connection_model)
  : Lemma
      (requires
        CS.ConnLocalEvent? lev /\
        CS.conn_events_sent_seal_replay m (lev :: rest) rs rr final /\
        CS.step_model m lev == Some m1)
      (ensures
        CS.conn_events_sent_seal_replay m1 rest rs rr final /\
        CS.legal_event m lev)
=
  PWReplay.lemma_conn_events_sent_seal_replay_head m lev rest rs rr final;
  eliminate exists model1 delta_sent delta_received tail_sent tail_received.
      (CS.legal_event m lev /\
       CS.step_model m lev == Some model1 /\
       CS.event_raw_delta_legal m lev delta_sent delta_received /\
       CS.sent_event_nonempty_seal_projection m lev delta_sent /\
       Seq.equal rs (B.append delta_sent tail_sent) /\
       Seq.equal rr (B.append delta_received tail_received) /\
       CS.conn_events_sent_seal_replay model1 rest tail_sent tail_received final)
  returns (CS.conn_events_sent_seal_replay m1 rest rs rr final /\ CS.legal_event m lev)
  with _.
  (
    // local event: delta_sent, delta_received empty; model1 == m1
    assert (Seq.equal delta_sent B.empty);
    assert (Seq.equal delta_received B.empty);
    Seq.lemma_eq_elim delta_sent B.empty;
    Seq.lemma_eq_elim delta_received B.empty;
    append_empty_left tail_sent;
    append_empty_left tail_received;
    assert (Seq.equal rs tail_sent);
    assert (Seq.equal rr tail_received);
    assert (model1 == m1)
  )
#pop-options

// Cons a local (empty-delta) event onto the front of a sent-seal replay.
#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
let peel_local_construct
  (m:CS.connection_model)
  (lev:CS.conn_event)
  (rest:list CS.conn_event)
  (rs rr:B.bytes)
  (final m1:CS.connection_model)
  : Lemma
      (requires
        CS.ConnLocalEvent? lev /\
        CS.legal_event m lev /\
        CS.step_model m lev == Some m1 /\
        CS.conn_events_sent_seal_replay m1 rest rs rr final)
      (ensures CS.conn_events_sent_seal_replay m (lev :: rest) rs rr final)
=
  append_empty_left rs;
  append_empty_left rr;
  PWReplay.lemma_conn_events_sent_seal_replay_cons
    m lev rest rs rr final m1 B.empty B.empty rs rr
#pop-options

let ev_sent_of (cf:GFin.finished) : CS.conn_event =
  CS.ConnNetworkEvent ({
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.Finished cf);
  })

let ev_vf_of (sf:GFin.finished) : CS.conn_event =
  CS.ConnLocalEvent (CS.LocalVerifyFinished sf)

// commutation of the two client app installs (proved earlier standalone)
#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
let install_commute
  (m:CS.connection_model)
  (cawm carm:CS.traffic_key_material)
  (m_r m_rw:CS.connection_model)
  : Lemma
      (requires
        CS.step_model m (iar carm) == Some m_r /\
        CS.step_model m_r (iaw cawm) == Some m_rw)
      (ensures
        (exists m_w.
          CS.step_model m (iaw cawm) == Some m_w /\
          CS.step_model m_w (iar carm) == Some m_rw))
= ()
#pop-options

// commutation of the two client app installs (proved earlier standalone)
#push-options "--z3rlimit 30 --fuel 3 --ifuel 3"
let install_commute_full
  (m:CS.connection_model)
  (cawm carm:CS.traffic_key_material)
  (m_r m_rw:CS.connection_model)
  : Lemma
      (requires
        CS.step_model m (iar carm) == Some m_r /\
        CS.step_model m_r (iaw cawm) == Some m_rw /\
        CS.legal_event m (iar carm) /\
        CS.legal_event m_r (iaw cawm))
      (ensures
        (exists m_w.
          CS.step_model m (iaw cawm) == Some m_w /\
          CS.step_model m_w (iar carm) == Some m_rw /\
          CS.legal_event m (iaw cawm) /\
          CS.legal_event m_w (iar carm)))
= ()
#pop-options

#push-options "--z3rlimit 30 --fuel 3 --ifuel 3"
let plain_write_install_legal
  (m m1:CS.connection_model)
  (ev:CS.conn_event)
  (cawm:CS.traffic_key_material)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_write_install_event ev /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m1 /\
        CS.step_model m (iaw cawm) == Some m1)
      (ensures CS.legal_event m (iaw cawm))
=
  PNTCAS.lemma_client_no_tail_application_write_install_event_cases ev
#pop-options

#push-options "--z3rlimit 30 --fuel 3 --ifuel 3"
let plain_read_install_legal
  (m m1:CS.connection_model)
  (ev:CS.conn_event)
  (carm:CS.traffic_key_material)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_read_install_event ev /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m1 /\
        CS.step_model m (iar carm) == Some m1)
      (ensures CS.legal_event m (iar carm))
=
  PNTCAS.lemma_client_no_tail_application_read_install_event_cases ev
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"
let lemma_two_app_install_events_are_local
  (e13 e14:CS.conn_event)
  : Lemma
      (requires PNTCAS.client_no_tail_application_install_cover e13 e14)
      (ensures CS.ConnLocalEvent? e13 /\ CS.ConnLocalEvent? e14)
=
  PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
  eliminate
    (PNTCAS.client_no_tail_application_write_install_event e13 /\
     PNTCAS.client_no_tail_application_read_install_event e14) \/
    (PNTCAS.client_no_tail_application_read_install_event e13 /\
     PNTCAS.client_no_tail_application_write_install_event e14)
  returns (CS.ConnLocalEvent? e13 /\ CS.ConnLocalEvent? e14)
  with _. (
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases e13;
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases e14
  )
  and _. (
    PNTCAS.lemma_client_no_tail_application_read_install_event_cases e13;
    PNTCAS.lemma_client_no_tail_application_write_install_event_cases e14
  )
#pop-options

#push-options "--z3rlimit 30 --fuel 4 --ifuel 2 --split_queries always"
let lemma_cover_to_self_install_replay
  (model12:CS.connection_model)
  (sf:GFin.finished)
  (e13 e14:CS.conn_event)
  (cf:GFin.finished)
  (suffix_sent suffix_received:B.bytes)
  (final:CS.connection_model)
  : Lemma
      (requires
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        CS.conn_events_sent_seal_replay model12
          (ev_vf_of sf :: e13 :: e14 :: ev_sent_of cf :: [])
          suffix_sent suffix_received final)
      (ensures
        (exists
           (cawm carm:CS.traffic_key_material)
           (av aw ar:CS.connection_model).
           CS.step_model model12 (ev_vf_of sf) == Some av /\
           CS.step_model av (iaw cawm) == Some aw /\
           CS.step_model aw (iar carm) == Some ar /\
           CS.step_model ar (ev_sent_of cf) == Some final /\
           CS.conn_events_sent_seal_replay model12
             (ev_vf_of sf :: iaw cawm :: iar carm :: ev_sent_of cf :: [])
             suffix_sent suffix_received final))
=
  let ev_vf = ev_vf_of sf in
  let ev_sent = ev_sent_of cf in
  let goal : prop =
    (exists
       (cawm carm:CS.traffic_key_material)
       (av aw ar:CS.connection_model).
       CS.step_model model12 ev_vf == Some av /\
       CS.step_model av (iaw cawm) == Some aw /\
       CS.step_model aw (iar carm) == Some ar /\
       CS.step_model ar ev_sent == Some final /\
       CS.conn_events_sent_seal_replay model12
         (ev_vf :: iaw cawm :: iar carm :: ev_sent :: [])
         suffix_sent suffix_received final) in
  PNTCFR.lemma_client_finished_sent_seal_suffix_head_steps
    model12 sf e13 e14 cf suffix_sent suffix_received final;
  eliminate exists after_verify after_e13 after_e14.
      (CS.step_model model12 ev_vf == Some after_verify /\
       CS.step_model after_verify e13 == Some after_e13 /\
       CS.step_model after_e13 e14 == Some after_e14 /\
       CS.step_model after_e14 ev_sent == Some final)
  returns goal
  with _hs.
  (
    PNTCAS.lemma_client_no_tail_application_install_cover_cases e13 e14;
    lemma_two_app_install_events_are_local e13 e14;
    peel_local_deconstruct model12 ev_vf (e13 :: e14 :: ev_sent :: []) suffix_sent suffix_received final after_verify;
    peel_local_deconstruct after_verify e13 (e14 :: ev_sent :: []) suffix_sent suffix_received final after_e13;
    peel_local_deconstruct after_e13 e14 (ev_sent :: []) suffix_sent suffix_received final after_e14;
    // now: conn_events_sent_seal_replay after_e14 [ev_sent] suffix_sent suffix_received final
    eliminate
       (PNTCAS.client_no_tail_application_write_install_event e13 /\
        PNTCAS.client_no_tail_application_read_install_event e14) \/
       (PNTCAS.client_no_tail_application_read_install_event e13 /\
        PNTCAS.client_no_tail_application_write_install_event e14)
    returns goal
    with _caseA.
    (
      PNTCAS.lemma_client_no_tail_application_write_install_event_step_model_as_plain after_verify after_e13 e13;
      PNTCAS.lemma_client_no_tail_application_read_install_event_step_model_as_plain after_e13 after_e14 e14;
      eliminate exists cawm. CS.step_model after_verify (iaw cawm) == Some after_e13
      returns goal
      with _pw.
      (
        eliminate exists carm. CS.step_model after_e13 (iar carm) == Some after_e14
        returns goal
        with _pr.
        (
          plain_write_install_legal after_verify after_e13 e13 cawm;
          plain_read_install_legal after_e13 after_e14 e14 carm;
          peel_local_construct after_e13 (iar carm) (ev_sent :: []) suffix_sent suffix_received final after_e14;
          peel_local_construct after_verify (iaw cawm) (iar carm :: ev_sent :: []) suffix_sent suffix_received final after_e13;
          peel_local_construct model12 ev_vf (iaw cawm :: iar carm :: ev_sent :: []) suffix_sent suffix_received final after_verify;
          assert goal
        )
      )
    )
    and _caseB.
    (
      PNTCAS.lemma_client_no_tail_application_read_install_event_step_model_as_plain after_verify after_e13 e13;
      PNTCAS.lemma_client_no_tail_application_write_install_event_step_model_as_plain after_e13 after_e14 e14;
      eliminate exists carm. CS.step_model after_verify (iar carm) == Some after_e13
      returns goal
      with _pr.
      (
        eliminate exists cawm. CS.step_model after_e13 (iaw cawm) == Some after_e14
        returns goal
        with _pw.
        (
          plain_read_install_legal after_verify after_e13 e13 carm;
          plain_write_install_legal after_e13 after_e14 e14 cawm;
          install_commute_full after_verify cawm carm after_e13 after_e14;
          eliminate exists aw. (CS.step_model after_verify (iaw cawm) == Some aw /\ CS.step_model aw (iar carm) == Some after_e14 /\ CS.legal_event after_verify (iaw cawm) /\ CS.legal_event aw (iar carm))
          returns goal
          with _cm.
          (
            peel_local_construct aw (iar carm) (ev_sent :: []) suffix_sent suffix_received final after_e14;
            peel_local_construct after_verify (iaw cawm) (iar carm :: ev_sent :: []) suffix_sent suffix_received final aw;
            peel_local_construct model12 ev_vf (iaw cawm :: iar carm :: ev_sent :: []) suffix_sent suffix_received final after_verify;
            assert goal
          )
        )
      )
    )
  )
#pop-options

// ===== end HOLE-4 reconstruction machinery =====

// ===== HOLE-4 packaging: compact exact-slice + reconstruction + client wire record =====
#push-options "--z3rlimit 30 --fuel 16 --ifuel 2 --split_queries always"
let lemma_h4_client_exact_recon (client server:CS.connection_state)
  : Lemma
      (requires
        PNTCFS.paired_no_tail_client_finished_staged_milestone client server /\
        CS.connection_state_sent_seal_replay_consistent client /\
        clean16_cleartext_final_hello_slot_milestone client server)
      (ensures
        (exists (model12:CS.connection_model) (sf cf:GFin.finished)
           (cawm carm:CS.traffic_key_material) (av aw ar:CS.connection_model)
           (suffix_sent suffix_received prefix_sent frag:B.bytes)
           (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello) (client_shared:C.x25519_shared_secret)
           (e4 e5:CS.conn_event) (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
           (cv:GCV.certificateVerify) (e13 e14:CS.conn_event) (prefix_received:B.bytes).
           Seq.equal client.CS.cs_wire_log.CL.raw_sent (B.append prefix_sent suffix_sent) /\
           W.parse_record_wire prefix_sent == Some (T.Handshake, frag, B.length prefix_sent) /\
           CS.step_model model12 (ev_vf_of sf) == Some av /\
           CS.step_model av (iaw cawm) == Some aw /\
           CS.step_model aw (iar carm) == Some ar /\
           CS.step_model ar (ev_sent_of cf) == Some client.CS.cs_model /\
           CS.conn_events_sent_seal_replay model12
             (ev_vf_of sf :: iaw cawm :: iar carm :: ev_sent_of cf :: [])
             suffix_sent suffix_received client.CS.cs_model /\
           CS.conn_events_sent_seal_replay
             (CS.initial_model client.CS.cs_model.CS.model_config)
             (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
              CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
              e4 :: e5 ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
              [])
             prefix_sent prefix_received model12 /\
           client.CS.cs_event_log ==
             (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
              CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
              e4 :: e5 ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
              CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
              CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
              CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
              e13 :: e14 ::
              CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf); }) ::
              [])))
=
  PNTCFR.lemma_client_finished_exact_suffix_sent_seal_replay_slice_from_staged_milestone client server;
  let goalp : prop =
    (exists (model12:CS.connection_model) (sf cf:GFin.finished)
       (cawm carm:CS.traffic_key_material) (av aw ar:CS.connection_model)
       (suffix_sent suffix_received prefix_sent frag:B.bytes)
       (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello) (client_shared:C.x25519_shared_secret)
       (e4 e5:CS.conn_event) (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
       (cv:GCV.certificateVerify) (e13 e14:CS.conn_event) (prefix_received:B.bytes).
       Seq.equal client.CS.cs_wire_log.CL.raw_sent (B.append prefix_sent suffix_sent) /\
       W.parse_record_wire prefix_sent == Some (T.Handshake, frag, B.length prefix_sent) /\
       CS.step_model model12 (ev_vf_of sf) == Some av /\
       CS.step_model av (iaw cawm) == Some aw /\
       CS.step_model aw (iar carm) == Some ar /\
       CS.step_model ar (ev_sent_of cf) == Some client.CS.cs_model /\
       CS.conn_events_sent_seal_replay model12
         (ev_vf_of sf :: iaw cawm :: iar carm :: ev_sent_of cf :: [])
         suffix_sent suffix_received client.CS.cs_model /\
       CS.conn_events_sent_seal_replay
         (CS.initial_model client.CS.cs_model.CS.model_config)
         (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
          e4 :: e5 ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
          CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
          CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
          [])
         prefix_sent prefix_received model12 /\
       client.CS.cs_event_log ==
         (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
          CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
          e4 :: e5 ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
          CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
          CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
          CS.ConnLocalEvent (CS.LocalVerifyFinished sf) ::
          e13 :: e14 ::
          CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf); }) ::
          [])) in
  eliminate exists start ch sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf
    (model12:CS.connection_model) prefix_sent prefix_received suffix_sent suffix_received.
    (
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

    )
  returns goalp
  with _ex.
  (
    lemma_cover_to_self_install_replay model12 sf e13 e14 cf suffix_sent suffix_received client.CS.cs_model;
    eliminate exists client_start client_ch client_sh client_shared2 client_rest
                     server_ch selection server_shared server_sh server_rest.
      (PNTRB.role_local_cleartext_prefix_shape client server
         client_start client_ch client_sh client_shared2 client_rest
         server_ch selection server_shared server_sh server_rest /\
       WFL.supported_client_hello_wire_profile client_ch /\
       PNTRB.normalized_cleartext_raw_wire_bridge client_ch server_ch client_sh server_sh /\
       client.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some client_ch /\
       client.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some client_sh /\
       server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some server_ch /\
       server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some server_sh)
    returns goalp
    with _prof.
    (
      assert (ch == client_ch);
      lemma_client_exact_prefix_sent_ch
        (CS.initial_model client.CS.cs_model.CS.model_config)
        start ch sh client_shared e4 e5 ee cert peer cv sf
        prefix_sent prefix_received model12;
      lemma_client_hello_sent_is_wire_h4 ch prefix_sent;
      eliminate exists frag.
        W.parse_record_wire prefix_sent == Some (T.Handshake, frag, B.length prefix_sent)
      returns goalp
      with _wire.
      (
        eliminate exists (cawm carm:CS.traffic_key_material) (av aw ar:CS.connection_model).
          (CS.step_model model12 (ev_vf_of sf) == Some av /\
           CS.step_model av (iaw cawm) == Some aw /\
           CS.step_model aw (iar carm) == Some ar /\
           CS.step_model ar (ev_sent_of cf) == Some client.CS.cs_model /\
           CS.conn_events_sent_seal_replay model12
             (ev_vf_of sf :: iaw cawm :: iar carm :: ev_sent_of cf :: [])
             suffix_sent suffix_received client.CS.cs_model)
        returns goalp
        with _rec.
        (
          introduce exists (model12':CS.connection_model) (sf':GFin.finished) (cf':GFin.finished)
             (cawm':CS.traffic_key_material) (carm':CS.traffic_key_material)
             (av':CS.connection_model) (aw':CS.connection_model) (ar':CS.connection_model)
             (suffix_sent':B.bytes) (suffix_received':B.bytes) (prefix_sent':B.bytes) (frag':B.bytes)
             (start':CS.handshake_start) (ch':GCH.clientHello) (sh':GSH.serverHello) (client_shared':C.x25519_shared_secret)
             (e4' e5':CS.conn_event) (ee':GEE.encryptedExtensions) (cert':GCert.certificate) (peer':X.peer_identity)
             (cv':GCV.certificateVerify) (e13' e14':CS.conn_event) (prefix_received':B.bytes).
             (Seq.equal client.CS.cs_wire_log.CL.raw_sent (B.append prefix_sent' suffix_sent') /\
              W.parse_record_wire prefix_sent' == Some (T.Handshake, frag', B.length prefix_sent') /\
              CS.step_model model12' (ev_vf_of sf') == Some av' /\
              CS.step_model av' (iaw cawm') == Some aw' /\
              CS.step_model aw' (iar carm') == Some ar' /\
              CS.step_model ar' (ev_sent_of cf') == Some client.CS.cs_model /\
              CS.conn_events_sent_seal_replay model12'
                (ev_vf_of sf' :: iaw cawm' :: iar carm' :: ev_sent_of cf' :: [])
                suffix_sent' suffix_received' client.CS.cs_model /\
              CS.conn_events_sent_seal_replay
                (CS.initial_model client.CS.cs_model.CS.model_config)
                (CS.ConnLocalEvent (CS.LocalStartHandshake start') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch'); }) ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh'); }) ::
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared') ::
                 e4' :: e5' ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee'); }) ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert'); }) ::
                 CS.ConnLocalEvent (CS.LocalValidateCertificate peer') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv'); }) ::
                 CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf'); }) ::
                 [])
                prefix_sent' prefix_received' model12' /\
              client.CS.cs_event_log ==
                (CS.ConnLocalEvent (CS.LocalStartHandshake start') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch'); }) ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh'); }) ::
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared') ::
                 e4' :: e5' ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee'); }) ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert'); }) ::
                 CS.ConnLocalEvent (CS.LocalValidateCertificate peer') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv'); }) ::
                 CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv') ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf'); }) ::
                 CS.ConnLocalEvent (CS.LocalVerifyFinished sf') ::
                 e13' :: e14' ::
                 CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf'); }) ::
                 []))
          with model12 sf cf cawm carm av aw ar suffix_sent suffix_received prefix_sent frag
               start ch sh client_shared e4 e5 ee cert peer cv e13 e14 prefix_received
          and ()
        )
      )
    )
  )
#pop-options


// ============================================================
// HOLE 3 helpers (client-write/server-read alignment) — ported
// ============================================================
#push-options "--z3rlimit 30 --split_queries always --ifuel 2"
let lemma_client_write_install_normalize
  (m m':CS.connection_model) (ev:CS.conn_event)
  : Lemma
      (requires
        PCPS.client_no_tail_handshake_write_install_event ev /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures
        (exists (mat:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule m.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; } /\
          CS.step_model m
            (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
              { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; }))
            == Some m'))
=
  PCPS.lemma_client_no_tail_handshake_write_install_event_cases ev;
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeys install) ->
    introduce exists (mat:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule m.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; } /\
      CS.step_model m
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; }))
        == Some m'
    with install.CS.install_material and ()
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    introduce exists (mat:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule m.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; } /\
      CS.step_model m
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
          { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat; }))
        == Some m'
    with role_install.CS.install_payload.CS.install_material and ()
#pop-options

#push-options "--z3rlimit 20 --ifuel 2"
let install_preserves_hs_secret_transcript
  (m m':CS.connection_model) (ev:CS.local_event)
  : Lemma
      (requires
        (CS.LocalInstallTrafficKeys? ev \/ CS.LocalInstallTrafficKeysForRole? ev) /\
        CS.step_model m (CS.ConnLocalEvent ev) == Some m')
      (ensures
        m'.CS.model_handshake.CS.hs_transcript == m.CS.model_handshake.CS.hs_transcript /\
        m'.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
          == m.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret)
= ()
#pop-options

#push-options "--z3rlimit 20 --ifuel 2"
let lemma_client_read_install_preserves_record_write
  (ev:CS.conn_event)
  : Lemma
      (requires PCPS.client_no_tail_handshake_read_install_event ev)
      (ensures
        CS.ConnLocalEvent? ev /\
        PWL.local_event_preserves_record_write (CS.ConnLocalEvent?._0 ev))
=
  PCPS.lemma_client_no_tail_handshake_read_install_event_cases ev
#pop-options

#push-options "--z3rlimit 30 --split_queries always"
let lemma_client_identity_determinism
  (initial model4_c client_after_installs_c c_after3 model12_ex:CS.connection_model)
  (pre4 two six:list CS.conn_event)
  (ps pr rs1 rr1 rs2 rr2 rs3 rr3:B.bytes)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay initial
          (L.append pre4 (L.append two six)) ps pr model12_ex /\
        CS.conn_events_received_decode_replay initial pre4 rs1 rr1 model4_c /\
        CS.conn_events_received_decode_replay model4_c two rs2 rr2 client_after_installs_c /\
        CS.conn_events_received_decode_replay client_after_installs_c six rs3 rr3 c_after3)
      (ensures model12_ex == c_after3)
=
  // split P12 = pre4 ++ (two ++ six)
  PWReplay.lemma_conn_events_sent_seal_replay_append_split
    initial pre4 (L.append two six) ps pr model12_ex;
  eliminate exists mid1 ps1 pr1 ss1 sr1.
    Seq.equal ps (B.append ps1 ss1) /\ Seq.equal pr (B.append pr1 sr1) /\
    CS.conn_events_sent_seal_replay initial pre4 ps1 pr1 mid1 /\
    CS.conn_events_sent_seal_replay mid1 (L.append two six) ss1 sr1 model12_ex
  returns model12_ex == c_after3
  with _.
  (
    PWReplay.lemma_conn_events_sent_received_replays_same_events_final_model_equal
      initial pre4 ps1 pr1 mid1 rs1 rr1 model4_c;
    // mid1 == model4_c
    PWReplay.lemma_conn_events_sent_seal_replay_append_split
      model4_c two six ss1 sr1 model12_ex;
    eliminate exists mid2 ps2 pr2 ss2 sr2.
      Seq.equal ss1 (B.append ps2 ss2) /\ Seq.equal sr1 (B.append pr2 sr2) /\
      CS.conn_events_sent_seal_replay model4_c two ps2 pr2 mid2 /\
      CS.conn_events_sent_seal_replay mid2 six ss2 sr2 model12_ex
    returns model12_ex == c_after3
    with _.
    (
      PWReplay.lemma_conn_events_sent_received_replays_same_events_final_model_equal
        model4_c two ps2 pr2 mid2 rs2 rr2 client_after_installs_c;
      // mid2 == client_after_installs_c
      PWReplay.lemma_conn_events_sent_received_replays_same_events_final_model_equal
        client_after_installs_c six ss2 sr2 model12_ex rs3 rr3 c_after3
    )
  )
#pop-options

#push-options "--z3rlimit 30 --split_queries always --ifuel 2"
let lemma_server_read_install_normalize
  (m m':CS.connection_model) (ev:CS.conn_event)
  : Lemma
      (requires
        PNTSS.server_no_tail_handshake_read_install_event ev /\
        CS.legal_event m ev /\
        CS.step_model m ev == Some m')
      (ensures
        (exists (mat:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint m.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; } /\
          CS.step_model m
            (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; }; }))
            == Some m'))
=
  match ev with
  | CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole role_install) ->
    introduce exists (mat:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint m.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; } /\
      CS.step_model m
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
          CS.install_role = CS.ServerEndpoint;
          CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat; }; }))
        == Some m'
    with role_install.CS.install_payload.CS.install_material and ()
#pop-options

#push-options "--z3rlimit 20 --ifuel 2"
let lemma_server_write_install_preserves_record_read
  (ev:CS.conn_event)
  : Lemma
      (requires PNTSS.server_no_tail_handshake_write_install_event ev)
      (ensures
        CS.ConnLocalEvent? ev /\
        PWL.local_event_preserves_record_read (CS.ConnLocalEvent?._0 ev))
= ()
#pop-options

#push-options "--z3rlimit 30 --ifuel 2 --split_queries always"
let lemma_hole3_alignment_covers
  (model5_r server_after_e5_r server_rr:CS.connection_model)
  (e5_r e6_r:CS.conn_event)
  (model4_c client_after_e4_c client_after_installs_c:CS.connection_model)
  (e4_c e5_c:CS.conn_event)
  : Lemma
      (requires
        (match
          model5_r.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
          model4_c.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
         with
         | Some ss, Some cs -> Seq.equal ss cs
         | _, _ -> False) /\
        Seq.equal
          model5_r.CS.model_handshake.CS.hs_transcript
          model4_c.CS.model_handshake.CS.hs_transcript /\
        PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
        CS.legal_event model5_r e5_r /\
        CS.step_model model5_r e5_r == Some server_after_e5_r /\
        CS.legal_event server_after_e5_r e6_r /\
        CS.step_model server_after_e5_r e6_r == Some server_rr /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        CS.legal_event model4_c e4_c /\
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.legal_event client_after_e4_c e5_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c)
      (ensures PWL.write_read_record_material_aligned client_after_installs_c server_rr)
=
  PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e5_r e6_r;
  PCPS.lemma_client_no_tail_two_handshake_install_cover_cases e4_c e5_c;
  // helper: apply RA:500 at (cwpre, srpre) -> align(cwpost, srpost)
  let apply_ra (cwpre cwpost srpre srpost:CS.connection_model) (mat_w mat_r:CS.traffic_key_material)
    : Lemma
        (requires
          (match cwpre.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
                 srpre.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret with
           | Some a, Some b -> Seq.equal a b | _,_ -> False) /\
          Seq.equal cwpre.CS.model_handshake.CS.hs_transcript srpre.CS.model_handshake.CS.hs_transcript /\
          CS.traffic_install_matches_key_schedule cwpre.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint srpre.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; } /\
          CS.step_model cwpre (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some cwpost /\
          CS.step_model srpre (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; }; })) == Some srpost)
        (ensures PWL.write_read_record_material_aligned cwpost srpost)
    = RA.lemma_client_handshake_write_server_handshake_read_install_aligned_from_key_schedule
        cwpre srpre mat_w mat_r cwpost srpost
  in
  // push client read install (sender) from a->b, keeping receiver r
  let push_client_read (a b r:CS.connection_model) (ev:CS.conn_event)
    : Lemma
        (requires
          PCPS.client_no_tail_handshake_read_install_event ev /\
          CS.step_model a ev == Some b /\
          PWL.write_read_record_material_aligned a r)
        (ensures PWL.write_read_record_material_aligned b r)
    = lemma_client_read_install_preserves_record_write ev;
      (match ev with
       | CS.ConnLocalEvent le ->
         RA.lemma_step_sender_local_event_preserves_write_read_record_material_alignment a le b r)
  in
  // push server write install (receiver) from a->b, keeping sender s
  let push_server_write (s a b:CS.connection_model) (ev:CS.conn_event)
    : Lemma
        (requires
          PNTSS.server_no_tail_handshake_write_install_event ev /\
          CS.step_model a ev == Some b /\
          PWL.write_read_record_material_aligned s a)
        (ensures PWL.write_read_record_material_aligned s b)
    = lemma_server_write_install_preserves_record_read ev;
      (match ev with
       | CS.ConnLocalEvent le ->
         RA.lemma_step_receiver_local_event_preserves_write_read_record_material_alignment s a le b)
  in
  eliminate
    (PNTSS.server_no_tail_handshake_write_install_event e5_r /\ PNTSS.server_no_tail_handshake_read_install_event e6_r) \/
    (PNTSS.server_no_tail_handshake_read_install_event e5_r /\ PNTSS.server_no_tail_handshake_write_install_event e6_r)
  returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
  with _sw. (
    // server write-first: e5_r=write, e6_r=read. server read-pre = server_after_e5_r (== model5_r secret via preserve)
    install_preserves_hs_secret_transcript model5_r server_after_e5_r (CS.ConnLocalEvent?._0 e5_r);
    lemma_server_read_install_normalize server_after_e5_r server_rr e6_r;
    eliminate exists (mat_r:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint server_after_e5_r.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; } /\
      CS.step_model server_after_e5_r (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; }; })) == Some server_rr
    returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
    with _sr2. (
      eliminate
        (PCPS.client_no_tail_handshake_write_install_event e4_c /\ PCPS.client_no_tail_handshake_read_install_event e5_c) \/
        (PCPS.client_no_tail_handshake_read_install_event e4_c /\ PCPS.client_no_tail_handshake_write_install_event e5_c)
      returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
      with _cw. (
        // client write-first: e4_c=write@model4_c
        lemma_client_write_install_normalize model4_c client_after_e4_c e4_c;
        eliminate exists (mat_w:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule model4_c.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.step_model model4_c (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some client_after_e4_c
        returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
        with _cw2. (
          apply_ra model4_c client_after_e4_c server_after_e5_r server_rr mat_w mat_r;
          push_client_read client_after_e4_c client_after_installs_c server_rr e5_c
        )
      )
      and _cr. (
        // client read-first: e4_c=read, e5_c=write@client_after_e4_c
        lemma_read_install_preserves_hs_secret_transcript model4_c client_after_e4_c e4_c;
        lemma_client_write_install_normalize client_after_e4_c client_after_installs_c e5_c;
        eliminate exists (mat_w:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule client_after_e4_c.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.step_model client_after_e4_c (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some client_after_installs_c
        returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
        with _cw2. (
          apply_ra client_after_e4_c client_after_installs_c server_after_e5_r server_rr mat_w mat_r
        )
      )
    )
  )
  and _sr. (
    // server read-first: e5_r=read@model5_r, e6_r=write@server_after_e5_r. server read-pre = model5_r
    lemma_server_read_install_normalize model5_r server_after_e5_r e5_r;
    eliminate exists (mat_r:CS.traffic_key_material).
      CS.traffic_install_matches_key_schedule_for_role CS.ServerEndpoint model5_r.CS.model_handshake
        { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; } /\
      CS.step_model model5_r (CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficRead; CS.install_material = mat_r; }; })) == Some server_after_e5_r
    returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
    with _sr2. (
      eliminate
        (PCPS.client_no_tail_handshake_write_install_event e4_c /\ PCPS.client_no_tail_handshake_read_install_event e5_c) \/
        (PCPS.client_no_tail_handshake_read_install_event e4_c /\ PCPS.client_no_tail_handshake_write_install_event e5_c)
      returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
      with _cw. (
        // client write-first
        lemma_client_write_install_normalize model4_c client_after_e4_c e4_c;
        eliminate exists (mat_w:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule model4_c.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.step_model model4_c (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some client_after_e4_c
        returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
        with _cw2. (
          apply_ra model4_c client_after_e4_c model5_r server_after_e5_r mat_w mat_r;
          push_client_read client_after_e4_c client_after_installs_c server_after_e5_r e5_c;
          push_server_write client_after_installs_c server_after_e5_r server_rr e6_r
        )
      )
      and _cr. (
        // client read-first
        lemma_read_install_preserves_hs_secret_transcript model4_c client_after_e4_c e4_c;
        lemma_client_write_install_normalize client_after_e4_c client_after_installs_c e5_c;
        eliminate exists (mat_w:CS.traffic_key_material).
          CS.traffic_install_matches_key_schedule client_after_e4_c.CS.model_handshake
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; } /\
          CS.step_model client_after_e4_c (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys
            { CS.install_epoch = CS.TrafficHandshake; CS.install_direction = CS.TrafficWrite; CS.install_material = mat_w; })) == Some client_after_installs_c
        returns PWL.write_read_record_material_aligned client_after_installs_c server_rr
        with _cw2. (
          apply_ra client_after_e4_c client_after_installs_c model5_r server_after_e5_r mat_w mat_r;
          push_server_write client_after_installs_c server_after_e5_r server_rr e6_r
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 60 --split_queries always --fuel 2 --ifuel 2"
let lemma_server_prefix_slots_received
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (model5:CS.connection_model)
  : Lemma
      (requires
        m0.CS.model_handshake.CS.hs_client_hello == None /\
        m0.CS.model_handshake.CS.hs_server_hello == None /\
        (exists rs rr.
          CS.conn_events_received_decode_replay m0
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
  peel_received m0 e0 [e1;e2;e3;e4] model5;
  let m1 = step_next m0 e0 in
  peel_received m1 e1 [e2;e3;e4] model5;
  let m2 = step_next m1 e1 in
  assert (m2.CS.model_handshake.CS.hs_client_hello == Some ch);
  peel_received m2 e2 [e3;e4] model5;
  let m3 = step_next m2 e2 in
  peel_received m3 e3 [e4] model5;
  let m4 = step_next m3 e3 in
  assert (m4.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared);
  peel_received m4 e4 [] model5;
  let m5 = step_next m4 e4 in
  peel_nil_received m5 model5;
  assert (m5.CS.model_handshake.CS.hs_server_hello == Some sh)
#pop-options

#push-options "--z3rlimit 60 --split_queries always --fuel 2 --ifuel 2"
let lemma_server_prefix_secret_transcript_received
  (m0:CS.connection_model)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (model5:CS.connection_model)
  : Lemma
      (requires
        m0.CS.model_handshake.CS.hs_transcript == B.empty /\
        m0.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret == None /\
        (exists rs rr.
          CS.conn_events_received_decode_replay m0
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
  peel_received m0 e0 [e1;e2;e3;e4] model5;
  let m1 = step_next m0 e0 in
  peel_received m1 e1 [e2;e3;e4] model5;
  let m2 = step_next m1 e1 in
  peel_received m2 e2 [e3;e4] model5;
  let m3 = step_next m2 e2 in
  peel_received m3 e3 [e4] model5;
  let m4 = step_next m3 e3 in
  assert (m4.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret ==
          Some (K.handshake_secret (K.early_secret B.empty) server_shared));
  peel_received m4 e4 [] model5;
  let m5 = step_next m4 e4 in
  peel_nil_received m5 model5;
  assert (Seq.equal m1.CS.model_handshake.CS.hs_transcript B.empty);
  assert (Seq.equal m2.CS.model_handshake.CS.hs_transcript (W.serialize_handshake (M.ClientHello ch)))
#pop-options

#push-options "--z3rlimit 30 --split_queries always --ifuel 2"
let lemma_cf_client_walk
  (client_after_installs_c receiver final:CS.connection_model)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:TLS13.X509.Spec.peer_identity)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  : Lemma
      (requires
        PWL.write_read_record_material_aligned client_after_installs_c receiver /\
        (exists rs rr. CS.conn_events_received_decode_replay client_after_installs_c
          [
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); };
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
            CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }
          ]
          rs rr final))
      (ensures PWL.write_read_record_material_aligned final receiver)
=
  let ev0 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
  let ev1 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
  let ev2 = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
  let ev3 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
  let ev4 = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
  let ev5 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); } in
  let m0 = client_after_installs_c in
  peel_received m0 ev0 [ev1;ev2;ev3;ev4;ev5] final;
  let m1 = step_next m0 ev0 in
  RA.lemma_step_received_network_event_preserves_write_read_record_material_alignment m0 (M.TlsHandshake (M.EncryptedExtensions ee)) m1 receiver;
  peel_received m1 ev1 [ev2;ev3;ev4;ev5] final;
  let m2 = step_next m1 ev1 in
  RA.lemma_step_received_network_event_preserves_write_read_record_material_alignment m1 (M.TlsHandshake (M.Certificate cert)) m2 receiver;
  peel_received m2 ev2 [ev3;ev4;ev5] final;
  let m3 = step_next m2 ev2 in
  RA.lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment m2 (CS.LocalValidateCertificate peer) m3 receiver;
  peel_received m3 ev3 [ev4;ev5] final;
  let m4 = step_next m3 ev3 in
  RA.lemma_step_received_network_event_preserves_write_read_record_material_alignment m3 (M.TlsHandshake (M.CertificateVerify cv)) m4 receiver;
  peel_received m4 ev4 [ev5] final;
  let m5 = step_next m4 ev4 in
  RA.lemma_step_sender_non_install_local_event_preserves_write_read_record_material_alignment m4 (CS.LocalVerifyCertificateSignature cv) m5 receiver;
  peel_received m5 ev5 [] final;
  let m6 = step_next m5 ev5 in
  RA.lemma_step_received_network_event_preserves_write_read_record_material_alignment m5 (M.TlsHandshake (M.Finished sf)) m6 receiver;
  peel_nil_received m6 final
#pop-options

#push-options "--z3rlimit 30 --split_queries always --ifuel 2"
let lemma_cf_server_walk
  (sender server_rr final:CS.connection_model)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  : Lemma
      (requires
        PWL.write_read_record_material_aligned sender server_rr /\
        (exists rs rr. CS.conn_events_received_decode_replay server_rr
          [
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
          ]
          rs rr final))
      (ensures PWL.write_read_record_material_aligned sender final)
=
  let ev0 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
  let ev1 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
  let ev2 = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
  let ev3 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
  let ev4 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); } in
  let m0 = server_rr in
  peel_received m0 ev0 [ev1;ev2;ev3;ev4] final;
  let m1 = step_next m0 ev0 in
  RA.lemma_step_sent_network_event_preserves_write_read_record_material_alignment sender m0 (M.TlsHandshake (M.EncryptedExtensions ee)) m1;
  peel_received m1 ev1 [ev2;ev3;ev4] final;
  let m2 = step_next m1 ev1 in
  RA.lemma_step_sent_network_event_preserves_write_read_record_material_alignment sender m1 (M.TlsHandshake (M.Certificate cert)) m2;
  peel_received m2 ev2 [ev3;ev4] final;
  let m3 = step_next m2 ev2 in
  RA.lemma_step_receiver_non_install_local_event_preserves_write_read_record_material_alignment sender m2 (CS.LocalSignCertificateVerify cv) m3;
  peel_received m3 ev3 [ev4] final;
  let m4 = step_next m3 ev3 in
  RA.lemma_step_sent_network_event_preserves_write_read_record_material_alignment sender m3 (M.TlsHandshake (M.CertificateVerify cv)) m4;
  peel_received m4 ev4 [] final;
  let m5 = step_next m4 ev4 in
  RA.lemma_step_sent_network_event_preserves_write_read_record_material_alignment sender m4 (M.TlsHandshake (M.Finished sf)) m5;
  peel_nil_received m5 final
#pop-options

let cf_six (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
         (cv:GCV.certificateVerify) (sf:GFin.finished) : list CS.conn_event =
  [
    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); };
    CS.ConnLocalEvent (CS.LocalValidateCertificate peer);
    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
    CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv);
    CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); };
  ]

// End-to-end combiner: tie _x/_c witnesses via two log-eqs, then determinism

#push-options "--z3rlimit 30 --split_queries always --ifuel 2"
let lemma_extract_client_two_six
  (model4_c client_after_e4_c client_after_installs_c c_after3 finalm:CS.connection_model)
  (e4_c e5_c:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  (tail:list CS.conn_event) (rs rr:B.bytes)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay model4_c
          (e4_c :: e5_c :: (L.append (cf_six ee cert peer cv sf) tail)) rs rr finalm /\
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c /\
        c_after3 ==
          step_next
            (step_next
              (step_next
                (step_next
                  (step_next
                    (step_next client_after_installs_c
                      (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }))
                    (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }))
                  (CS.ConnLocalEvent (CS.LocalValidateCertificate peer)))
                (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }))
              (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv)))
            (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }))
      (ensures
        (exists a b. CS.conn_events_received_decode_replay model4_c [e4_c; e5_c] a b client_after_installs_c) /\
        (exists a b. CS.conn_events_received_decode_replay client_after_installs_c (cf_six ee cert peer cv sf) a b c_after3))
=
  let six = cf_six ee cert peer cv sf in
  // e4::e5::(six++tail) == [e4;e5] ++ (six++tail)
  assert (e4_c :: e5_c :: (L.append six tail) == L.append [e4_c; e5_c] (L.append six tail));
  PWReplay.lemma_conn_events_received_decode_replay_append_split
    model4_c [e4_c; e5_c] (L.append six tail) rs rr finalm;
  eliminate exists mid1 ps1 pr1 ss1 sr1.
    Seq.equal rs (B.append ps1 ss1) /\ Seq.equal rr (B.append pr1 sr1) /\
    CS.conn_events_received_decode_replay model4_c [e4_c; e5_c] ps1 pr1 mid1 /\
    CS.conn_events_received_decode_replay mid1 (L.append six tail) ss1 sr1 finalm
  returns
    ((exists a b. CS.conn_events_received_decode_replay model4_c [e4_c; e5_c] a b client_after_installs_c) /\
     (exists a b. CS.conn_events_received_decode_replay client_after_installs_c (cf_six ee cert peer cv sf) a b c_after3))
  with _.
  (
    // mid1 == client_after_installs_c via peel
    peel_received model4_c e4_c [e5_c] mid1;
    peel_received (step_next model4_c e4_c) e5_c [] mid1;
    peel_nil_received (step_next (step_next model4_c e4_c) e5_c) mid1;
    assert (mid1 == client_after_installs_c);
    introduce exists a b. CS.conn_events_received_decode_replay model4_c [e4_c; e5_c] a b client_after_installs_c
    with ps1 pr1 and ();
    // split six ++ tail
    PWReplay.lemma_conn_events_received_decode_replay_append_split
      client_after_installs_c six tail ss1 sr1 finalm;
    eliminate exists mid2 ps2 pr2 ss2 sr2.
      Seq.equal ss1 (B.append ps2 ss2) /\ Seq.equal sr1 (B.append pr2 sr2) /\
      CS.conn_events_received_decode_replay client_after_installs_c six ps2 pr2 mid2 /\
      CS.conn_events_received_decode_replay mid2 tail ss2 sr2 finalm
    returns (exists a b. CS.conn_events_received_decode_replay client_after_installs_c (cf_six ee cert peer cv sf) a b c_after3)
    with _.
    (
      let ev0 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
      let ev1 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
      let ev2 = CS.ConnLocalEvent (CS.LocalValidateCertificate peer) in
      let ev3 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
      let ev4 = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) in
      let ev5 = CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); } in
      peel_received client_after_installs_c ev0 [ev1;ev2;ev3;ev4;ev5] mid2;
      let n1 = step_next client_after_installs_c ev0 in
      peel_received n1 ev1 [ev2;ev3;ev4;ev5] mid2;
      let n2 = step_next n1 ev1 in
      peel_received n2 ev2 [ev3;ev4;ev5] mid2;
      let n3 = step_next n2 ev2 in
      peel_received n3 ev3 [ev4;ev5] mid2;
      let n4 = step_next n3 ev3 in
      peel_received n4 ev4 [ev5] mid2;
      let n5 = step_next n4 ev4 in
      peel_received n5 ev5 [] mid2;
      let n6 = step_next n5 ev5 in
      peel_nil_received n6 mid2;
      assert (mid2 == c_after3);
      introduce exists a b. CS.conn_events_received_decode_replay client_after_installs_c (cf_six ee cert peer cv sf) a b c_after3
      with ps2 pr2 and ()
    )
  )
#pop-options

#push-options "--z3rlimit 30 --split_queries always --ifuel 2"
let lemma_extract_server_covers_flight
  (model5_r server_rr' server_rr after_server_flight_r:CS.connection_model)
  (e5_r e6_r:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate)
  (cv:GCV.certificateVerify) (sf:GFin.finished)
  (rs rr:B.bytes)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay model5_r
          [
            e5_r;
            e6_r;
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
          ]
          rs rr after_server_flight_r /\
        server_rr' == step_next model5_r e5_r /\
        server_rr == step_next server_rr' e6_r)
      (ensures
        CS.legal_event model5_r e5_r /\
        CS.step_model model5_r e5_r == Some server_rr' /\
        CS.legal_event server_rr' e6_r /\
        CS.step_model server_rr' e6_r == Some server_rr /\
        (exists a b. CS.conn_events_received_decode_replay server_rr
          [
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
            CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
            CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
          ]
          a b after_server_flight_r))
=
  let f0 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); } in
  let f1 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); } in
  let f2 = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv) in
  let f3 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); } in
  let f4 = CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); } in
  peel_received model5_r e5_r [e6_r; f0; f1; f2; f3; f4] after_server_flight_r;
  peel_received server_rr' e6_r [f0; f1; f2; f3; f4] after_server_flight_r
#pop-options

// server final slots via received-decode _cr chain (two-segment)
#push-options "--z3rlimit 30 --split_queries always --ifuel 2 --fuel 16"
let lemma_server_final_slots_received
  (server:CS.connection_state)
  (ch:GCH.clientHello) (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret) (sh:GSH.serverHello)
  (e5_r e6_r:CS.conn_event)
  (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (cv:GCV.certificateVerify) (sf:GFin.finished)
  (server_app_write_material server_app_read_material:CS.traffic_key_material) (cf:GFin.finished)
  (model5_r after_server_flight_r:CS.connection_model)
  : Lemma
      (requires
        PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
        (exists rs rr. CS.conn_events_received_decode_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch selection server_shared sh)
           rs rr model5_r) /\
        (exists rs rr. CS.conn_events_received_decode_replay model5_r
           [
             e5_r; e6_r;
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
             CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
           ]
           rs rr after_server_flight_r) /\
        (exists rs rr. CS.conn_events_received_decode_replay after_server_flight_r
           [
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material; }; });
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); };
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material; }; });
             CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
           ]
           rs rr server.CS.cs_model))
      (ensures
        server.CS.cs_model.CS.model_handshake.CS.hs_client_hello == Some ch /\
        server.CS.cs_model.CS.model_handshake.CS.hs_server_hello == Some sh /\
        server.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_shared_secret == Some server_shared)
=
  let m0 = CS.initial_model server.CS.cs_model.CS.model_config in
  assert (m0.CS.model_handshake.CS.hs_client_hello == None);
  assert (m0.CS.model_handshake.CS.hs_server_hello == None);
  lemma_server_prefix_slots_received m0 ch selection server_shared sh model5_r;
  let flight =
    [
      e5_r; e6_r;
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert); };
      CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv);
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); };
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf); }
    ] in
  PNTSS.lemma_server_no_tail_two_handshake_install_cover_cases e5_r e6_r;
  assert (all_not_hello flight);
  lemma_received_replay_preserves_slots model5_r flight after_server_flight_r;
  let cfin =
    [
      CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material; }; });
      CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf); };
      CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
        CS.install_role = CS.ServerEndpoint;
        CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material; }; });
      CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf)
    ] in
  assert (all_not_hello cfin);
  lemma_received_replay_preserves_slots after_server_flight_r cfin server.CS.cs_model
#pop-options



// ============================================================
// HOLE 3 bundle: shared-secret (received), alignment core, client identity
// ============================================================
#push-options "--z3rlimit 30 --fuel 16 --ifuel 2 --split_queries always"
let lemma_shared_secret_eq_received
  (client server:CS.connection_state)
  (ch_r:GCH.clientHello) (selection_r:CS.server_handshake_selection)
  (server_shared_r:C.x25519_shared_secret) (sh_r:GSH.serverHello)
  (e5_r e6_r:CS.conn_event)
  (ee_r:GEE.encryptedExtensions) (cert_r:GCert.certificate) (cv_r:GCV.certificateVerify)
  (sf_r:GFin.finished) (cf_r:GFin.finished)
  (server_app_write_material_r server_app_read_material_r:CS.traffic_key_material)
  (model5_r after_server_flight_r:CS.connection_model)
  (start_c:CS.handshake_start) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (client_shared_c:C.x25519_shared_secret)
  (e4_c e5_c e13_c e14_c:CS.conn_event)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (cf_c:GFin.finished)
  (model4_c:CS.connection_model)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        PNTCAS.client_no_tail_application_install_cover e13_c e14_c /\
        (exists rs rr. CS.conn_events_received_decode_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch_r selection_r server_shared_r sh_r)
           rs rr model5_r) /\
        (exists rs rr. CS.conn_events_received_decode_replay model5_r
           [
             e5_r; e6_r;
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_r); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert_r); };
             CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_r);
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_r); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf_r); }
           ]
           rs rr after_server_flight_r) /\
        (exists rs rr. CS.conn_events_received_decode_replay after_server_flight_r
           [
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material_r; }; });
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf_r); };
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material_r; }; });
             CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_r)
           ]
           rs rr server.CS.cs_model) /\
        (exists rs rr. CS.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
           rs rr model4_c) /\
        (exists rs rr. CS.conn_events_received_decode_replay model4_c
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
           rs rr client.CS.cs_model))
      (ensures Seq.equal server_shared_r client_shared_c)
=
  lemma_server_final_slots_received server ch_r selection_r server_shared_r sh_r
    e5_r e6_r ee_r cert_r cv_r sf_r server_app_write_material_r server_app_read_material_r cf_r
    model5_r after_server_flight_r;
  lemma_client_suffix_all_not_hello e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c;
  lemma_client_final_slots client start_c ch_c sh_c client_shared_c model4_c
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
     ]);
  Pairing.lemma_client_server_driver_paired_x25519_key_shares_from_key_share_projection_inputs
    client server;
  CSL.lemma_paired_x25519_key_shares_shared_secret_agree client server;
  assert (Seq.equal client_shared_c server_shared_r)
#pop-options

// focused congruence: rewrite the client suffix's explicit tail into cf_six ++ tail form
#push-options "--z3rlimit 20 --fuel 16 --ifuel 2"
let lemma_client_suffix_append_form
  (model4_c finalm:CS.connection_model)
  (e4_c e5_c e13_c e14_c:CS.conn_event)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (cf_c:GFin.finished)
  (suffix_sent_c suffix_received_c:B.bytes)
  : Lemma
      (requires
        CS.conn_events_received_decode_replay model4_c
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
          suffix_sent_c suffix_received_c finalm)
      (ensures
        CS.conn_events_received_decode_replay model4_c
          (e4_c :: e5_c ::
           (L.append (cf_six ee_c cert_c peer_c cv_c sf_c)
             [
               CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
               e13_c;
               e14_c;
               CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
             ]))
          suffix_sent_c suffix_received_c finalm)
=
  ()
#pop-options

#push-options "--z3rlimit 30 --fuel 16 --ifuel 2 --split_queries always"
let lemma_pack_cf_align_core
  (client server:CS.connection_state)
  (ch_r:GCH.clientHello) (selection_r:CS.server_handshake_selection)
  (server_shared_r:C.x25519_shared_secret) (sh_r:GSH.serverHello)
  (e5_r e6_r:CS.conn_event)
  (ee_r:GEE.encryptedExtensions) (cert_r:GCert.certificate) (cv_r:GCV.certificateVerify)
  (sf_r:GFin.finished) (cf_r:GFin.finished)
  (server_app_write_material_r server_app_read_material_r:CS.traffic_key_material)
  (model5_r after_server_flight_r:CS.connection_model)
  (server_flight_sent_r server_flight_received_r:B.bytes)
  (start_c:CS.handshake_start) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello)
  (client_shared_c:C.x25519_shared_secret)
  (e4_c e5_c e13_c e14_c:CS.conn_event)
  (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (cf_c:GFin.finished)
  (model4_c client_after_e4_c client_after_installs_c c_after3:CS.connection_model)
  (suffix_sent_c suffix_received_c:B.bytes)
  : Lemma
      (requires
        CD.client_driver_application_ready client /\
        SD.server_driver_application_ready server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        clean16_cleartext_final_hello_slot_milestone client server /\
        PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        PNTCAS.client_no_tail_application_install_cover e13_c e14_c /\
        (exists rs rr. CS.conn_events_received_decode_replay
           (CS.initial_model server.CS.cs_model.CS.model_config)
           (PWSeg.server_cleartext_handshake_prefix_events ch_r selection_r server_shared_r sh_r)
           rs rr model5_r) /\
        CS.conn_events_received_decode_replay model5_r
           [
             e5_r; e6_r;
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_r); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Certificate cert_r); };
             CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_r);
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_r); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished sf_r); }
           ]
           server_flight_sent_r server_flight_received_r after_server_flight_r /\
        (exists rs rr. CS.conn_events_received_decode_replay after_server_flight_r
           [
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficWrite; CS.install_material = server_app_write_material_r; }; });
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished cf_r); };
             CS.ConnLocalEvent (CS.LocalInstallTrafficKeysForRole {
               CS.install_role = CS.ServerEndpoint;
               CS.install_payload = { CS.install_epoch = CS.TrafficApplication; CS.install_direction = CS.TrafficRead; CS.install_material = server_app_read_material_r; }; });
             CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_r)
           ]
           rs rr server.CS.cs_model) /\
        (exists rs rr. CS.conn_events_received_decode_replay
           (CS.initial_model client.CS.cs_model.CS.model_config)
           (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c client_shared_c)
           rs rr model4_c) /\
        CS.conn_events_received_decode_replay model4_c
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
           suffix_sent_c suffix_received_c client.CS.cs_model /\
        CS.legal_event model4_c e4_c /\
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.legal_event client_after_e4_c e5_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c /\
        c_after3 ==
          step_next
            (step_next
              (step_next
                (step_next
                  (step_next
                    (step_next client_after_installs_c
                      (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); }))
                    (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); }))
                  (CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c)))
                (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); }))
              (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c)))
            (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); }))
      (ensures PWL.write_read_record_material_aligned c_after3 after_server_flight_r)
=
  let server_rr' = step_next model5_r e5_r in
  let server_rr = step_next server_rr' e6_r in
  let tail_c =
    [
      CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
      e13_c;
      e14_c;
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
    ] in
  // establish model5_r / model4_c handshake-secret + transcript equality
  lemma_shared_secret_eq_received client server ch_r selection_r server_shared_r sh_r
    e5_r e6_r ee_r cert_r cv_r sf_r cf_r server_app_write_material_r server_app_read_material_r
    model5_r after_server_flight_r
    start_c ch_c sh_c client_shared_c e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c model4_c;
  lemma_server_prefix_secret_transcript_received
    (CS.initial_model server.CS.cs_model.CS.model_config)
    ch_r selection_r server_shared_r sh_r model5_r;
  lemma_client_prefix_secret_transcript
    (CS.initial_model client.CS.cs_model.CS.model_config)
    start_c ch_c sh_c client_shared_c model4_c;
  lemma_hs_secret_seq_eq server_shared_r client_shared_c;
  lemma_server_final_slots_received server ch_r selection_r server_shared_r sh_r
    e5_r e6_r ee_r cert_r cv_r sf_r server_app_write_material_r server_app_read_material_r cf_r
    model5_r after_server_flight_r;
  lemma_client_suffix_all_not_hello e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c;
  lemma_client_final_slots client start_c ch_c sh_c client_shared_c model4_c
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
     ]);
  lemma_checkpoint_th_sh_from_milestone client server;
  lemma_transcript_eq_from_checkpoint client server model5_r model4_c ch_r sh_r ch_c sh_c;
  assert (Seq.equal server_shared_r client_shared_c);
  assert (match
            model5_r.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret,
            model4_c.CS.model_handshake.CS.hs_keys.CS.ks_handshake_secret
          with
          | Some ss, Some cs -> Seq.equal ss cs
          | _, _ -> False);
  assert (Seq.equal model5_r.CS.model_handshake.CS.hs_transcript
                    model4_c.CS.model_handshake.CS.hs_transcript);
  // server covers + flight replay from _cr
  lemma_extract_server_covers_flight model5_r server_rr' server_rr after_server_flight_r
    e5_r e6_r ee_r cert_r cv_r sf_r server_flight_sent_r server_flight_received_r;
  // STEP 1: install-adjacent alignment
  lemma_hole3_alignment_covers model5_r server_rr' server_rr e5_r e6_r
    model4_c client_after_e4_c client_after_installs_c e4_c e5_c;
  // client [e4;e5] and six segments (rewrite explicit tail into cf_six ++ tail form)
  lemma_client_suffix_append_form model4_c client.CS.cs_model
    e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c
    suffix_sent_c suffix_received_c;
  lemma_extract_client_two_six model4_c client_after_e4_c client_after_installs_c c_after3
    client.CS.cs_model e4_c e5_c ee_c cert_c peer_c cv_c sf_c tail_c
    suffix_sent_c suffix_received_c;
  // client walk: client_after_installs_c -> c_after3 (writer), receiver = server_rr
  lemma_cf_client_walk client_after_installs_c server_rr c_after3 ee_c cert_c peer_c cv_c sf_c;
  // server walk: server_rr -> after_server_flight_r (reader), sender = c_after3
  lemma_cf_server_walk c_after3 server_rr after_server_flight_r ee_r cert_r cv_r sf_r
#pop-options

#push-options "--z3rlimit 20 --fuel 16 --ifuel 2"
let lemma_client_prefix_append_form
  (initial model12:CS.connection_model)
  (start:CS.handshake_start) (ch:GCH.clientHello) (sh:GSH.serverHello) (client_shared:C.x25519_shared_secret)
  (e4 e5:CS.conn_event) (ee:GEE.encryptedExtensions) (cert:GCert.certificate) (peer:X.peer_identity)
  (cv:GCV.certificateVerify) (sf:GFin.finished) (prefix_sent prefix_received:B.bytes)
  : Lemma
      (requires
        CS.conn_events_sent_seal_replay initial
          (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh); }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
           e4 :: e5 ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert); }) ::
           CS.ConnLocalEvent (CS.LocalValidateCertificate peer) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv); }) ::
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf); }) ::
           [])
          prefix_sent prefix_received model12)
      (ensures
        CS.conn_events_sent_seal_replay initial
          (L.append (PWSeg.client_cleartext_handshake_prefix_events start ch sh client_shared)
                    (L.append [e4; e5] (cf_six ee cert peer cv sf)))
          prefix_sent prefix_received model12)
= ()
#pop-options

#push-options "--z3rlimit 30 --fuel 16 --ifuel 2 --split_queries always"
let lemma_cf_client_identity
  (client:CS.connection_state)
  (initial model4_c client_after_e4_c client_after_installs_c c_after3 model12_ex:CS.connection_model)
  // recon witnesses
  (start_x:CS.handshake_start) (ch_x:GCH.clientHello) (sh_x:GSH.serverHello) (shared_x:C.x25519_shared_secret)
  (e4_x e5_x:CS.conn_event) (ee_x:GEE.encryptedExtensions) (cert_x:GCert.certificate) (peer_x:X.peer_identity)
  (cv_x:GCV.certificateVerify) (sf_x:GFin.finished) (e13_x e14_x:CS.conn_event) (cf_x:GFin.finished)
  // _cc witnesses
  (start_c:CS.handshake_start) (ch_c:GCH.clientHello) (sh_c:GSH.serverHello) (shared_c:C.x25519_shared_secret)
  (e4_c e5_c:CS.conn_event) (ee_c:GEE.encryptedExtensions) (cert_c:GCert.certificate) (peer_c:X.peer_identity)
  (cv_c:GCV.certificateVerify) (sf_c:GFin.finished) (e13_c e14_c:CS.conn_event) (cf_c:GFin.finished)
  (ps pr ps1 pr1 ss sr:B.bytes)
  : Lemma
      (requires
        // recon sent prefix replay over 12 recon events (EXPLICIT-12 form)
        CS.conn_events_sent_seal_replay initial
          (CS.ConnLocalEvent (CS.LocalStartHandshake start_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch_x); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh_x); }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared_x) ::
           e4_x :: e5_x ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_x); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_x); }) ::
           CS.ConnLocalEvent (CS.LocalValidateCertificate peer_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_x); }) ::
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_x); }) ::
           [])
          ps pr model12_ex /\
        // recon log-eq (16 recon events, EXPLICIT-16 form)
        client.CS.cs_event_log ==
          (CS.ConnLocalEvent (CS.LocalStartHandshake start_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch_x); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh_x); }) ::
           CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared_x) ::
           e4_x :: e5_x ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_x); }) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_x); }) ::
           CS.ConnLocalEvent (CS.LocalValidateCertificate peer_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_x); }) ::
           CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_x) ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_x); }) ::
           CS.ConnLocalEvent (CS.LocalVerifyFinished sf_x) ::
           e13_x :: e14_x ::
           CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_x); }) ::
           []) /\
        // _cc log-eq (literal ordered_rest form)
        client.CS.cs_event_log ==
          L.append (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c shared_c)
            (e4_c :: e5_c ::
             [
               CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
               CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
               CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
               CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
               CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
               CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
               CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
               e13_c; e14_c;
               CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
             ]) /\
        // segment 1: prefix received
        CS.conn_events_received_decode_replay initial
          (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c shared_c) ps1 pr1 model4_c /\
        // suffix received (literal ordered_rest form)
        CS.conn_events_received_decode_replay model4_c
          (e4_c :: e5_c ::
           [
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); };
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); };
             CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); };
             CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
             CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); };
             CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
             e13_c; e14_c;
             CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); }
           ])
          ss sr client.CS.cs_model /\
        // step facts + c_after3 defn
        CS.step_model model4_c e4_c == Some client_after_e4_c /\
        CS.step_model client_after_e4_c e5_c == Some client_after_installs_c /\
        c_after3 ==
          step_next
            (step_next
              (step_next
                (step_next
                  (step_next
                    (step_next client_after_installs_c
                      (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c); }))
                    (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_c); }))
                  (CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c)))
                (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c); }))
              (CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c)))
            (CS.ConnNetworkEvent { CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_c); }))
      (ensures model12_ex == c_after3)
=
  // convert recon prefix replay to append form
  lemma_client_prefix_append_form initial model12_ex start_x ch_x sh_x shared_x
    e4_x e5_x ee_x cert_x peer_x cv_x sf_x ps pr;
  // injectivity: _x == _c on the 12-event prefix
  assert (L.append (PWSeg.client_cleartext_handshake_prefix_events start_x ch_x sh_x shared_x)
                    (L.append [e4_x; e5_x] (cf_six ee_x cert_x peer_x cv_x sf_x))
          == L.append (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c shared_c)
                    (L.append [e4_c; e5_c] (cf_six ee_c cert_c peer_c cv_c sf_c)));
  // convert suffix to append form and extract segments 2,3
  lemma_client_suffix_append_form model4_c client.CS.cs_model
    e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c ss sr;
  lemma_extract_client_two_six model4_c client_after_e4_c client_after_installs_c c_after3
    client.CS.cs_model e4_c e5_c ee_c cert_c peer_c cv_c sf_c
    [ CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c); e13_c; e14_c;
      CS.ConnNetworkEvent { CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_c); } ]
    ss sr;
  eliminate exists a2 b2. CS.conn_events_received_decode_replay model4_c [e4_c; e5_c] a2 b2 client_after_installs_c
  returns model12_ex == c_after3
  with _.
  (
    eliminate exists a3 b3. CS.conn_events_received_decode_replay client_after_installs_c (cf_six ee_c cert_c peer_c cv_c sf_c) a3 b3 c_after3
    returns model12_ex == c_after3
    with _.
    (
      lemma_client_identity_determinism initial model4_c client_after_installs_c c_after3 model12_ex
        (PWSeg.client_cleartext_handshake_prefix_events start_c ch_c sh_c shared_c)
        [e4_c; e5_c] (cf_six ee_c cert_c peer_c cv_c sf_c)
        ps pr ps1 pr1 a2 b2 a3 b3
    )
  )
#pop-options


#push-options "--z3rlimit 60 --split_queries always"
let lemma_installed_protected_projection_replay_witnesses_from_milestones_and_hello_key_shares
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        clean16_staged_boundary_derivation_milestones client server /\
        WFL.paired_cleartext_hello_key_shares client server)
      (ensures
        PNTPPD.installed_protected_projection_replay_witnesses client server)
=
    // ---- Bring the canonical + ClientFinished milestone slices into scope ----
    assert (PNTSFR.server_post_server_hello_canonical_handshake_installs_sent_seal_replay_slice server);
    assert (PNTSFR.client_post_derive_ordered_received_decode_replay_slice client);
    assert (PNTCFRR.server_client_finished_received_decode_suffix_replay_slice server);
    lemma_clean16_staged_boundary_derivation_milestones_client_finished_canonical_sent_seal_replay_slice
      client server;
    assert (PNTCFR.client_finished_canonical_sent_seal_replay_slice client);
    eliminate exists
      (ch_s:GCH.clientHello)
      (selection_s:CS.server_handshake_selection)
      (server_shared_s:C.x25519_shared_secret)
      (sh_s:GSH.serverHello)
      (ee_s:GEE.encryptedExtensions)
      (cert_s:GCert.certificate)
      (cv_s:GCV.certificateVerify)
      (sf_s:GFin.finished)
      (cf_s:GFin.finished)
      (server_material_s:CS.traffic_key_material)
      (server_read_material_s:CS.traffic_key_material)
      (server_app_write_material_s:CS.traffic_key_material)
      (server_app_read_material_s:CS.traffic_key_material)
      (model5_s:CS.connection_model)
      (server_after_write_s:CS.connection_model)
      (server_after_read_s:CS.connection_model)
      (prefix_sent_s:B.bytes)
      (prefix_received_s:B.bytes)
      (suffix_sent_s:B.bytes)
      (suffix_received_s:B.bytes).
      (let server_write_install =
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficWrite;
              CS.install_material = server_material_s;
            };
          }) in
      let server_read_install =
        CS.ConnLocalEvent
          (CS.LocalInstallTrafficKeysForRole {
            CS.install_role = CS.ServerEndpoint;
            CS.install_payload = {
              CS.install_epoch = CS.TrafficHandshake;
              CS.install_direction = CS.TrafficRead;
              CS.install_material = server_read_material_s;
            };
          }) in
      let ordered_rest =
        [
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_s);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Certificate cert_s);
          };
          CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_s);
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv_s);
          };
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished sf_s);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficWrite;
                CS.install_material = server_app_write_material_s;
              };
            });
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.Finished cf_s);
          };
          CS.ConnLocalEvent
            (CS.LocalInstallTrafficKeysForRole {
              CS.install_role = CS.ServerEndpoint;
              CS.install_payload = {
                CS.install_epoch = CS.TrafficApplication;
                CS.install_direction = CS.TrafficRead;
                CS.install_material = server_app_read_material_s;
              };
            });
          CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)
        ] in
      PNTSFR.server_post_server_hello_ordered_sent_seal_replay_slice server /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append prefix_sent_s suffix_sent_s) /\
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append prefix_received_s suffix_received_s) /\
      CS.conn_events_sent_seal_replay
        (CS.initial_model server.CS.cs_model.CS.model_config)
        (PWSeg.server_cleartext_handshake_prefix_events
          ch_s
          selection_s
          server_shared_s
          sh_s)
        prefix_sent_s
        prefix_received_s
        model5_s /\
      CS.step_model model5_s server_write_install == Some server_after_write_s /\
      CS.step_model server_after_write_s server_read_install == Some server_after_read_s /\
      CS.conn_events_sent_seal_replay
        model5_s
        (server_write_install :: server_read_install :: ordered_rest)
        suffix_sent_s
        suffix_received_s
        server.CS.cs_model)
    returns
      (PNTPPD.installed_protected_projection_replay_witnesses client server)
    with _sc.
    (
      assert (PNTSFR.client_post_derive_ordered_received_decode_replay_slice client);
      eliminate exists
        (start_c:CS.handshake_start)
        (ch_c:GCH.clientHello)
        (sh_c:GSH.serverHello)
        (client_shared_c:C.x25519_shared_secret)
        (e4_c:CS.conn_event)
        (e5_c:CS.conn_event)
        (ee_c:GEE.encryptedExtensions)
        (cert_c:GCert.certificate)
        (peer_c:X.peer_identity)
        (cv_c:GCV.certificateVerify)
        (sf_c:GFin.finished)
        (e13_c:CS.conn_event)
        (e14_c:CS.conn_event)
        (cf_c:GFin.finished)
        (model4_c:CS.connection_model)
        (prefix_sent_c:B.bytes)
        (prefix_received_c:B.bytes)
        (suffix_sent_c:B.bytes)
        (suffix_received_c:B.bytes).
        (let ordered_rest =
          [
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c);
            };
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Certificate cert_c);
            };
            CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c);
            };
            CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Received;
              CL.message_value = M.TlsHandshake (M.Finished sf_c);
            };
            CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
            e13_c;
            e14_c;
            CS.ConnNetworkEvent {
              CL.message_direction = CL.Sent;
              CL.message_value = M.TlsHandshake (M.Finished cf_c);
            }
          ] in
        client.CS.cs_event_log ==
          FStar.List.Tot.append
            (PWSeg.client_cleartext_handshake_prefix_events
              start_c
              ch_c
              sh_c
              client_shared_c)
            (e4_c :: e5_c :: ordered_rest) /\
        PCPS.client_no_tail_two_handshake_install_cover e4_c e5_c /\
        PNTCAS.client_no_tail_application_install_cover e13_c e14_c /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_sent
          (B.append prefix_sent_c suffix_sent_c) /\
        Seq.equal
          client.CS.cs_wire_log.CL.raw_received
          (B.append prefix_received_c suffix_received_c) /\
        CS.conn_events_received_decode_replay
          (CS.initial_model client.CS.cs_model.CS.model_config)
          (PWSeg.client_cleartext_handshake_prefix_events
            start_c
            ch_c
            sh_c
            client_shared_c)
          prefix_sent_c
          prefix_received_c
          model4_c /\
        CS.conn_events_received_decode_replay
          model4_c
          (e4_c :: e5_c :: ordered_rest)
          suffix_sent_c
          suffix_received_c
          client.CS.cs_model)
      returns
        (PNTPPD.installed_protected_projection_replay_witnesses client server)
      with _cc.
      (
        assert (PNTCFRR.server_client_finished_received_decode_suffix_replay_slice server);
        eliminate exists
          (ch_r:GCH.clientHello)
          (selection_r:CS.server_handshake_selection)
          (server_shared_r:C.x25519_shared_secret)
          (sh_r:GSH.serverHello)
          (e5_r:CS.conn_event)
          (e6_r:CS.conn_event)
          (ee_r:GEE.encryptedExtensions)
          (cert_r:GCert.certificate)
          (cv_r:GCV.certificateVerify)
          (sf_r:GFin.finished)
          (cf_r:GFin.finished)
          (server_app_write_material_r:CS.traffic_key_material)
          (server_app_read_material_r:CS.traffic_key_material)
          (model5_r:CS.connection_model)
          (after_server_flight_r:CS.connection_model)
          (prefix_sent_r:B.bytes)
          (prefix_received_r:B.bytes)
          (suffix_sent_r:B.bytes)
          (suffix_received_r:B.bytes)
          (server_flight_sent_r:B.bytes)
          (server_flight_received_r:B.bytes)
          (client_finished_sent_r:B.bytes)
          (client_finished_received_r:B.bytes).
          (let server_flight_prefix =
            [
              e5_r;
              e6_r;
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_r);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert_r);
              };
              CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_r);
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv_r);
              };
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf_r);
              }
            ] in
          let client_finished_suffix =
            [
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_app_write_material_r;
                  };
                });
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf_r);
              };
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_app_read_material_r;
                  };
                });
              CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_r)
            ] in
          server.CS.cs_event_log ==
            FStar.List.Tot.append
              (PWSeg.server_cleartext_handshake_prefix_events
                ch_r
                selection_r
                server_shared_r
                sh_r)
              (FStar.List.Tot.append server_flight_prefix client_finished_suffix) /\
          PNTSS.server_no_tail_two_handshake_install_cover e5_r e6_r /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_sent
            (B.append prefix_sent_r suffix_sent_r) /\
          Seq.equal
            server.CS.cs_wire_log.CL.raw_received
            (B.append prefix_received_r suffix_received_r) /\
          Seq.equal
            suffix_sent_r
            (B.append server_flight_sent_r client_finished_sent_r) /\
          Seq.equal
            suffix_received_r
            (B.append server_flight_received_r client_finished_received_r) /\
          CS.conn_events_received_decode_replay
            (CS.initial_model server.CS.cs_model.CS.model_config)
            (PWSeg.server_cleartext_handshake_prefix_events
              ch_r
              selection_r
              server_shared_r
              sh_r)
            prefix_sent_r
            prefix_received_r
            model5_r /\
          CS.conn_events_received_decode_replay
            model5_r
            server_flight_prefix
            server_flight_sent_r
            server_flight_received_r
            after_server_flight_r /\
          CS.conn_events_received_decode_replay
            after_server_flight_r
            client_finished_suffix
            client_finished_sent_r
            client_finished_received_r
            server.CS.cs_model)
        returns
          (PNTPPD.installed_protected_projection_replay_witnesses client server)
        with _cr.
        (
          assert (PNTCFR.client_finished_canonical_sent_seal_replay_slice client);
          eliminate exists
            (sf_f:GFin.finished)
            (cf_f:GFin.finished)
            (model12_f:CS.connection_model)
            (after_verify_f:CS.connection_model)
            (after_app_write_f:CS.connection_model)
            (after_app_read_f:CS.connection_model)
            (client_app_write_material_f:CS.traffic_key_material)
            (client_app_read_material_f:CS.traffic_key_material)
            (suffix_sent_f:B.bytes)
            (suffix_received_f:B.bytes).
            (CS.conn_events_sent_seal_replay
              model12_f
              (CS.ConnLocalEvent (CS.LocalVerifyFinished sf_f) ::
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeys {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficWrite;
                   CS.install_material = client_app_write_material_f;
                 }) ::
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeys {
                   CS.install_epoch = CS.TrafficApplication;
                   CS.install_direction = CS.TrafficRead;
                   CS.install_material = client_app_read_material_f;
                 }) ::
               CS.ConnNetworkEvent ({
                 CL.message_direction = CL.Sent;
                 CL.message_value = M.TlsHandshake (M.Finished cf_f);
               }) ::
               [])
              suffix_sent_f
              suffix_received_f
              client.CS.cs_model /\
            CS.step_model
              model12_f
              (CS.ConnLocalEvent (CS.LocalVerifyFinished sf_f)) == Some after_verify_f /\
            CS.step_model
              after_verify_f
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficWrite;
                  CS.install_material = client_app_write_material_f;
                })) == Some after_app_write_f /\
            CS.step_model
              after_app_write_f
              (CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeys {
                  CS.install_epoch = CS.TrafficApplication;
                  CS.install_direction = CS.TrafficRead;
                  CS.install_material = client_app_read_material_f;
                })) == Some after_app_read_f /\
            CS.step_model
              after_app_read_f
              (CS.ConnNetworkEvent ({
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished cf_f);
              })) == Some client.CS.cs_model /\
            CS.raw_records_exactly suffix_sent_f T.Application_data 1)
          returns
            (PNTPPD.installed_protected_projection_replay_witnesses client server)
          with _cf.
          (
            lemma_h4_client_exact_recon client server;
            let goal_w : prop = PNTPPD.installed_protected_projection_replay_witnesses client server in
            eliminate exists (model12_ex:CS.connection_model) (sf_ex cf_ex:GFin.finished)
               (cawm_ex carm_ex:CS.traffic_key_material) (av_ex aw_ex ar_ex:CS.connection_model)
               (suffix_sent_ex suffix_received_ex prefix_sent_ex frag_ex:B.bytes)
               (start_ex:CS.handshake_start) (ch_ex:GCH.clientHello) (sh_ex:GSH.serverHello) (client_shared_ex:C.x25519_shared_secret)
               (e4_ex e5_ex:CS.conn_event) (ee_ex:GEE.encryptedExtensions) (cert_ex:GCert.certificate) (peer_ex:X.peer_identity)
               (cv_ex:GCV.certificateVerify) (e13_ex e14_ex:CS.conn_event) (prefix_received_ex:B.bytes).
               (Seq.equal client.CS.cs_wire_log.CL.raw_sent (B.append prefix_sent_ex suffix_sent_ex) /\
                W.parse_record_wire prefix_sent_ex == Some (T.Handshake, frag_ex, B.length prefix_sent_ex) /\
                CS.step_model model12_ex (ev_vf_of sf_ex) == Some av_ex /\
                CS.step_model av_ex (iaw cawm_ex) == Some aw_ex /\
                CS.step_model aw_ex (iar carm_ex) == Some ar_ex /\
                CS.step_model ar_ex (ev_sent_of cf_ex) == Some client.CS.cs_model /\
                CS.conn_events_sent_seal_replay model12_ex
                  (ev_vf_of sf_ex :: iaw cawm_ex :: iar carm_ex :: ev_sent_of cf_ex :: [])
                  suffix_sent_ex suffix_received_ex client.CS.cs_model /\
                CS.conn_events_sent_seal_replay
                  (CS.initial_model client.CS.cs_model.CS.model_config)
                  (CS.ConnLocalEvent (CS.LocalStartHandshake start_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch_ex); }) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared_ex) ::
                   e4_ex :: e5_ex ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_ex); }) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalValidateCertificate peer_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_ex); }) ::
                   [])
                  prefix_sent_ex prefix_received_ex model12_ex /\
                client.CS.cs_event_log ==
                  (CS.ConnLocalEvent (CS.LocalStartHandshake start_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.ClientHello ch_ex); }) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.ServerHello sh_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared_ex) ::
                   e4_ex :: e5_ex ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_ex); }) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Certificate cert_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalValidateCertificate peer_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.CertificateVerify cv_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_ex) ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Received; CL.message_value = M.TlsHandshake (M.Finished sf_ex); }) ::
                   CS.ConnLocalEvent (CS.LocalVerifyFinished sf_ex) ::
                   e13_ex :: e14_ex ::
                   CS.ConnNetworkEvent ({ CL.message_direction = CL.Sent; CL.message_value = M.TlsHandshake (M.Finished cf_ex); }) ::
                   []))
            returns goal_w
            with _exrec.
            (
            let ordered_rest_s =
              [
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_s);
                };
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.Certificate cert_s);
                };
                CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_s);
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.CertificateVerify cv_s);
                };
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.Finished sf_s);
                };
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficWrite;
                      CS.install_material = server_app_write_material_s;
                    };
                  });
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.Finished cf_s);
                };
                CS.ConnLocalEvent
                  (CS.LocalInstallTrafficKeysForRole {
                    CS.install_role = CS.ServerEndpoint;
                    CS.install_payload = {
                      CS.install_epoch = CS.TrafficApplication;
                      CS.install_direction = CS.TrafficRead;
                      CS.install_material = server_app_read_material_s;
                    };
                  });
                CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)
              ] in
            let server_write_install =
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficHandshake;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_material_s;
                  };
                }) in
            let server_read_install =
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficHandshake;
                    CS.install_direction = CS.TrafficRead;
                    CS.install_material = server_read_material_s;
                  };
                }) in
            peel_sent_bp model5_s server_write_install (server_read_install :: ordered_rest_s) suffix_sent_s suffix_received_s server.CS.cs_model;
            assert (step_next model5_s server_write_install == server_after_write_s);
            peel_sent_bp server_after_write_s server_read_install ordered_rest_s suffix_sent_s suffix_received_s server.CS.cs_model;
            assert (step_next server_after_write_s server_read_install == server_after_read_s);
            let srv_raw_sent = suffix_sent_s in
            let srv_raw_received = suffix_received_s in
            (
            let ordered_rest_c =
              [
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c);
                };
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.Certificate cert_c);
                };
                CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c);
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c);
                };
                CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c);
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Received;
                  CL.message_value = M.TlsHandshake (M.Finished sf_c);
                };
                CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
                e13_c;
                e14_c;
                CS.ConnNetworkEvent {
                  CL.message_direction = CL.Sent;
                  CL.message_value = M.TlsHandshake (M.Finished cf_c);
                }
              ] in
            lemma_two_install_events_are_local e4_c e5_c;
            peel_received_bp model4_c e4_c (e5_c :: ordered_rest_c) suffix_sent_c suffix_received_c client.CS.cs_model;
            let client_after_e4_c = step_next model4_c e4_c in
            peel_received_bp client_after_e4_c e5_c ordered_rest_c suffix_sent_c suffix_received_c client.CS.cs_model;
            let client_after_installs_c = step_next client_after_e4_c e5_c in
            let cli_raw_sent = suffix_sent_c in
            let cli_raw_received = suffix_received_c in
            (
            let ev_sent_ee =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_s);
              } in
            let ev_sent_cert =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Certificate cert_s);
              } in
            let ev_sign_cv = CS.ConnLocalEvent (CS.LocalSignCertificateVerify cv_s) in
            let ev_sent_cv =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv_s);
              } in
            let ev_sent_sf =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.Finished sf_s);
              } in
            let s_after0 = step_next server_after_read_s ev_sent_ee in
            let s_after1 = step_next s_after0 ev_sent_cert in
            let s_after_auth = step_next s_after1 ev_sign_cv in
            let s_after2 = step_next s_after_auth ev_sent_cv in
            let s_after3 = step_next s_after2 ev_sent_sf in
            let ev_recv_ee =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.EncryptedExtensions ee_c);
              } in
            let ev_recv_cert =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Certificate cert_c);
              } in
            let ev_validate = CS.ConnLocalEvent (CS.LocalValidateCertificate peer_c) in
            let ev_recv_cv =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv_c);
              } in
            let ev_verify_cert = CS.ConnLocalEvent (CS.LocalVerifyCertificateSignature cv_c) in
            let ev_recv_sf =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished sf_c);
              } in
            let c_after0 = step_next client_after_installs_c ev_recv_ee in
            let c_after1 = step_next c_after0 ev_recv_cert in
            let c_after_auth = step_next c_after1 ev_validate in
            let c_after2 = step_next c_after_auth ev_recv_cv in
            let c_after_verify = step_next c_after2 ev_verify_cert in
            let c_after3 = step_next c_after_verify ev_recv_sf in
            let ev_install_app_write_forrole =
              CS.ConnLocalEvent
                (CS.LocalInstallTrafficKeysForRole {
                  CS.install_role = CS.ServerEndpoint;
                  CS.install_payload = {
                    CS.install_epoch = CS.TrafficApplication;
                    CS.install_direction = CS.TrafficWrite;
                    CS.install_material = server_app_write_material_r;
                  };
                }) in
            let ev_recv_cf_r =
              CS.ConnNetworkEvent {
                CL.message_direction = CL.Received;
                CL.message_value = M.TlsHandshake (M.Finished cf_r);
              } in
            let cf_srv_after_app_write = step_next after_server_flight_r ev_install_app_write_forrole in
            let cf_srv_after_finished = step_next cf_srv_after_app_write ev_recv_cf_r in
            // ---- Peel step facts along the server flight ----
            peel_sent server_after_read_s ev_sent_ee
              [ev_sent_cert; ev_sign_cv; ev_sent_cv; ev_sent_sf;
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeysForRole {
                   CS.install_role = CS.ServerEndpoint;
                   CS.install_payload = {
                     CS.install_epoch = CS.TrafficApplication;
                     CS.install_direction = CS.TrafficWrite;
                     CS.install_material = server_app_write_material_s;
                   };
                 });
               CS.ConnNetworkEvent {
                 CL.message_direction = CL.Received;
                 CL.message_value = M.TlsHandshake (M.Finished cf_s);
               };
               CS.ConnLocalEvent
                 (CS.LocalInstallTrafficKeysForRole {
                   CS.install_role = CS.ServerEndpoint;
                   CS.install_payload = {
                     CS.install_epoch = CS.TrafficApplication;
                     CS.install_direction = CS.TrafficRead;
                     CS.install_material = server_app_read_material_s;
                   };
                 });
               CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)]
              server.CS.cs_model;
            let w : PNTPPD.installed_protected_projection_replay_witness_pack = {
              PNTPPD.ippr_server_flight_sender = server_after_read_s;
              PNTPPD.ippr_server_flight_receiver = client_after_installs_c;
              PNTPPD.ippr_server_after0 = s_after0;
              PNTPPD.ippr_client_after0 = c_after0;
              PNTPPD.ippr_server_after1 = s_after1;
              PNTPPD.ippr_client_after1 = c_after1;
              PNTPPD.ippr_server_after_auth_skip = s_after_auth;
              PNTPPD.ippr_client_after_auth_skip = c_after_auth;
              PNTPPD.ippr_server_after2 = s_after2;
              PNTPPD.ippr_client_after2 = c_after2;
              PNTPPD.ippr_client_after_verify_skip = c_after_verify;
              PNTPPD.ippr_server_after3 = s_after3;
              PNTPPD.ippr_client_after3 = c_after3;
              PNTPPD.ippr_server_auth_skip = CS.LocalSignCertificateVerify cv_s;
              PNTPPD.ippr_client_auth_skip = CS.LocalValidateCertificate peer_c;
              PNTPPD.ippr_client_verify_skip = CS.LocalVerifyCertificateSignature cv_c;
              PNTPPD.ippr_sent_msg0 = M.EncryptedExtensions ee_s;
              PNTPPD.ippr_received_msg0 = M.EncryptedExtensions ee_c;
              PNTPPD.ippr_sent_msg1 = M.Certificate cert_s;
              PNTPPD.ippr_received_msg1 = M.Certificate cert_c;
              PNTPPD.ippr_sent_msg2 = M.CertificateVerify cv_s;
              PNTPPD.ippr_received_msg2 = M.CertificateVerify cv_c;
              PNTPPD.ippr_sent_msg3 = M.Finished sf_s;
              PNTPPD.ippr_received_msg3 = M.Finished sf_c;
              PNTPPD.ippr_server_rest =
                [
                  CS.ConnLocalEvent
                    (CS.LocalInstallTrafficKeysForRole {
                      CS.install_role = CS.ServerEndpoint;
                      CS.install_payload = {
                        CS.install_epoch = CS.TrafficApplication;
                        CS.install_direction = CS.TrafficWrite;
                        CS.install_material = server_app_write_material_s;
                      };
                    });
                  CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.Finished cf_s);
                  };
                  CS.ConnLocalEvent
                    (CS.LocalInstallTrafficKeysForRole {
                      CS.install_role = CS.ServerEndpoint;
                      CS.install_payload = {
                        CS.install_epoch = CS.TrafficApplication;
                        CS.install_direction = CS.TrafficRead;
                        CS.install_material = server_app_read_material_s;
                      };
                    });
                  CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_s)
                ];
              PNTPPD.ippr_client_rest =
                [
                  CS.ConnLocalEvent (CS.LocalVerifyFinished sf_c);
                  e13_c;
                  e14_c;
                  CS.ConnNetworkEvent {
                    CL.message_direction = CL.Sent;
                    CL.message_value = M.TlsHandshake (M.Finished cf_c);
                  }
                ];
              PNTPPD.ippr_server_raw_sent = srv_raw_sent;
              PNTPPD.ippr_server_raw_received = srv_raw_received;
              PNTPPD.ippr_client_raw_sent = cli_raw_sent;
              PNTPPD.ippr_client_raw_received = cli_raw_received;
              PNTPPD.ippr_server_final = server.CS.cs_model;
              PNTPPD.ippr_client_final = client.CS.cs_model;
              PNTPPD.ippr_client_finished_sender = model12_ex;
              PNTPPD.ippr_client_finished_receiver = after_server_flight_r;
              PNTPPD.ippr_cf_client_after_verify = av_ex;
              PNTPPD.ippr_cf_client_after_app_write = aw_ex;
              PNTPPD.ippr_cf_client_after_app_read = ar_ex;
              PNTPPD.ippr_cf_server_after_app_write = cf_srv_after_app_write;
              PNTPPD.ippr_cf_client_after_finished = client.CS.cs_model;
              PNTPPD.ippr_cf_server_after_finished = cf_srv_after_finished;
              PNTPPD.ippr_verified_server_finished = sf_ex;
              PNTPPD.ippr_client_app_write_material = cawm_ex;
              PNTPPD.ippr_client_app_read_material = carm_ex;
              PNTPPD.ippr_server_app_write_material = server_app_write_material_r;
              PNTPPD.ippr_sent_msg4 = M.Finished cf_ex;
              PNTPPD.ippr_received_msg4 = M.Finished cf_r;
              PNTPPD.ippr_client_finished_rest = [];
              PNTPPD.ippr_server_finished_rest =
                [
                  CS.ConnLocalEvent
                    (CS.LocalInstallTrafficKeysForRole {
                      CS.install_role = CS.ServerEndpoint;
                      CS.install_payload = {
                        CS.install_epoch = CS.TrafficApplication;
                        CS.install_direction = CS.TrafficRead;
                        CS.install_material = server_app_read_material_r;
                      };
                    });
                  CS.ConnLocalEvent (CS.LocalVerifyClientFinished cf_r)
                ];
              PNTPPD.ippr_client_finished_raw_sent = suffix_sent_ex;
              PNTPPD.ippr_client_finished_raw_received = suffix_received_ex;
              PNTPPD.ippr_server_finished_raw_sent = client_finished_sent_r;
              PNTPPD.ippr_server_finished_raw_received = client_finished_received_r;
              PNTPPD.ippr_client_finished_final = client.CS.cs_model;
              PNTPPD.ippr_server_finished_final = server.CS.cs_model;
            } in
            introduce exists (w0:PNTPPD.installed_protected_projection_replay_witness_pack).
              PNTPPD.installed_protected_projection_replay_pack_inputs client server w0
            with w
            and (
              // --- Message-match: field-track the two canonical flights ---
              lemma_server_flight_walk server_after_read_s ee_s cert_s cv_s sf_s cf_s
                server_app_write_material_s server_app_read_material_s server.CS.cs_model;
              lemma_client_flight_walk client_after_installs_c ee_c cert_c peer_c cv_c sf_c cf_c
                e13_c e14_c client.CS.cs_model;
              // server.hs_client_finished == Some cf_r (cross-flight, from CFRR suffix)
              lemma_cfrr_suffix_walk after_server_flight_r
                server_app_write_material_r server_app_read_material_r cf_r server.CS.cs_model;
              // client.hs_client_finished == Some cf_f (cross-flight, from CF slice sent finished)
              lemma_sent_finished_at_appdata_sets_client_finished ar_ex client.CS.cs_model cf_ex;
              // --- Hard conjuncts (alignments + byte pairings) ---
              // ---- Hole 1: server-write / client-read handshake install alignment ----
              lemma_pack_server_flight_align_real client server ch_s selection_s server_shared_s sh_s
                ee_s cert_s cv_s sf_s cf_s
                server_material_s server_read_material_s server_app_write_material_s server_app_read_material_s
                model5_s server_after_write_s server_after_read_s
                start_c ch_c sh_c client_shared_c
                ee_c cert_c peer_c cv_c sf_c cf_c
                e4_c e5_c e13_c e14_c
                model4_c client_after_e4_c client_after_installs_c;
              // ---- Hole 2: server-sent / client-received suffix byte equality ----
              assert (PNTSFS.clean16_server_encrypted_flight_staged_milestone client server);
              assert (CS.paired_wire_logs client server);
              lemma_pack_server_bytes_real client server ch_s selection_s server_shared_s sh_s
                ee_s cert_s cv_s sf_s cf_s
                server_material_s server_read_material_s server_app_write_material_s server_app_read_material_s
                model5_s prefix_sent_s prefix_received_s suffix_sent_s suffix_received_s
                start_c ch_c sh_c client_shared_c
                e4_c e5_c ee_c cert_c peer_c cv_c sf_c e13_c e14_c cf_c
                model4_c prefix_sent_c prefix_received_c suffix_received_c;
              // ---- Hole 3: client-write / server-read handshake install alignment ----
              lemma_cf_client_identity client
                (CS.initial_model client.CS.cs_model.CS.model_config)
                model4_c client_after_e4_c client_after_installs_c c_after3 model12_ex
                start_ex ch_ex sh_ex client_shared_ex e4_ex e5_ex ee_ex cert_ex peer_ex cv_ex sf_ex e13_ex e14_ex cf_ex
                start_c ch_c sh_c client_shared_c e4_c e5_c ee_c cert_c peer_c cv_c sf_c e13_c e14_c cf_c
                prefix_sent_ex prefix_received_ex prefix_sent_c prefix_received_c suffix_sent_c suffix_received_c;
              lemma_pack_cf_align_core client server ch_r selection_r server_shared_r sh_r
                e5_r e6_r ee_r cert_r cv_r sf_r cf_r server_app_write_material_r server_app_read_material_r
                model5_r after_server_flight_r server_flight_sent_r server_flight_received_r
                start_c ch_c sh_c client_shared_c e4_c e5_c e13_c e14_c ee_c cert_c peer_c cv_c sf_c cf_c
                model4_c client_after_e4_c client_after_installs_c c_after3
                suffix_sent_c suffix_received_c;
              assert (PWL.write_read_record_material_aligned model12_ex after_server_flight_r);
              // ---- HOLE 4 (closed): client-finished suffix byte equality ----
              // suffix_sent_ex (stream-tied client-finished record) == client_finished_received_r
              lemma_server_prefix_received_ch
                (CS.initial_model server.CS.cs_model.CS.model_config)
                ch_r selection_r server_shared_r sh_r
                prefix_sent_r prefix_received_r model5_r;
              lemma_received_client_hello_is_wire_h4 ch_r prefix_received_r;
              eliminate exists frag2.
                W.parse_record_wire prefix_received_r == Some (T.Handshake, frag2, B.length prefix_received_r)
              returns (Seq.equal suffix_sent_ex client_finished_received_r)
              with _w2.
              (
                // server flight received bytes are empty
                lemma_server_flight_received_empty model5_r e5_r e6_r ee_r cert_r cv_r sf_r
                  server_flight_sent_r server_flight_received_r after_server_flight_r;
                Seq.lemma_eq_elim server_flight_received_r B.empty;
                append_empty_left client_finished_received_r;
                Seq.lemma_eq_elim
                  (B.append server_flight_received_r client_finished_received_r)
                  client_finished_received_r;
                Seq.lemma_eq_elim suffix_received_r client_finished_received_r;
                // S == server.raw_received == prefix_received_r ++ suffix_received_r
                //   == prefix_received_r ++ client_finished_received_r
                assert (CS.paired_wire_logs client server);
                Seq.lemma_eq_elim
                  client.CS.cs_wire_log.CL.raw_sent
                  server.CS.cs_wire_log.CL.raw_received;
                Seq.lemma_eq_elim
                  server.CS.cs_wire_log.CL.raw_received
                  (B.append prefix_received_r suffix_received_r);
                Seq.lemma_eq_elim
                  (B.append prefix_received_r suffix_received_r)
                  (B.append prefix_received_r client_finished_received_r);
                // client side split (from packaging bundle):
                //   S == prefix_sent_ex ++ suffix_sent_ex
                // first-wire-record uniqueness pins suffix_sent_ex == client_finished_received_r
                lemma_first_wire_record_unique_split_h4
                  client.CS.cs_wire_log.CL.raw_sent
                  prefix_sent_ex suffix_sent_ex
                  prefix_received_r client_finished_received_r
                  T.Handshake T.Handshake frag_ex frag2
              );
              // Bring the 10 final message-field facts into context (from the walks/inversions)
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_s);
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert_s);
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv_s);
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf_s);
              assert (server.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf_r);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_encrypted_extensions == Some ee_c);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_certificate == Some cert_c);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify == Some cv_c);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_server_finished == Some sf_c);
              assert (client.CS.cs_model.CS.model_handshake.CS.hs_client_finished == Some cf_ex);
              // Isolate the message-match conjunct (clean-context helper)
              lemma_message_match client server ee_s cert_s cv_s sf_s cf_r ee_c cert_c cv_c sf_c cf_ex;
              assert (PNTPPD.installed_protected_projection_replay_pack_inputs client server w)
            )
            )
            )
            )
          )
        )
      )
    )

let lemma_paired_protected_witnesses_from_clean16_valid_byte_traces_and_hello_key_shares
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
          client_initial server_initial client server
          client_received client_sent server_received server_sent /\
        WFL.paired_cleartext_hello_key_shares client server)
      (ensures
        Pairing.paired_protected_handshake_event_projection_pair_witnesses client server)
=
  lemma_clean16_no_tail_valid_byte_traces_staged_boundary_derivation_milestones
    client_initial server_initial client server
    client_received client_sent server_received server_sent;
  lemma_installed_protected_projection_replay_witnesses_from_milestones_and_hello_key_shares
    client server;
  PNTPPD.lemma_pairing_protected_projection_witnesses_from_installed_replay_witnesses
    client server
#pop-options
