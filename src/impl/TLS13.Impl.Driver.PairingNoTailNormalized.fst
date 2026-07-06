module TLS13.Impl.Driver.PairingNoTailNormalized

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CVE = TLS13.ConnectionState.ClientCertificateVerifyEvent
module PBridge = TLS13.Impl.Driver.PairingNormalizedBridge
module Pairing = TLS13.Impl.Driver.Pairing
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNS = TLS13.Impl.Driver.PairingNormalizedShape
module PNT = TLS13.Impl.Driver.PairingNoTail
module PNTCPrS = TLS13.Impl.Driver.PairingNoTailClientProtectedShape
module PNTCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTCS = TLS13.Impl.Driver.PairingNoTailClientShape
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PNTRB = TLS13.Impl.Driver.PairingNoTailRawBridge
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module Seq = FStar.Seq
module SM = Common.StateMachine
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module WFL = TLS13.Spec.WireFormatLemmas

let lemma_clean_no_tail_valid_byte_traces_preserve_connection_state_consistent
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.connection_state_consistent client /\
        CS.connection_state_consistent server)
=
  assert (CS.connection_state_consistent client_initial);
  assert (CS.connection_state_consistent server_initial);
  PNT.lemma_client_valid_byte_trace_preserves_connection_state_consistent
    client_initial
    client
    client_received
    client_sent
    Seq.empty;
  PNT.lemma_server_valid_byte_trace_preserves_connection_state_consistent
    server_initial
    server
    server_received
    server_sent
    Seq.empty

let lemma_clean16_no_tail_valid_byte_traces_preserve_connection_state_consistent
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.connection_state_consistent client /\
        CS.connection_state_consistent server)
=
  assert (CS.connection_state_consistent client_initial);
  assert (CS.connection_state_consistent server_initial);
  PNT.lemma_client_valid_byte_trace_preserves_connection_state_consistent
    client_initial
    client
    client_received
    client_sent
    Seq.empty;
  PNT.lemma_server_valid_byte_trace_preserves_connection_state_consistent
    server_initial
    server
    server_received
    server_sent
    Seq.empty

let lemma_clean16_no_tail_valid_byte_traces_preserve_connection_state_replay_consistent
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.connection_state_sent_seal_replay_consistent client /\
        CS.connection_state_received_decode_replay_consistent client /\
        CS.connection_state_sent_seal_replay_consistent server /\
        CS.connection_state_received_decode_replay_consistent server)
=
  CSL.lemma_initial_sent_seal_replay_consistent
    client_initial.CS.cs_model.CS.model_config;
  CSL.lemma_initial_received_decode_replay_consistent
    client_initial.CS.cs_model.CS.model_config;
  assert (CS.connection_state_sent_seal_replay_consistent client_initial);
  assert (CS.connection_state_received_decode_replay_consistent client_initial);
  CSL.lemma_initial_sent_seal_replay_consistent
    server_initial.CS.cs_model.CS.model_config;
  CSL.lemma_initial_received_decode_replay_consistent
    server_initial.CS.cs_model.CS.model_config;
  assert (CS.connection_state_sent_seal_replay_consistent server_initial);
  assert (CS.connection_state_received_decode_replay_consistent server_initial);
  PNT.lemma_client_valid_byte_trace_preserves_connection_state_replay_consistent
    client_initial
    client
    client_received
    client_sent
    Seq.empty;
  PNT.lemma_server_valid_byte_trace_preserves_connection_state_replay_consistent
    server_initial
    server
    server_received
    server_sent
    Seq.empty

let lemma_clean16_no_tail_valid_byte_traces_role_local_start_spine16
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures paired_no_tail_role_local_start_spine16 client server)
=
  PNTCS.lemma_client_no_tail_start_spine client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_start_spine16
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_two_handshake_installs_server_start_spine16
          client
          server)
=
  PNTCPS.lemma_client_no_tail_fifth_and_sixth_events_handshake_traffic_install_clean
    client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_handshake_install_cover_server_start_spine16
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_handshake_install_cover_server_start_spine16
          client
          server)
=
  PNTCPS.lemma_client_no_tail_fifth_and_sixth_events_handshake_install_cover_clean
    client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_first_protected_receive_server_start_spine16
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_first_protected_receive_server_start_spine16
          client
          server)
=
  PNTCPrS.lemma_client_no_tail_seventh_event_encrypted_extensions_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_second_protected_receive_server_start_spine16
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_second_protected_receive_server_start_spine16
          client
          server)
=
  PNTCPrS.lemma_client_no_tail_eighth_event_certificate_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_client_certificate_verify_witness
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures Some? client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify)
=
  PNTCS.lemma_client_no_tail_certificate_verify_witness client

let lemma_clean16_no_tail_valid_byte_traces_client_received_certificate_verify_event
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures CVE.contains_received_certificate_verify client.CS.cs_event_log)
=
  lemma_clean16_no_tail_valid_byte_traces_preserve_connection_state_consistent
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (CS.connection_state_consistent client);
  assert (client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
  assert (client.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  CVE.lemma_client_application_ready_received_certificate_verify_event client

let lemma_clean16_no_tail_valid_byte_traces_client_received_certificate_verify_event_split
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures client_received_certificate_verify_event_split client)
=
  lemma_clean16_no_tail_valid_byte_traces_client_received_certificate_verify_event
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  CVE.lemma_contains_received_certificate_verify_split client.CS.cs_event_log

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_start_spine16_and_client_certificate_verify_witness
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_two_handshake_installs_server_start_spine16_and_client_certificate_verify_witness
          client
          server)
=
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_start_spine16
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCS.lemma_client_no_tail_certificate_verify_witness client

let lemma_clean_no_tail_valid_byte_traces_role_local_start_and_final_witnesses
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_start_and_final_witnesses client server)
=
  PNTCS.lemma_client_no_tail_start_spine_and_final_model_witnesses client;
  PNTSS.lemma_server_no_tail_start_spine_and_final_model_witnesses server

let lemma_clean_no_tail_valid_byte_traces_role_local_cleartext_prefixes
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_cleartext_prefixes client server)
=
  PNTCS.lemma_client_no_tail_third_event_server_hello_clean client;
  PNTSS.lemma_server_no_tail_second_event_client_hello_clean server

let lemma_clean_no_tail_valid_byte_traces_role_local_client_shared_prefix
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_shared_prefix client server)
=
  PNTCS.lemma_client_no_tail_fourth_event_derive_shared_secret_clean client;
  PNTSS.lemma_server_no_tail_second_event_client_hello_clean server

let lemma_clean_no_tail_valid_byte_traces_role_local_client_shared_server_selection_prefix
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_shared_server_selection_prefix client server)
=
  PNTCS.lemma_client_no_tail_fourth_event_derive_shared_secret_clean client;
  PNTSS.lemma_server_no_tail_third_event_select_parameters_clean server

let lemma_clean_no_tail_valid_byte_traces_role_local_client_shared_server_shared_prefix
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_shared_server_shared_prefix client server)
=
  PNTCS.lemma_client_no_tail_fourth_event_derive_shared_secret_clean client;
  PNTSS.lemma_server_no_tail_fourth_event_derive_shared_secret_clean server

let lemma_clean_no_tail_valid_byte_traces_role_local_client_handshake_install_server_shared_prefix
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_handshake_install_server_shared_prefix
          client
          server)
=
  PNTCS.lemma_client_no_tail_fifth_event_handshake_traffic_install_clean client;
  PNTSS.lemma_server_no_tail_fourth_event_derive_shared_secret_clean server

let lemma_clean_no_tail_valid_byte_traces_role_local_client_handshake_install_server_hello_prefix
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_handshake_install_server_hello_prefix
          client
          server)
=
  PNTCS.lemma_client_no_tail_fifth_event_handshake_traffic_install_clean client;
  PNTSS.lemma_server_no_tail_fifth_event_server_hello_clean server

let lemma_clean_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_hello_prefix
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        paired_no_tail_role_local_client_two_handshake_installs_server_hello_prefix
          client
          server)
=
  PNTCPS.lemma_client_no_tail_fifth_and_sixth_events_handshake_traffic_install_clean
    client;
  PNTSS.lemma_server_no_tail_fifth_event_server_hello_clean server

let lemma_clean_no_tail_valid_byte_traces_client_supported_hello_profile
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures WFL.state_supported_client_hello_wire_profile client)
=
  lemma_clean_no_tail_valid_byte_traces_preserve_connection_state_consistent
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (CS.connection_state_consistent client);
  assert (CS.client_x25519_key_share_projection client);
  WFL.lemma_state_supported_client_hello_wire_profile_from_config client

let lemma_clean16_no_tail_valid_byte_traces_client_supported_hello_profile
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures WFL.state_supported_client_hello_wire_profile client)
=
  lemma_clean16_no_tail_valid_byte_traces_preserve_connection_state_consistent
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (CS.connection_state_consistent client);
  assert (CS.client_x25519_key_share_projection client);
  WFL.lemma_state_supported_client_hello_wire_profile_from_config client

let lemma_valid_byte_traces_invert_to_paired_serialized_traces_common
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
        WFSM.valid_byte_trace
          (ClientCP.client_system client_initial)
          client_received
          client
          client_sent
          Seq.empty /\
        WFSM.valid_byte_trace
          (ServerCP.server_system server_initial)
          server_received
          server
          server_sent
          Seq.empty /\
        Seq.equal client_sent server_received /\
        Seq.equal server_sent client_received)
      (ensures
        exists client_trace server_trace.
          SM.trace_reaches
            (ClientCP.client_state_machine client_initial)
            client_initial
            client_trace
            client /\
          SM.trace_reaches
            (ServerCP.server_state_machine server_initial)
            server_initial
            server_trace
            server /\
          Seq.equal
            (WF.serialize_all
              TLS13.Impl.CanonicalWire.tls_record_wire_format
              (SM.trace_wire_outputs client_trace))
            (WF.serialize_all
              TLS13.Impl.CanonicalWire.tls_record_wire_format
              (WFSM.trace_input_messages server_trace)) /\
          Seq.equal
            (WF.serialize_all
              TLS13.Impl.CanonicalWire.tls_record_wire_format
              (SM.trace_wire_outputs server_trace))
            (WF.serialize_all
              TLS13.Impl.CanonicalWire.tls_record_wire_format
              (WFSM.trace_input_messages client_trace)))
=
  PNTWL.lemma_client_valid_byte_trace_inverts_to_serialized_trace
    client_initial
    client_received
    client
    client_sent;
  PNTWL.lemma_server_valid_byte_trace_inverts_to_serialized_trace
    server_initial
    server_received
    server
    server_sent;
  assert (exists client_trace.
    SM.trace_reaches
      (ClientCP.client_state_machine client_initial)
      client_initial
      client_trace
      client /\
    Seq.equal
      client_received
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (WFSM.trace_input_messages client_trace)) /\
    Seq.equal
      client_sent
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (SM.trace_wire_outputs client_trace)));
  assert (exists server_trace.
    SM.trace_reaches
      (ServerCP.server_state_machine server_initial)
      server_initial
      server_trace
      server /\
    Seq.equal
      server_received
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (WFSM.trace_input_messages server_trace)) /\
    Seq.equal
      server_sent
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (SM.trace_wire_outputs server_trace)));
  eliminate exists client_trace.
    SM.trace_reaches
      (ClientCP.client_state_machine client_initial)
      client_initial
      client_trace
      client /\
    Seq.equal
      client_received
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (WFSM.trace_input_messages client_trace)) /\
    Seq.equal
      client_sent
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (SM.trace_wire_outputs client_trace))
  returns
    exists client_trace server_trace.
      SM.trace_reaches
        (ClientCP.client_state_machine client_initial)
        client_initial
        client_trace
        client /\
      SM.trace_reaches
        (ServerCP.server_state_machine server_initial)
        server_initial
        server_trace
        server /\
      Seq.equal
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (SM.trace_wire_outputs client_trace))
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (WFSM.trace_input_messages server_trace)) /\
      Seq.equal
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (SM.trace_wire_outputs server_trace))
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (WFSM.trace_input_messages client_trace))
  with _.
  (
    eliminate exists server_trace.
      SM.trace_reaches
        (ServerCP.server_state_machine server_initial)
        server_initial
        server_trace
        server /\
      Seq.equal
        server_received
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (WFSM.trace_input_messages server_trace)) /\
      Seq.equal
        server_sent
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (SM.trace_wire_outputs server_trace))
    returns
      exists client_trace' server_trace'.
        SM.trace_reaches
          (ClientCP.client_state_machine client_initial)
          client_initial
          client_trace'
          client /\
        SM.trace_reaches
          (ServerCP.server_state_machine server_initial)
          server_initial
          server_trace'
          server /\
        Seq.equal
          (WF.serialize_all
            TLS13.Impl.CanonicalWire.tls_record_wire_format
            (SM.trace_wire_outputs client_trace'))
          (WF.serialize_all
            TLS13.Impl.CanonicalWire.tls_record_wire_format
            (WFSM.trace_input_messages server_trace')) /\
        Seq.equal
          (WF.serialize_all
            TLS13.Impl.CanonicalWire.tls_record_wire_format
            (SM.trace_wire_outputs server_trace'))
          (WF.serialize_all
            TLS13.Impl.CanonicalWire.tls_record_wire_format
            (WFSM.trace_input_messages client_trace'))
    with _.
    (
      Seq.lemma_eq_elim
        client_sent
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (SM.trace_wire_outputs client_trace));
      Seq.lemma_eq_elim
        server_received
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (WFSM.trace_input_messages server_trace));
      Seq.lemma_eq_elim
        server_sent
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (SM.trace_wire_outputs server_trace));
      Seq.lemma_eq_elim
        client_received
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (WFSM.trace_input_messages client_trace));
      assert (Seq.equal
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (SM.trace_wire_outputs client_trace))
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (WFSM.trace_input_messages server_trace)));
      assert (Seq.equal
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (SM.trace_wire_outputs server_trace))
        (WF.serialize_all
          TLS13.Impl.CanonicalWire.tls_record_wire_format
          (WFSM.trace_input_messages client_trace)));
      assert (exists client_trace' server_trace'.
        SM.trace_reaches
          (ClientCP.client_state_machine client_initial)
          client_initial
          client_trace'
          client /\
        SM.trace_reaches
          (ServerCP.server_state_machine server_initial)
          server_initial
          server_trace'
          server /\
        Seq.equal
          (WF.serialize_all
            TLS13.Impl.CanonicalWire.tls_record_wire_format
            (SM.trace_wire_outputs client_trace'))
          (WF.serialize_all
            TLS13.Impl.CanonicalWire.tls_record_wire_format
            (WFSM.trace_input_messages server_trace')) /\
        Seq.equal
          (WF.serialize_all
            TLS13.Impl.CanonicalWire.tls_record_wire_format
            (SM.trace_wire_outputs server_trace'))
          (WF.serialize_all
            TLS13.Impl.CanonicalWire.tls_record_wire_format
            (WFSM.trace_input_messages client_trace')))
    )
  )

let lemma_clean_no_tail_valid_byte_traces_invert_to_paired_serialized_traces
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
        paired_supported_no_tail_valid_byte_traces_clean
            client_initial
            server_initial
            client
            server
            client_received
            client_sent
            server_received
            server_sent)
      (ensures
        exists client_trace server_trace.
            SM.trace_reaches
              (ClientCP.client_state_machine client_initial)
              client_initial
              client_trace
              client /\
            SM.trace_reaches
              (ServerCP.server_state_machine server_initial)
              server_initial
              server_trace
              server /\
            Seq.equal
              (WF.serialize_all
                TLS13.Impl.CanonicalWire.tls_record_wire_format
                (SM.trace_wire_outputs client_trace))
              (WF.serialize_all
                TLS13.Impl.CanonicalWire.tls_record_wire_format
                (WFSM.trace_input_messages server_trace)) /\
            Seq.equal
              (WF.serialize_all
                TLS13.Impl.CanonicalWire.tls_record_wire_format
                (SM.trace_wire_outputs server_trace))
              (WF.serialize_all
                TLS13.Impl.CanonicalWire.tls_record_wire_format
                (WFSM.trace_input_messages client_trace)))
=
  lemma_valid_byte_traces_invert_to_paired_serialized_traces_common
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent

let lemma_clean16_no_tail_valid_byte_traces_invert_to_paired_serialized_traces
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
        paired_supported_no_tail_valid_byte_traces_clean16
            client_initial
            server_initial
            client
            server
            client_received
            client_sent
            server_received
            server_sent)
      (ensures
        exists client_trace server_trace.
            SM.trace_reaches
              (ClientCP.client_state_machine client_initial)
              client_initial
              client_trace
              client /\
            SM.trace_reaches
              (ServerCP.server_state_machine server_initial)
              server_initial
              server_trace
              server /\
            Seq.equal
              (WF.serialize_all
                TLS13.Impl.CanonicalWire.tls_record_wire_format
                (SM.trace_wire_outputs client_trace))
              (WF.serialize_all
                TLS13.Impl.CanonicalWire.tls_record_wire_format
                (WFSM.trace_input_messages server_trace)) /\
            Seq.equal
              (WF.serialize_all
                TLS13.Impl.CanonicalWire.tls_record_wire_format
                (SM.trace_wire_outputs server_trace))
              (WF.serialize_all
                TLS13.Impl.CanonicalWire.tls_record_wire_format
                (WFSM.trace_input_messages client_trace)))
=
  lemma_valid_byte_traces_invert_to_paired_serialized_traces_common
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent

let lemma_clean16_no_tail_valid_byte_traces_invert_to_paired_wire_message_traces
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        exists client_trace server_trace.
          SM.trace_reaches
            (ClientCP.client_state_machine client_initial)
            client_initial
            client_trace
            client /\
          SM.trace_reaches
            (ServerCP.server_state_machine server_initial)
            server_initial
            server_trace
            server /\
          SM.trace_wire_outputs client_trace ==
            WFSM.trace_input_messages server_trace /\
          SM.trace_wire_outputs server_trace ==
            WFSM.trace_input_messages client_trace)
=
  lemma_clean16_no_tail_valid_byte_traces_invert_to_paired_serialized_traces
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  eliminate exists client_trace server_trace.
    SM.trace_reaches
      (ClientCP.client_state_machine client_initial)
      client_initial
      client_trace
      client /\
    SM.trace_reaches
      (ServerCP.server_state_machine server_initial)
      server_initial
      server_trace
      server /\
    Seq.equal
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (SM.trace_wire_outputs client_trace))
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (WFSM.trace_input_messages server_trace)) /\
    Seq.equal
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (SM.trace_wire_outputs server_trace))
      (WF.serialize_all
        TLS13.Impl.CanonicalWire.tls_record_wire_format
        (WFSM.trace_input_messages client_trace))
  returns
    exists client_trace' server_trace'.
      SM.trace_reaches
        (ClientCP.client_state_machine client_initial)
        client_initial
        client_trace'
        client /\
      SM.trace_reaches
        (ServerCP.server_state_machine server_initial)
        server_initial
        server_trace'
        server /\
      SM.trace_wire_outputs client_trace' ==
        WFSM.trace_input_messages server_trace' /\
      SM.trace_wire_outputs server_trace' ==
        WFSM.trace_input_messages client_trace'
  with _.
  (
    PNTWL.lemma_wire_serialize_all_injective
      (SM.trace_wire_outputs client_trace)
      (WFSM.trace_input_messages server_trace);
    PNTWL.lemma_wire_serialize_all_injective
      (SM.trace_wire_outputs server_trace)
      (WFSM.trace_input_messages client_trace);
    assert (exists client_trace' server_trace'.
      SM.trace_reaches
        (ClientCP.client_state_machine client_initial)
        client_initial
        client_trace'
        client /\
      SM.trace_reaches
        (ServerCP.server_state_machine server_initial)
        server_initial
        server_trace'
        server /\
      SM.trace_wire_outputs client_trace' ==
        WFSM.trace_input_messages server_trace' /\
      SM.trace_wire_outputs server_trace' ==
        WFSM.trace_input_messages client_trace')
  )

let lemma_clean_no_tail_valid_byte_traces_paired_wire_logs
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures CS.paired_wire_logs client server)
=
  PNTWL.lemma_client_valid_byte_trace_wire_logs_exact
    client_initial
    client_received
    client
    client_sent;
  PNTWL.lemma_server_valid_byte_trace_wire_logs_exact
    server_initial
    server_received
    server
    server_sent;
  Seq.lemma_eq_elim client_sent client.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim server_received server.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim server_sent server.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim client_received client.CS.cs_wire_log.CL.raw_received;
  assert (Seq.equal
    client.CS.cs_wire_log.CL.raw_sent
    server.CS.cs_wire_log.CL.raw_received);
  assert (Seq.equal
    server.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received)

let lemma_clean16_no_tail_valid_byte_traces_paired_wire_logs
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures CS.paired_wire_logs client server)
=
  PNTWL.lemma_client_valid_byte_trace_wire_logs_exact
    client_initial
    client_received
    client
    client_sent;
  PNTWL.lemma_server_valid_byte_trace_wire_logs_exact
    server_initial
    server_received
    server
    server_sent;
  Seq.lemma_eq_elim client_sent client.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim server_received server.CS.cs_wire_log.CL.raw_received;
  Seq.lemma_eq_elim server_sent server.CS.cs_wire_log.CL.raw_sent;
  Seq.lemma_eq_elim client_received client.CS.cs_wire_log.CL.raw_received;
  assert (Seq.equal
    client.CS.cs_wire_log.CL.raw_sent
    server.CS.cs_wire_log.CL.raw_received);
  assert (Seq.equal
    server.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received)

let lemma_clean_no_tail_valid_byte_traces_normalized_cleartext_raw_wire_bridge_from_role_local_prefix
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  (client_start:CS.handshake_start)
  (client_ch:M.client_hello)
  (client_sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:M.server_hello)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
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
        WFL.supported_client_hello_wire_profile client_ch)
      (ensures
        PNTRB.normalized_cleartext_raw_wire_bridge
          client_ch
          server_ch
          client_sh
          server_sh)
=
  lemma_clean_no_tail_valid_byte_traces_paired_wire_logs
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (CS.paired_wire_logs client server);
  assert (PNT.paired_no_tail_application_ready_boundary client server);
  assert (TLS13.Impl.Client.Driver.client_driver_application_ready client);
  assert (TLS13.Impl.Server.Driver.server_driver_application_ready server);
  assert (TLS13.Impl.Client.Types.client_end_to_end_invariant client);
  assert (TLS13.Impl.Server.Types.server_end_to_end_invariant server);
  assert (CS.connection_state_raw_event_replay_consistent client);
  assert (CS.connection_state_raw_event_replay_consistent server);
  PNTRB.lemma_normalized_cleartext_raw_wire_bridge_from_role_local_prefixes
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
    server_rest

let lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_raw_wire_bridge_from_role_local_prefix
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  (client_start:CS.handshake_start)
  (client_ch:M.client_hello)
  (client_sh:M.server_hello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:M.server_hello)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
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
        WFL.supported_client_hello_wire_profile client_ch)
      (ensures
        PNTRB.normalized_cleartext_raw_wire_bridge
          client_ch
          server_ch
          client_sh
          server_sh)
=
  lemma_clean16_no_tail_valid_byte_traces_paired_wire_logs
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (CS.paired_wire_logs client server);
  assert (PNT.paired_no_tail_application_ready_boundary16 client server);
  assert (TLS13.Impl.Client.Driver.client_driver_application_ready client);
  assert (TLS13.Impl.Server.Driver.server_driver_application_ready server);
  assert (TLS13.Impl.Client.Types.client_end_to_end_invariant client);
  assert (TLS13.Impl.Server.Types.server_end_to_end_invariant server);
  assert (CS.connection_state_raw_event_replay_consistent client);
  assert (CS.connection_state_raw_event_replay_consistent server);
  PNTRB.lemma_normalized_cleartext_raw_wire_bridge_from_role_local_prefixes
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
    server_rest

let lemma_paired_successful_handshake_normalized_replay_shape_from_clean_no_tail_valid_byte_traces_and_normalized_replay_boundary
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        PNB.paired_supported_normalized_replay_boundary client server)
      (ensures
        PNS.paired_successful_handshake_normalized_replay_shape
          client
          server)
=
  PBridge.lemma_paired_successful_handshake_normalized_replay_shape_from_normalized_replay_boundary
    client
    server

let lemma_paired_successful_handshake_normalized_replay_shape_from_clean16_no_tail_valid_byte_traces_and_normalized_replay_boundary
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        PNB.paired_supported_normalized_replay_boundary client server)
      (ensures
        PNS.paired_successful_handshake_normalized_replay_shape
          client
          server)
=
  PBridge.lemma_paired_successful_handshake_normalized_replay_shape_from_normalized_replay_boundary
    client
    server

let lemma_client_server_application_record_material_agrees_from_clean_no_tail_valid_byte_traces_and_normalized_replay_boundary
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
        paired_supported_no_tail_valid_byte_traces_clean
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        PNB.paired_supported_normalized_replay_boundary client server)
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
  lemma_paired_successful_handshake_normalized_replay_shape_from_clean_no_tail_valid_byte_traces_and_normalized_replay_boundary
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNS.lemma_client_server_application_record_material_agrees_from_normalized_replay_shape
    client
    server

let lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_normalized_replay_boundary
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        PNB.paired_supported_normalized_replay_boundary client server)
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
  lemma_paired_successful_handshake_normalized_replay_shape_from_clean16_no_tail_valid_byte_traces_and_normalized_replay_boundary
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNS.lemma_client_server_application_record_material_agrees_from_normalized_replay_shape
    client
    server

let lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_normalized_staged_replay_boundary
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
        paired_supported_no_tail_valid_byte_traces_clean16
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent /\
        PSNB.paired_supported_normalized_staged_replay_boundary client server)
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
  PSNB.lemma_client_server_application_record_material_agrees_from_normalized_staged_replay_boundary
    client
    server
