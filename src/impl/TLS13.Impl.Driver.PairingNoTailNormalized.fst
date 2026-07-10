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
module M = TLS13.Messages
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished
module Pairing = TLS13.Impl.Driver.Pairing
module PNB = TLS13.Impl.Driver.PairingNormalizedBoundary
module PNS = TLS13.Impl.Driver.PairingNormalizedShape
module PNT = TLS13.Impl.Driver.PairingNoTail
module PNTCAS = TLS13.Impl.Driver.PairingNoTailClientAppShape
module PNTCFS = TLS13.Impl.Driver.PairingNoTailClientFinishedShape
module PNTCPrS = TLS13.Impl.Driver.PairingNoTailClientProtectedShape
module PNTCPS = TLS13.Impl.Driver.PairingNoTailClientPostSharedShape
module PNTCRR = TLS13.Impl.Driver.PairingNoTailClientReceivedRawShape
module PNTCS = TLS13.Impl.Driver.PairingNoTailClientShape
module PNTCSR = TLS13.Impl.Driver.PairingNoTailClientSentRawShape
module PNTCVS = TLS13.Impl.Driver.PairingNoTailClientVerifyShape
module PNI = TLS13.Impl.Driver.PairingNoTailInversion
module PNTRB = TLS13.Impl.Driver.PairingNoTailRawBridge
module PNTSC = TLS13.Impl.Driver.PairingNoTailServerCleartextShape
module PNTSS = TLS13.Impl.Driver.PairingNoTailServerShape
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module PWR = TLS13.ConnectionState.ProtectedWireReplay
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module Seq = FStar.Seq
module SCVE = TLS13.ConnectionState.ServerCertificateVerifyEvent
module SM = Common.StateMachine
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module T = TLS13.Types
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

let lemma_clean16_no_tail_valid_byte_traces_role_local_start_and_final_witnesses16
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
      (ensures paired_no_tail_role_local_start_and_final_witnesses16 client server)
=
  PNTCS.lemma_client_no_tail_start_spine_and_final_model_witnesses client;
  PNTSS.lemma_server_no_tail_start_spine16 server;
  PNTSS.lemma_server_no_tail_final_model_witnesses16 server

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

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_certificate_validated_server_start_spine16
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
        paired_no_tail_role_local_client_certificate_validated_server_start_spine16
          client
          server)
=
  PNTCPrS.lemma_client_no_tail_ninth_event_validate_certificate_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_certificate_verify_received_server_start_spine16
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
        paired_no_tail_role_local_client_certificate_verify_received_server_start_spine16
          client
          server)
=
  PNTCVS.lemma_client_no_tail_tenth_event_certificate_verify_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_certificate_signature_verified_server_start_spine16
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
        paired_no_tail_role_local_client_certificate_signature_verified_server_start_spine16
          client
          server)
=
  PNTCVS.lemma_client_no_tail_eleventh_event_verify_certificate_signature_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_server_finished_received_server_start_spine16
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
        paired_no_tail_role_local_client_server_finished_received_server_start_spine16
          client
          server)
=
  PNTCFS.lemma_client_no_tail_twelfth_event_server_finished_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_server_finished_verified_server_start_spine16
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
        paired_no_tail_role_local_client_server_finished_verified_server_start_spine16
          client
          server)
=
  PNTCFS.lemma_client_no_tail_thirteenth_event_verify_finished_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_application_installs_server_start_spine16
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
        paired_no_tail_role_local_client_application_installs_server_start_spine16
          client
          server)
=
  PNTCAS.lemma_client_no_tail_fourteenth_and_fifteenth_events_application_install_cover_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_finished_sent_server_start_spine16
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
        paired_no_tail_role_local_client_finished_sent_server_start_spine16
          client
          server)
=
  PNTCAS.lemma_client_no_tail_sixteenth_event_client_finished_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server

let lemma_clean16_no_tail_valid_byte_traces_client_sent_cleartext_and_finished_raw_slices
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
      (ensures PNTCSR.client_sent_cleartext_and_finished_raw_slices client)
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
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_finished_sent_server_start_spine16
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (CS.connection_state_raw_event_replay_consistent client);
  PNTCSR.lemma_client_no_tail_finished_sent_raw_slices client

let lemma_clean16_no_tail_valid_byte_traces_client_received_cleartext_and_server_flight_raw_slices
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
        PNTCRR.client_received_cleartext_and_server_flight_raw_slices client)
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
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_finished_sent_server_start_spine16
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (CS.connection_state_raw_event_replay_consistent client);
  PNTCRR.lemma_client_no_tail_server_flight_received_raw_slices client

let lemma_clean16_no_tail_valid_byte_traces_server_sent_cleartext_and_server_flight_raw_slices
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
      (ensures server_sent_cleartext_and_server_flight_raw_slices server)
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
    client.CS.cs_wire_log.CL.raw_received);
  lemma_clean16_no_tail_valid_byte_traces_client_received_cleartext_and_server_flight_raw_slices
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (CS.paired_wire_logs client server);
  eliminate exists
    (sh:GSH.serverHello)
    (ee:GEE.encryptedExtensions)
    (cert:GCert.certificate)
    (cv:GCV.certificateVerify)
    (sf:GFin.finished)
    server_sh_raw
    ee_raw
    cert_raw
    cv_raw
    sf_raw.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append
        server_sh_raw
        (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw)))) /\
    CS.received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello sh))
      server_sh_raw /\
    CS.raw_records_exactly ee_raw T.Application_data 1 /\
    CS.raw_records_exactly cert_raw T.Application_data 1 /\
    CS.raw_records_exactly cv_raw T.Application_data 1 /\
    CS.raw_records_exactly sf_raw T.Application_data 1
  returns server_sent_cleartext_and_server_flight_raw_slices server
  with _.
  (
    let flight_raw =
      B.append
        server_sh_raw
        (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw))) in
    assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent client.CS.cs_wire_log.CL.raw_received);
    Seq.lemma_eq_elim
      server.CS.cs_wire_log.CL.raw_sent
      client.CS.cs_wire_log.CL.raw_received;
    assert (Seq.equal server.CS.cs_wire_log.CL.raw_sent flight_raw);
    assert (CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello sh))
      server_sh_raw);
    assert (exists
      (sh0:GSH.serverHello)
      (ee0:GEE.encryptedExtensions)
      (cert0:GCert.certificate)
      (cv0:GCV.certificateVerify)
      (sf0:GFin.finished)
      server_sh_raw0
      ee_raw0
      cert_raw0
      cv_raw0
      sf_raw0.
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append
          server_sh_raw0
          (B.append ee_raw0 (B.append cert_raw0 (B.append cv_raw0 sf_raw0)))) /\
      CS.cleartext_tls_message_raw
        (M.TlsHandshake (M.ServerHello sh0))
        server_sh_raw0 /\
      CS.raw_records_exactly ee_raw0 T.Application_data 1 /\
      CS.raw_records_exactly cert_raw0 T.Application_data 1 /\
      CS.raw_records_exactly cv_raw0 T.Application_data 1 /\
      CS.raw_records_exactly sf_raw0 T.Application_data 1)
  )

let lemma_clean16_no_tail_valid_byte_traces_server_received_cleartext_and_client_finished_raw_slices
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
      (ensures server_received_cleartext_and_client_finished_raw_slices server)
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
  lemma_clean16_no_tail_valid_byte_traces_client_sent_cleartext_and_finished_raw_slices
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  eliminate exists (ch:GCH.clientHello) (cf:GFin.finished) client_ch_raw client_finished_raw.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_finished_raw) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      client_ch_raw /\
    CS.raw_records_exactly client_finished_raw T.Application_data 1
  returns server_received_cleartext_and_client_finished_raw_slices server
  with _.
  (
    assert (Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received);
    Seq.lemma_eq_elim
      server.CS.cs_wire_log.CL.raw_received
      client.CS.cs_wire_log.CL.raw_sent;
    assert (exists (ch0:GCH.clientHello) (cf0:GFin.finished) client_ch_raw0 client_finished_raw0.
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append client_ch_raw0 client_finished_raw0) /\
      CS.cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello ch0))
        client_ch_raw0 /\
      CS.raw_records_exactly client_finished_raw0 T.Application_data 1)
  )

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

let lemma_clean16_no_tail_valid_byte_traces_server_sent_certificate_verify_event
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
      (ensures SCVE.contains_sent_certificate_verify server.CS.cs_event_log)
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
  assert (PNT.paired_no_tail_application_ready_boundary16 client server);
  assert (TLS13.Impl.Server.Driver.server_driver_application_ready server);
  assert (server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert (server.CS.cs_model.CS.model_control == CS.ControlApplicationData);
  SCVE.lemma_server_application_ready_sent_certificate_verify_event server

let lemma_clean16_no_tail_valid_byte_traces_server_sent_certificate_verify_event_split
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
      (ensures server_sent_certificate_verify_event_split server)
=
  lemma_clean16_no_tail_valid_byte_traces_server_sent_certificate_verify_event
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  SCVE.lemma_contains_sent_certificate_verify_split server.CS.cs_event_log

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

let lemma_paired_client_sent_client_hello_not_server_received_ccs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        WFL.supported_client_config_wire_profile
          client.CS.cs_model.CS.model_config /\
        CS.paired_wire_logs client server /\
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        client.CS.cs_event_log ==
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
          client_rest /\
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsChangeCipherSpec;
          }) ::
          server_rest)
      (ensures False)
=
  let client_model0 =
    CS.initial_model client.CS.cs_model.CS.model_config in
  let server_model0 =
    CS.initial_model server.CS.cs_model.CS.model_config in
  assert (CS.conn_events_raw_replay
    client_model0
    client.CS.cs_event_log
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model);
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
  PNTRB.lemma_client_prefix_sent_client_hello_supported
    client_model0
    client_start
    client_ch
    client_sh
    client_shared
    client_rest
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model;
  assert (WFL.supported_client_hello_wire_profile client_ch);
  PNTRB.lemma_client_prefix_raw_slices
    client_model0
    client_start
    client_ch
    client_sh
    client_shared
    client_rest
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model;
  eliminate exists client_ch_raw client_sh_raw client_sent_tail client_received_tail.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_sent_tail) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append client_sh_raw client_received_tail) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello client_ch))
      client_ch_raw /\
    CS.received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello client_sh))
      client_sh_raw
  returns False
  with _.
  (
    assert (CS.conn_events_raw_replay
      server_model0
      server.CS.cs_event_log
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    assert (CS.conn_events_raw_replay
      server_model0
      (CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsChangeCipherSpec;
       }) ::
       server_rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_start_then_received_change_cipher_spec_raw_slice
      server_model0
      server_rest
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists ccs_raw server_received_tail.
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append ccs_raw server_received_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    returns False
    with _.
    (
      assert (Seq.equal
        client.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received);
      PNTRB.lemma_equal_stream_head_sent_supported_client_hello_not_change_cipher_spec
        client.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received
        client_ch
        client_ch_raw
        client_sent_tail
        ccs_raw
        server_received_tail
    )
  )

let lemma_paired_client_received_server_hello_not_server_sent_ccs
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        CS.paired_wire_logs client server /\
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        client.CS.cs_event_log ==
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
          client_rest /\
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsChangeCipherSpec;
          }) ::
          server_rest)
      (ensures False)
=
  let client_model0 =
    CS.initial_model client.CS.cs_model.CS.model_config in
  let server_model0 =
    CS.initial_model server.CS.cs_model.CS.model_config in
  assert (CS.conn_events_raw_replay
    client_model0
    client.CS.cs_event_log
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model);
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
  PNTRB.lemma_client_prefix_raw_slices
    client_model0
    client_start
    client_ch
    client_sh
    client_shared
    client_rest
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model;
  eliminate exists client_ch_raw client_sh_raw client_sent_tail client_received_tail.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_sent_tail) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append client_sh_raw client_received_tail) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello client_ch))
      client_ch_raw /\
    CS.received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello client_sh))
      client_sh_raw
  returns False
  with _.
  (
    assert (CS.conn_events_raw_replay
      server_model0
      server.CS.cs_event_log
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    assert (CS.conn_events_raw_replay
      server_model0
      (CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsChangeCipherSpec;
       }) ::
       server_rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_start_then_sent_change_cipher_spec_raw_slice
      server_model0
      server_rest
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists ccs_raw server_sent_tail.
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append ccs_raw server_sent_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    returns False
    with _.
    (
      assert (Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received);
      PNTRB.lemma_equal_stream_head_received_server_hello_not_change_cipher_spec
        client.CS.cs_wire_log.CL.raw_received
        server.CS.cs_wire_log.CL.raw_sent
        client_sh
        client_sh_raw
        client_received_tail
        ccs_raw
        server_sent_tail
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_second_event_not_change_cipher_spec
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
      (ensures server_second_event_not_change_cipher_spec16 server)
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
  PNTCS.lemma_client_no_tail_fourth_event_derive_shared_secret_clean client;
  PNTSS.lemma_server_no_tail_start_spine16 server;
  assert (CS.paired_wire_logs client server);
  assert (PNT.paired_no_tail_application_ready_boundary16 client server);
  assert (TLS13.Impl.Client.Types.client_end_to_end_invariant client);
  assert (TLS13.Impl.Server.Types.server_end_to_end_invariant server);
  assert (CS.connection_state_raw_event_replay_consistent client);
  assert (CS.connection_state_raw_event_replay_consistent server);
  eliminate exists client_start client_ch client_sh client_shared client_rest.
    client.CS.cs_event_log ==
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
      client_rest
  returns server_second_event_not_change_cipher_spec16 server
  with _.
  (
    eliminate exists e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15.
      server.CS.cs_event_log ==
        [ CS.ConnLocalEvent CS.LocalStartServer;
          e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15 ]
    returns server_second_event_not_change_cipher_spec16 server
    with _.
    (
      let server_rest = [e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15] in
      assert (server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer :: e1 :: server_rest);
      (match e1 with
      | CS.ConnNetworkEvent msg ->
        (match msg.CL.message_value with
        | M.TlsChangeCipherSpec ->
          (match msg.CL.message_direction with
          | CL.Received ->
            lemma_paired_client_sent_client_hello_not_server_received_ccs
              client
              server
              client_start
              client_ch
              client_sh
              client_shared
              client_rest
              server_rest
          | CL.Sent ->
            lemma_paired_client_received_server_hello_not_server_sent_ccs
              client
              server
              client_start
              client_ch
              client_sh
              client_shared
              client_rest
              server_rest)
        | _ -> ())
      | _ -> ());
      assert (~ (exists m.
        e1 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec));
      assert (server_second_event_not_change_cipher_spec16 server)
    )
  )

let lemma_paired_client_finished_not_server_received_ccs_after_client_hello
  (client:CS.connection_state)
  (server:CS.connection_state)
  (start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (e4 e5:CS.conn_event)
  (ee:GEE.encryptedExtensions)
  (cert:GCert.certificate)
  (peer:TLS13.X509.Spec.peer_identity)
  (cv:GCV.certificateVerify)
  (sf:GFin.finished)
  (e13 e14:CS.conn_event)
  (cf:GFin.finished)
  (server_ch:GCH.clientHello)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        WFL.supported_client_config_wire_profile
          client.CS.cs_model.CS.model_config /\
        CS.paired_wire_logs client server /\
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        client.CS.cs_event_log ==
          CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
          }) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
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
        PNTCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
          }) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsChangeCipherSpec;
          }) ::
          server_rest)
      (ensures False)
=
  let client_model0 =
    CS.initial_model client.CS.cs_model.CS.model_config in
  let server_model0 =
    CS.initial_model server.CS.cs_model.CS.model_config in
  assert (CS.conn_events_raw_replay
    client_model0
    client.CS.cs_event_log
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model);
  let client_rest =
    CS.ConnNetworkEvent ({
      CL.message_direction = CL.Received;
      CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
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
    [] in
  assert (CS.conn_events_raw_replay
    client_model0
    (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
     CS.ConnNetworkEvent ({
       CL.message_direction = CL.Sent;
       CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
     }) ::
     client_rest)
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model);
  PNTRB.lemma_client_prefix_sent_client_hello_supported
    client_model0
    start
    client_ch
    client_sh
    client_shared
    (e4 ::
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
     [])
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model;
  assert (WFL.supported_client_hello_wire_profile client_ch);
  PNTCSR.lemma_client_no_tail_finished_sent_raw_slices_for_shape
    client
    start
    client_ch
    client_sh
    client_shared
    e4
    e5
    ee
    cert
    peer
    cv
    sf
    e13
    e14
    cf;
  eliminate exists client_ch_raw client_finished_raw.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_finished_raw) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello client_ch))
      client_ch_raw /\
    CS.raw_records_exactly client_finished_raw T.Application_data 1
  returns False
  with _.
  (
    assert (CS.conn_events_raw_replay
      server_model0
      server.CS.cs_event_log
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    assert (CS.conn_events_raw_replay
      server_model0
      (CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsChangeCipherSpec;
       }) ::
       server_rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_start_client_hello_then_received_change_cipher_spec_raw_slices
      server_model0
      server_ch
      server_rest
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists server_ch_raw ccs_raw server_received_tail.
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append server_ch_raw (B.append ccs_raw server_received_tail)) /\
      CS.received_cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello server_ch))
        server_ch_raw /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    returns False
    with _.
    (
      assert (Seq.equal
        client.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received);
      PNTRB.lemma_equal_stream_after_client_hello_application_data_not_change_cipher_spec
        client.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received
        client_ch
        server_ch
        client_ch_raw
        client_finished_raw
        server_ch_raw
        ccs_raw
        server_received_tail
    )
  )

let lemma_paired_client_received_server_hello_not_server_sent_ccs_after_client_hello
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:GCH.clientHello)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        CS.paired_wire_logs client server /\
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        client.CS.cs_event_log ==
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
          client_rest /\
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
          }) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsChangeCipherSpec;
          }) ::
          server_rest)
      (ensures False)
=
  let client_model0 =
    CS.initial_model client.CS.cs_model.CS.model_config in
  let server_model0 =
    CS.initial_model server.CS.cs_model.CS.model_config in
  assert (CS.conn_events_raw_replay
    client_model0
    client.CS.cs_event_log
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model);
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
  PNTRB.lemma_client_prefix_raw_slices
    client_model0
    client_start
    client_ch
    client_sh
    client_shared
    client_rest
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model;
  eliminate exists client_ch_raw client_sh_raw client_sent_tail client_received_tail.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_sent_tail) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append client_sh_raw client_received_tail) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello client_ch))
      client_ch_raw /\
    CS.received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello client_sh))
      client_sh_raw
  returns False
  with _.
  (
    assert (CS.conn_events_raw_replay
      server_model0
      server.CS.cs_event_log
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    assert (CS.conn_events_raw_replay
      server_model0
      (CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
       }) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsChangeCipherSpec;
       }) ::
       server_rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_start_client_hello_then_sent_change_cipher_spec_raw_slice
      server_model0
      server_ch
      server_rest
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists ccs_raw server_sent_tail.
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append ccs_raw server_sent_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    returns False
    with _.
    (
      assert (Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received);
      PNTRB.lemma_equal_stream_head_received_server_hello_not_change_cipher_spec
        client.CS.cs_wire_log.CL.raw_received
        server.CS.cs_wire_log.CL.raw_sent
        client_sh
        client_sh_raw
        client_received_tail
        ccs_raw
        server_sent_tail
    )
  )

let lemma_paired_client_finished_not_server_received_ccs_after_client_hello_select
  (client:CS.connection_state)
  (server:CS.connection_state)
  (start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (e4 e5:CS.conn_event)
  (ee:GEE.encryptedExtensions)
  (cert:GCert.certificate)
  (peer:TLS13.X509.Spec.peer_identity)
  (cv:GCV.certificateVerify)
  (sf:GFin.finished)
  (e13 e14:CS.conn_event)
  (cf:GFin.finished)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        WFL.supported_client_config_wire_profile
          client.CS.cs_model.CS.model_config /\
        CS.paired_wire_logs client server /\
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        client.CS.cs_event_log ==
          CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
          }) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
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
        PNTCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
        PNTCAS.client_no_tail_application_install_cover e13 e14 /\
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
          }) ::
          CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsChangeCipherSpec;
          }) ::
          server_rest)
      (ensures False)
=
  let client_model0 =
    CS.initial_model client.CS.cs_model.CS.model_config in
  let server_model0 =
    CS.initial_model server.CS.cs_model.CS.model_config in
  assert (CS.conn_events_raw_replay
    client_model0
    client.CS.cs_event_log
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model);
  PNTRB.lemma_client_prefix_sent_client_hello_supported
    client_model0
    start
    client_ch
    client_sh
    client_shared
    (e4 ::
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
     [])
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model;
  assert (WFL.supported_client_hello_wire_profile client_ch);
  PNTCSR.lemma_client_no_tail_finished_sent_raw_slices_for_shape
    client
    start
    client_ch
    client_sh
    client_shared
    e4
    e5
    ee
    cert
    peer
    cv
    sf
    e13
    e14
    cf;
  eliminate exists client_ch_raw client_finished_raw.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_finished_raw) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello client_ch))
      client_ch_raw /\
    CS.raw_records_exactly client_finished_raw T.Application_data 1
  returns False
  with _.
  (
    assert (CS.conn_events_raw_replay
      server_model0
      server.CS.cs_event_log
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    assert (CS.conn_events_raw_replay
      server_model0
      (CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
       }) ::
       CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsChangeCipherSpec;
       }) ::
       server_rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_start_client_hello_select_then_received_change_cipher_spec_raw_slices
      server_model0
      server_ch
      selection
      server_rest
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists server_ch_raw ccs_raw server_received_tail.
      Seq.equal
        server.CS.cs_wire_log.CL.raw_received
        (B.append server_ch_raw (B.append ccs_raw server_received_tail)) /\
      CS.received_cleartext_tls_message_raw
        (M.TlsHandshake (M.ClientHello server_ch))
        server_ch_raw /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    returns False
    with _.
    (
      assert (Seq.equal
        client.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received);
      PNTRB.lemma_equal_stream_after_client_hello_application_data_not_change_cipher_spec
        client.CS.cs_wire_log.CL.raw_sent
        server.CS.cs_wire_log.CL.raw_received
        client_ch
        server_ch
        client_ch_raw
        client_finished_raw
        server_ch_raw
        ccs_raw
        server_received_tail
    )
  )

let lemma_paired_client_received_server_hello_not_server_sent_ccs_after_client_hello_select
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_start:CS.handshake_start)
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_rest:list CS.conn_event)
  : Lemma
      (requires
        CS.paired_wire_logs client server /\
        CS.connection_state_raw_event_replay_consistent client /\
        CS.connection_state_raw_event_replay_consistent server /\
        client.CS.cs_event_log ==
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
          client_rest /\
        server.CS.cs_event_log ==
          CS.ConnLocalEvent CS.LocalStartServer ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
          }) ::
          CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
          CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsChangeCipherSpec;
          }) ::
          server_rest)
      (ensures False)
=
  let client_model0 =
    CS.initial_model client.CS.cs_model.CS.model_config in
  let server_model0 =
    CS.initial_model server.CS.cs_model.CS.model_config in
  assert (CS.conn_events_raw_replay
    client_model0
    client.CS.cs_event_log
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model);
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
  PNTRB.lemma_client_prefix_raw_slices
    client_model0
    client_start
    client_ch
    client_sh
    client_shared
    client_rest
    client.CS.cs_wire_log.CL.raw_sent
    client.CS.cs_wire_log.CL.raw_received
    client.CS.cs_model;
  eliminate exists client_ch_raw client_sh_raw client_sent_tail client_received_tail.
    Seq.equal
      client.CS.cs_wire_log.CL.raw_sent
      (B.append client_ch_raw client_sent_tail) /\
    Seq.equal
      client.CS.cs_wire_log.CL.raw_received
      (B.append client_sh_raw client_received_tail) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello client_ch))
      client_ch_raw /\
    CS.received_cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello client_sh))
      client_sh_raw
  returns False
  with _.
  (
    assert (CS.conn_events_raw_replay
      server_model0
      server.CS.cs_event_log
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    assert (CS.conn_events_raw_replay
      server_model0
      (CS.ConnLocalEvent CS.LocalStartServer ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Received;
         CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
       }) ::
       CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
       CS.ConnNetworkEvent ({
         CL.message_direction = CL.Sent;
         CL.message_value = M.TlsChangeCipherSpec;
       }) ::
       server_rest)
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model);
    PNTRB.lemma_server_start_client_hello_select_then_sent_change_cipher_spec_raw_slice
      server_model0
      server_ch
      selection
      server_rest
      server.CS.cs_wire_log.CL.raw_sent
      server.CS.cs_wire_log.CL.raw_received
      server.CS.cs_model;
    eliminate exists ccs_raw server_sent_tail.
      Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        (B.append ccs_raw server_sent_tail) /\
      CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
    returns False
    with _.
    (
      assert (Seq.equal
        server.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received);
      PNTRB.lemma_equal_stream_head_received_server_hello_not_change_cipher_spec
        client.CS.cs_wire_log.CL.raw_received
        server.CS.cs_wire_log.CL.raw_sent
        client_sh
        client_sh_raw
        client_received_tail
        ccs_raw
        server_sent_tail
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_third_event_not_change_cipher_spec
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
      (ensures server_third_event_not_change_cipher_spec16 server)
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
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_finished_sent_server_start_spine16
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_clean16_no_tail_valid_byte_traces_server_second_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSS.lemma_server_no_tail_second_event_client_hello_if_not_ccs16 server;
  assert (CS.paired_wire_logs client server);
  assert (TLS13.Impl.Client.Types.client_end_to_end_invariant client);
  assert (TLS13.Impl.Server.Types.server_end_to_end_invariant server);
  assert (CS.connection_state_raw_event_replay_consistent client);
  assert (CS.connection_state_raw_event_replay_consistent server);
  eliminate exists start client_ch client_sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
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
    PNTCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14
  returns server_third_event_not_change_cipher_spec16 server
  with _.
  (
    eliminate exists server_ch server_tail.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        }) ::
        server_tail
    returns server_third_event_not_change_cipher_spec16 server
    with _.
    (
      match server_tail with
      | [] ->
        PNTSS.lemma_server_no_tail_start_spine16 server;
        assert False
      | e2 :: server_rest ->
        (match e2 with
        | CS.ConnNetworkEvent msg ->
          (match msg.CL.message_value with
          | M.TlsChangeCipherSpec ->
            (match msg.CL.message_direction with
            | CL.Received ->
              lemma_paired_client_finished_not_server_received_ccs_after_client_hello
                client
                server
                start
                client_ch
                client_sh
                client_shared
                e4
                e5
                ee
                cert
                peer
                cv
                sf
                e13
                e14
                cf
                server_ch
                server_rest
            | CL.Sent ->
              lemma_paired_client_received_server_hello_not_server_sent_ccs_after_client_hello
                client
                server
                start
                client_ch
                client_sh
                client_shared
                (e4 ::
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
                 [])
                server_ch
                server_rest)
          | _ -> ())
        | _ -> ());
        assert (~ (exists m.
          e2 == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec));
        assert (server_third_event_not_change_cipher_spec16 server)
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_fourth_event_not_change_cipher_spec
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
      (ensures server_fourth_event_not_change_cipher_spec16 server)
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
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_finished_sent_server_start_spine16
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCS.lemma_client_no_tail_fourth_event_derive_shared_secret_clean client;
  lemma_clean16_no_tail_valid_byte_traces_server_second_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSS.lemma_server_no_tail_second_event_client_hello_if_not_ccs16 server;
  lemma_clean16_no_tail_valid_byte_traces_server_third_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSC.lemma_server_no_tail_third_event_select_parameters_if_not_ccs16 server;
  assert (CS.paired_wire_logs client server);
  assert (TLS13.Impl.Client.Types.client_end_to_end_invariant client);
  assert (TLS13.Impl.Server.Types.server_end_to_end_invariant server);
  assert (CS.connection_state_raw_event_replay_consistent client);
  assert (CS.connection_state_raw_event_replay_consistent server);
  eliminate exists start client_ch client_sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
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
    PNTCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14
  returns server_fourth_event_not_change_cipher_spec16 server
  with _.
  (
    eliminate exists server_ch selection server_tail.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
        server_tail
    returns server_fourth_event_not_change_cipher_spec16 server
    with _.
    (
      match server_tail with
      | [] ->
        PNTSS.lemma_server_no_tail_start_spine16 server;
        assert False
      | e3 :: server_rest ->
        (match e3 with
        | CS.ConnNetworkEvent msg ->
          (match msg.CL.message_value with
          | M.TlsChangeCipherSpec ->
            (match msg.CL.message_direction with
            | CL.Received ->
              lemma_paired_client_finished_not_server_received_ccs_after_client_hello_select
                client
                server
                start
                client_ch
                client_sh
                client_shared
                e4
                e5
                ee
                cert
                peer
                cv
                sf
                e13
                e14
                cf
                server_ch
                selection
                server_rest
            | CL.Sent ->
              lemma_paired_client_received_server_hello_not_server_sent_ccs_after_client_hello_select
                client
                server
                start
                client_ch
                client_sh
                client_shared
                (e4 ::
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
                 [])
                server_ch
                selection
                server_rest)
          | _ -> ())
        | _ -> ());
        assert (~ (exists m.
          e3 == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec));
        assert (server_fourth_event_not_change_cipher_spec16 server)
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_fifth_event_not_change_cipher_spec
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
      (ensures server_fifth_event_not_change_cipher_spec16 server)
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
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_finished_sent_server_start_spine16
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTCS.lemma_client_no_tail_fourth_event_derive_shared_secret_clean client;
  lemma_clean16_no_tail_valid_byte_traces_server_second_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSS.lemma_server_no_tail_second_event_client_hello_if_not_ccs16 server;
  lemma_clean16_no_tail_valid_byte_traces_server_third_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSC.lemma_server_no_tail_third_event_select_parameters_if_not_ccs16 server;
  lemma_clean16_no_tail_valid_byte_traces_server_fourth_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSC.lemma_server_no_tail_fourth_event_derive_shared_secret_if_not_ccs16 server;
  assert (CS.paired_wire_logs client server);
  assert (TLS13.Impl.Client.Types.client_end_to_end_invariant client);
  assert (TLS13.Impl.Server.Types.server_end_to_end_invariant server);
  assert (CS.connection_state_raw_event_replay_consistent client);
  assert (CS.connection_state_raw_event_replay_consistent server);
  eliminate exists start client_ch client_sh client_shared e4 e5 ee cert peer cv sf e13 e14 cf.
    client.CS.cs_event_log ==
      CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
      }) ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
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
    PNTCPS.client_no_tail_two_handshake_install_cover e4 e5 /\
    PNTCAS.client_no_tail_application_install_cover e13 e14
  returns server_fifth_event_not_change_cipher_spec16 server
  with _.
  (
    eliminate exists server_ch selection server_shared server_tail.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
        server_tail
    returns server_fifth_event_not_change_cipher_spec16 server
    with _.
    (
      match server_tail with
      | [] ->
        PNTSS.lemma_server_no_tail_start_spine16 server;
        assert False
      | e4_server :: server_rest ->
        (match e4_server with
        | CS.ConnNetworkEvent msg ->
          (match msg.CL.message_value with
          | M.TlsChangeCipherSpec ->
            (match msg.CL.message_direction with
            | CL.Received ->
              let client_tail =
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
                [] in
              let client_model0 =
                CS.initial_model client.CS.cs_model.CS.model_config in
              let server_model0 =
                CS.initial_model server.CS.cs_model.CS.model_config in
              assert (CS.conn_events_raw_replay
                client_model0
                client.CS.cs_event_log
                client.CS.cs_wire_log.CL.raw_sent
                client.CS.cs_wire_log.CL.raw_received
                client.CS.cs_model);
              PNTRB.lemma_client_prefix_sent_client_hello_supported
                client_model0
                start
                client_ch
                client_sh
                client_shared
                client_tail
                client.CS.cs_wire_log.CL.raw_sent
                client.CS.cs_wire_log.CL.raw_received
                client.CS.cs_model;
              assert (WFL.supported_client_hello_wire_profile client_ch);
              PNTCSR.lemma_client_no_tail_finished_sent_raw_slices_for_shape
                client
                start
                client_ch
                client_sh
                client_shared
                e4
                e5
                ee
                cert
                peer
                cv
                sf
                e13
                e14
                cf;
              eliminate exists client_ch_raw client_finished_raw.
                Seq.equal
                  client.CS.cs_wire_log.CL.raw_sent
                  (B.append client_ch_raw client_finished_raw) /\
                CS.cleartext_tls_message_raw
                  (M.TlsHandshake (M.ClientHello client_ch))
                  client_ch_raw /\
                CS.raw_records_exactly client_finished_raw T.Application_data 1
              returns False
              with _.
              (
                assert (CS.conn_events_raw_replay
                  server_model0
                  server.CS.cs_event_log
                  server.CS.cs_wire_log.CL.raw_sent
                  server.CS.cs_wire_log.CL.raw_received
                  server.CS.cs_model);
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
                     CL.message_direction = CL.Received;
                     CL.message_value = M.TlsChangeCipherSpec;
                   }) ::
                   server_rest)
                  server.CS.cs_wire_log.CL.raw_sent
                  server.CS.cs_wire_log.CL.raw_received
                  server.CS.cs_model);
                PNTRB.lemma_server_start_client_hello_select_shared_then_received_change_cipher_spec_raw_slices
                  server_model0
                  server_ch
                  selection
                  server_shared
                  server_rest
                  server.CS.cs_wire_log.CL.raw_sent
                  server.CS.cs_wire_log.CL.raw_received
                  server.CS.cs_model;
                eliminate exists server_ch_raw ccs_raw server_received_tail.
                  Seq.equal
                    server.CS.cs_wire_log.CL.raw_received
                    (B.append server_ch_raw (B.append ccs_raw server_received_tail)) /\
                  CS.received_cleartext_tls_message_raw
                    (M.TlsHandshake (M.ClientHello server_ch))
                    server_ch_raw /\
                  CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
                returns False
                with _.
                (
                  assert (Seq.equal
                    client.CS.cs_wire_log.CL.raw_sent
                    server.CS.cs_wire_log.CL.raw_received);
                  PNTRB.lemma_equal_stream_after_client_hello_application_data_not_change_cipher_spec
                    client.CS.cs_wire_log.CL.raw_sent
                    server.CS.cs_wire_log.CL.raw_received
                    client_ch
                    server_ch
                    client_ch_raw
                    client_finished_raw
                    server_ch_raw
                    ccs_raw
                    server_received_tail
                )
              )
            | CL.Sent ->
              let client_tail =
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
                [] in
              let client_model0 =
                CS.initial_model client.CS.cs_model.CS.model_config in
              let server_model0 =
                CS.initial_model server.CS.cs_model.CS.model_config in
              assert (CS.conn_events_raw_replay
                client_model0
                client.CS.cs_event_log
                client.CS.cs_wire_log.CL.raw_sent
                client.CS.cs_wire_log.CL.raw_received
                client.CS.cs_model);
              assert (CS.conn_events_raw_replay
                client_model0
                (CS.ConnLocalEvent (CS.LocalStartHandshake start) ::
                 CS.ConnNetworkEvent ({
                   CL.message_direction = CL.Sent;
                   CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
                 }) ::
                 CS.ConnNetworkEvent ({
                   CL.message_direction = CL.Received;
                   CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
                 }) ::
                 CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) ::
                 client_tail)
                client.CS.cs_wire_log.CL.raw_sent
                client.CS.cs_wire_log.CL.raw_received
                client.CS.cs_model);
              PNTRB.lemma_client_prefix_raw_slices
                client_model0
                start
                client_ch
                client_sh
                client_shared
                client_tail
                client.CS.cs_wire_log.CL.raw_sent
                client.CS.cs_wire_log.CL.raw_received
                client.CS.cs_model;
              eliminate exists client_ch_raw client_sh_raw client_sent_tail client_received_tail.
                Seq.equal
                  client.CS.cs_wire_log.CL.raw_sent
                  (B.append client_ch_raw client_sent_tail) /\
                Seq.equal
                  client.CS.cs_wire_log.CL.raw_received
                  (B.append client_sh_raw client_received_tail) /\
                CS.cleartext_tls_message_raw
                  (M.TlsHandshake (M.ClientHello client_ch))
                  client_ch_raw /\
                CS.received_cleartext_tls_message_raw
                  (M.TlsHandshake (M.ServerHello client_sh))
                  client_sh_raw
              returns False
              with _.
              (
                assert (CS.conn_events_raw_replay
                  server_model0
                  server.CS.cs_event_log
                  server.CS.cs_wire_log.CL.raw_sent
                  server.CS.cs_wire_log.CL.raw_received
                  server.CS.cs_model);
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
                     CL.message_value = M.TlsChangeCipherSpec;
                   }) ::
                   server_rest)
                  server.CS.cs_wire_log.CL.raw_sent
                  server.CS.cs_wire_log.CL.raw_received
                  server.CS.cs_model);
                PNTRB.lemma_server_start_client_hello_select_shared_then_sent_change_cipher_spec_raw_slice
                  server_model0
                  server_ch
                  selection
                  server_shared
                  server_rest
                  server.CS.cs_wire_log.CL.raw_sent
                  server.CS.cs_wire_log.CL.raw_received
                  server.CS.cs_model;
                eliminate exists ccs_raw server_sent_tail.
                  Seq.equal
                    server.CS.cs_wire_log.CL.raw_sent
                    (B.append ccs_raw server_sent_tail) /\
                  CS.cleartext_tls_message_raw M.TlsChangeCipherSpec ccs_raw
                returns False
                with _.
                (
                  assert (Seq.equal
                    server.CS.cs_wire_log.CL.raw_sent
                    client.CS.cs_wire_log.CL.raw_received);
                  PNTRB.lemma_equal_stream_head_received_server_hello_not_change_cipher_spec
                    client.CS.cs_wire_log.CL.raw_received
                    server.CS.cs_wire_log.CL.raw_sent
                    client_sh
                    client_sh_raw
                    client_received_tail
                    ccs_raw
                    server_sent_tail
                )
              )
            )
          | _ -> ())
        | _ -> ());
        assert (~ (exists m.
          e4_server == CS.ConnNetworkEvent m /\
          m.CL.message_value == M.TlsChangeCipherSpec));
        assert (server_fifth_event_not_change_cipher_spec16 server)
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_prefix
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
      (ensures paired_no_tail_role_local_client_shared_prefix client server)
=
  PNTCS.lemma_client_no_tail_fourth_event_derive_shared_secret_clean client;
  lemma_clean16_no_tail_valid_byte_traces_server_second_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSS.lemma_server_no_tail_second_event_client_hello_if_not_ccs16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_server_selection_prefix
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
      (ensures paired_no_tail_role_local_client_shared_server_selection_prefix client server)
=
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_prefix
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_clean16_no_tail_valid_byte_traces_server_third_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSC.lemma_server_no_tail_third_event_select_parameters_if_not_ccs16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_server_shared_prefix
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
      (ensures paired_no_tail_role_local_client_shared_server_shared_prefix client server)
=
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_server_selection_prefix
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_clean16_no_tail_valid_byte_traces_server_fourth_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSC.lemma_server_no_tail_fourth_event_derive_shared_secret_if_not_ccs16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_handshake_install_server_hello_prefix
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
        paired_no_tail_role_local_client_handshake_install_server_hello_prefix
          client
          server)
=
  PNTCS.lemma_client_no_tail_fifth_event_handshake_traffic_install_clean client;
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_server_shared_prefix
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_clean16_no_tail_valid_byte_traces_server_fifth_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSC.lemma_server_no_tail_fifth_event_server_hello_if_not_ccs16 server

let lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_hello_prefix
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
        paired_no_tail_role_local_client_two_handshake_installs_server_hello_prefix
          client
          server)
=
  PNTCPS.lemma_client_no_tail_fifth_and_sixth_events_handshake_traffic_install_clean
    client;
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_server_shared_prefix
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_clean16_no_tail_valid_byte_traces_server_fifth_event_not_change_cipher_spec
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTSC.lemma_server_no_tail_fifth_event_server_hello_if_not_ccs16 server

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
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:GSH.serverHello)
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
  (client_ch:GCH.clientHello)
  (client_sh:GSH.serverHello)
  (client_shared:C.x25519_shared_secret)
  (client_rest:list CS.conn_event)
  (server_ch:GCH.clientHello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (server_sh:GSH.serverHello)
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

let lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_raw_wire_bridge
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
        paired_no_tail_normalized_cleartext_raw_wire_bridge_clean16
          client
          server)
=
  lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_hello_prefix
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  assert (TLS13.Impl.Client.Types.client_end_to_end_invariant client);
  assert (CS.connection_state_raw_event_replay_consistent client);
  eliminate exists client_start client_ch client_sh client_shared e4 e5 client_tail.
    client.CS.cs_event_log ==
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
      e4 ::
      e5 ::
      client_tail /\
    PNI.client_no_tail_handshake_traffic_install_event e4 /\
    PNI.client_no_tail_handshake_traffic_install_event e5
  returns paired_no_tail_normalized_cleartext_raw_wire_bridge_clean16 client server
  with _.
  (
    eliminate exists server_ch selection server_shared server_sh server_tail.
      server.CS.cs_event_log ==
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
        server_tail
    returns paired_no_tail_normalized_cleartext_raw_wire_bridge_clean16 client server
    with _.
    (
      let client_rest = e4 :: e5 :: client_tail in
      let client_model0 =
        CS.initial_model client.CS.cs_model.CS.model_config in
      assert (CS.conn_events_raw_replay
        client_model0
        client.CS.cs_event_log
        client.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received
        client.CS.cs_model);
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
      PNTRB.lemma_client_prefix_sent_client_hello_supported
        client_model0
        client_start
        client_ch
        client_sh
        client_shared
        client_rest
        client.CS.cs_wire_log.CL.raw_sent
        client.CS.cs_wire_log.CL.raw_received
        client.CS.cs_model;
      assert (WFL.supported_client_hello_wire_profile client_ch);
      assert (PNTRB.role_local_cleartext_prefix_shape
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
        server_tail);
      lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_raw_wire_bridge_from_role_local_prefix
        client_initial
        server_initial
        client
        server
        client_received
        client_sent
        server_received
        server_sent
        client_start
        client_ch
        client_sh
        client_shared
        client_rest
        server_ch
        selection
        server_shared
        server_sh
        server_tail;
      assert (PNTRB.normalized_cleartext_raw_wire_bridge
        client_ch
        server_ch
        client_sh
        server_sh);
      assert (exists
        client_start0
        client_ch0
        client_sh0
        client_shared0
        client_rest0
        server_ch0
        selection0
        server_shared0
        server_sh0
        server_rest0.
        PNTRB.role_local_cleartext_prefix_shape
          client
          server
          client_start0
          client_ch0
          client_sh0
          client_shared0
          client_rest0
          server_ch0
          selection0
          server_shared0
          server_sh0
          server_rest0 /\
        WFL.supported_client_hello_wire_profile client_ch0 /\
        PNTRB.normalized_cleartext_raw_wire_bridge
          client_ch0
          server_ch0
          client_sh0
          server_sh0)
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_replay_suffixes
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
        paired_no_tail_normalized_cleartext_replay_suffixes_clean16
          client
          server)
=
  lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_raw_wire_bridge
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_clean16_no_tail_valid_byte_traces_paired_wire_logs
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_clean16_no_tail_valid_byte_traces_preserve_connection_state_replay_consistent
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
  assert (CS.connection_state_sent_seal_replay_consistent client);
  assert (CS.connection_state_received_decode_replay_consistent client);
  assert (CS.connection_state_sent_seal_replay_consistent server);
  assert (CS.connection_state_received_decode_replay_consistent server);
  assert (CS.paired_wire_logs client server);
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
      server_sh
  returns paired_no_tail_normalized_cleartext_replay_suffixes_clean16 client server
  with _.
  (
    let client_model0 =
      CS.initial_model client.CS.cs_model.CS.model_config in
    let server_model0 =
      CS.initial_model server.CS.cs_model.CS.model_config in
    let client_ev0 = CS.ConnLocalEvent (CS.LocalStartHandshake client_start) in
    let client_ev1 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
      }) in
    let client_ev2 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
      }) in
    let client_ev3 =
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared) in
    let server_ev0 = CS.ConnLocalEvent CS.LocalStartServer in
    let server_ev1 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
      }) in
    let server_ev2 =
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) in
    let server_ev3 =
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) in
    let server_ev4 =
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
      }) in
    let client_prefix =
      client_ev0 :: client_ev1 :: client_ev2 :: client_ev3 :: [] in
    let server_prefix =
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [] in
    let client_full_sent = client.CS.cs_wire_log.CL.raw_sent in
    let client_full_received = client.CS.cs_wire_log.CL.raw_received in
    let server_full_sent = server.CS.cs_wire_log.CL.raw_sent in
    let server_full_received = server.CS.cs_wire_log.CL.raw_received in
    FStar.List.Tot.Properties.append_cons_l
      client_ev0
      (client_ev1 :: client_ev2 :: client_ev3 :: [])
      client_rest;
    FStar.List.Tot.Properties.append_cons_l
      client_ev1
      (client_ev2 :: client_ev3 :: [])
      client_rest;
    FStar.List.Tot.Properties.append_cons_l
      client_ev2
      (client_ev3 :: [])
      client_rest;
    FStar.List.Tot.Properties.append_cons_l client_ev3 [] client_rest;
    FStar.List.Tot.Properties.append_nil_l client_rest;
    assert (FStar.List.Tot.append client_prefix client_rest ==
      client_ev0 :: client_ev1 :: client_ev2 :: client_ev3 :: client_rest);
    FStar.List.Tot.Properties.append_cons_l
      server_ev0
      (server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 :: [])
      server_rest;
    FStar.List.Tot.Properties.append_cons_l
      server_ev1
      (server_ev2 :: server_ev3 :: server_ev4 :: [])
      server_rest;
    FStar.List.Tot.Properties.append_cons_l
      server_ev2
      (server_ev3 :: server_ev4 :: [])
      server_rest;
    FStar.List.Tot.Properties.append_cons_l
      server_ev3
      (server_ev4 :: [])
      server_rest;
    FStar.List.Tot.Properties.append_cons_l server_ev4 [] server_rest;
    FStar.List.Tot.Properties.append_nil_l server_rest;
    assert (FStar.List.Tot.append server_prefix server_rest ==
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
      server_rest);
    assert (client.CS.cs_event_log ==
      client_ev0 :: client_ev1 :: client_ev2 :: client_ev3 :: client_rest);
    assert (server.CS.cs_event_log ==
      server_ev0 :: server_ev1 :: server_ev2 :: server_ev3 :: server_ev4 ::
      server_rest);
    assert (FStar.List.Tot.append client_prefix client_rest ==
      client.CS.cs_event_log);
    assert (FStar.List.Tot.append server_prefix server_rest ==
      server.CS.cs_event_log);
    assert (server_prefix ==
      PWSeg.server_cleartext_handshake_prefix_events
        server_ch
        selection
        server_shared
        server_sh);
    assert (client_prefix ==
      PWSeg.client_cleartext_handshake_prefix_events
        client_start
        client_ch
        client_sh
        client_shared);
    assert (Seq.equal server_full_sent client_full_received);
    assert (Seq.equal client_full_sent server_full_received);
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
      client_full_sent
      client_full_received
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
      server_full_sent
      server_full_received
      server.CS.cs_model);
    PNTRB.lemma_server_cleartext_prefix_step_models_from_raw_replay
      server_model0
      server_ch
      selection
      server_shared
      server_sh
      server_rest
      server_full_sent
      server_full_received
      server.CS.cs_model;
    assert (exists sm1 sm2 sm3 sm4 sm5 ts tr.
      CS.step_model
        server_model0
        (CS.ConnLocalEvent CS.LocalStartServer) == Some sm1 /\
      CS.step_model
        sm1
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        })) == Some sm2 /\
      CS.step_model
        sm2
        (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
        Some sm3 /\
      CS.step_model
        sm3
        (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
        Some sm4 /\
      CS.step_model
        sm4
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
        })) == Some sm5 /\
      CS.conn_events_raw_replay
        sm5
        server_rest
        ts
        tr
        server.CS.cs_model);
    eliminate exists
      server_model1
      server_model2
      server_model3
      server_model4
      server_model5
      server_tail_sent
      server_tail_received.
      CS.step_model
        server_model0
        (CS.ConnLocalEvent CS.LocalStartServer) == Some server_model1 /\
      CS.step_model
        server_model1
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        })) == Some server_model2 /\
      CS.step_model
        server_model2
        (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection)) ==
        Some server_model3 /\
      CS.step_model
        server_model3
        (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared)) ==
        Some server_model4 /\
      CS.step_model
        server_model4
        (CS.ConnNetworkEvent ({
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.ServerHello server_sh);
        })) == Some server_model5 /\
      CS.conn_events_raw_replay
        server_model5
        server_rest
        server_tail_sent
        server_tail_received
        server.CS.cs_model
    returns paired_no_tail_normalized_cleartext_replay_suffixes_clean16 client server
    with _.
    (
      PNTRB.lemma_client_cleartext_prefix_step_models_from_raw_replay
        client_model0
        client_start
        client_ch
        client_sh
        client_shared
        client_rest
        client_full_sent
        client_full_received
        client.CS.cs_model;
      eliminate exists
        client_model1
        client_model2
        client_model3
        client_model4
        client_tail_sent
        client_tail_received.
        CS.step_model
          client_model0
          (CS.ConnLocalEvent (CS.LocalStartHandshake client_start)) ==
          Some client_model1 /\
        CS.step_model
          client_model1
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello client_ch);
          })) == Some client_model2 /\
        CS.step_model
          client_model2
          (CS.ConnNetworkEvent ({
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.ServerHello client_sh);
          })) == Some client_model3 /\
        CS.step_model
          client_model3
          (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared)) ==
          Some client_model4 /\
        CS.conn_events_raw_replay
          client_model4
          client_rest
          client_tail_sent
          client_tail_received
          client.CS.cs_model
      returns paired_no_tail_normalized_cleartext_replay_suffixes_clean16 client server
      with _.
      (
        eliminate exists
          client_ch_raw
          server_ch_raw
          client_sh_raw
          server_sh_raw.
          Seq.equal client_ch_raw server_ch_raw /\
          Seq.equal server_sh_raw client_sh_raw /\
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
        returns paired_no_tail_normalized_cleartext_replay_suffixes_clean16 client server
        with _.
        (
          PWSeg.lemma_same_endpoint_replay_split_prefixes_equal_uniform_server_cleartext_handshake_prefix
            server_model0
            server_ch
            selection
            server_shared
            server_sh
            server_rest
            server_model1
            server_model2
            server_model3
            server_model4
            server_model5;
          assert (PWSeg.same_endpoint_replay_split_prefixes_equal
            server_model0
            server_prefix
            server_rest
            server_full_sent
            server_full_received
            server.CS.cs_model);
          PWSeg.lemma_same_endpoint_replay_split_prefixes_equal_uniform_client_cleartext_handshake_prefix
            client_model0
            client_start
            client_ch
            client_sh
            client_shared
            client_rest
            client_model1
            client_model2
            client_model3
            client_model4;
          assert (PWSeg.same_endpoint_replay_split_prefixes_equal
            client_model0
            client_prefix
            client_rest
            client_full_sent
            client_full_received
            client.CS.cs_model);
          PWSeg.lemma_paired_replay_split_prefixes_equal_uniform_normalized_cleartext_handshake_prefix
            server_model0
            client_model0
            client_start
            client_ch
            server_ch
            selection
            server_shared
            client_shared
            server_sh
            client_sh
            server_rest
            client_rest
            server_model1
            server_model2
            server_model3
            server_model4
            server_model5
            client_model1
            client_model2
            client_model3
            client_model4
            client_ch_raw
            server_ch_raw
            client_sh_raw
            server_sh_raw;
          assert (PWSeg.paired_replay_split_prefixes_equal_with_full_streams
            server_model0
            client_model0
            server_prefix
            server_rest
            client_prefix
            client_rest
            server_full_sent
            server_full_received
            client_full_sent
            client_full_received
            server.CS.cs_model
            client.CS.cs_model);
          PWSeg.lemma_paired_replay_split_prefixes_equal_from_full_streams
            server_model0
            client_model0
            server_prefix
            server_rest
            client_prefix
            client_rest
            server_full_sent
            server_full_received
            client_full_sent
            client_full_received
            server.CS.cs_model
            client.CS.cs_model;
          assert (PWSeg.paired_replay_split_prefixes_equal
            server_model0
            client_model0
            server_prefix
            server_rest
            client_prefix
            client_rest
            server_full_sent
            server_full_received
            client_full_sent
            client_full_received
            server.CS.cs_model
            client.CS.cs_model);
          assert (CS.conn_events_sent_seal_replay
            server_model0
            (FStar.List.Tot.append server_prefix server_rest)
            server_full_sent
            server_full_received
            server.CS.cs_model);
          assert (CS.conn_events_received_decode_replay
            server_model0
            (FStar.List.Tot.append server_prefix server_rest)
            server_full_sent
            server_full_received
            server.CS.cs_model);
          assert (CS.conn_events_sent_seal_replay
            client_model0
            (FStar.List.Tot.append client_prefix client_rest)
            client_full_sent
            client_full_received
            client.CS.cs_model);
          assert (CS.conn_events_received_decode_replay
            client_model0
            (FStar.List.Tot.append client_prefix client_rest)
            client_full_sent
            client_full_received
            client.CS.cs_model);
          PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
            server_model0
            server_prefix
            server_rest
            server_full_sent
            server_full_received
            server.CS.cs_model
            (fun
              sent_mid
              received_mid
              sent_prefix_sent
              sent_prefix_received
              sent_suffix_sent
              sent_suffix_received
              received_prefix_sent
              received_prefix_received
              received_suffix_sent
              received_suffix_received ->
              assert (Seq.equal sent_prefix_sent received_prefix_sent);
              assert (Seq.equal sent_prefix_received received_prefix_received));
          eliminate exists
            server_mid
            server_prefix_sent
            server_prefix_received
            server_suffix_sent
            server_suffix_received.
            Seq.equal
              server_full_sent
              (B.append server_prefix_sent server_suffix_sent) /\
            Seq.equal
              server_full_received
              (B.append server_prefix_received server_suffix_received) /\
            CS.conn_events_sent_seal_replay
              server_model0
              server_prefix
              server_prefix_sent
              server_prefix_received
              server_mid /\
            CS.conn_events_sent_seal_replay
              server_mid
              server_rest
              server_suffix_sent
              server_suffix_received
              server.CS.cs_model /\
            CS.conn_events_received_decode_replay
              server_model0
              server_prefix
              server_prefix_sent
              server_prefix_received
              server_mid /\
            CS.conn_events_received_decode_replay
              server_mid
              server_rest
              server_suffix_sent
              server_suffix_received
              server.CS.cs_model
          returns paired_no_tail_normalized_cleartext_replay_suffixes_clean16 client server
          with _.
          (
            PWSeg.lemma_conn_events_sent_seal_replay_server_cleartext_handshake_prefix_final_model
              server_model0
              server_ch
              selection
              server_shared
              server_sh
              server_model1
              server_model2
              server_model3
              server_model4
              server_model5
              server_prefix_sent
              server_prefix_received
              server_mid;
            assert (server_mid == server_model5);
            PWR.lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes
              client_model0
              client_prefix
              client_rest
              client_full_sent
              client_full_received
              client.CS.cs_model
              (fun
                sent_mid
                received_mid
                sent_prefix_sent
                sent_prefix_received
                sent_suffix_sent
                sent_suffix_received
                received_prefix_sent
                received_prefix_received
                received_suffix_sent
                received_suffix_received ->
                assert (Seq.equal sent_prefix_sent received_prefix_sent);
                assert (Seq.equal sent_prefix_received received_prefix_received));
            eliminate exists
              client_mid
              client_prefix_sent
              client_prefix_received
              client_suffix_sent
              client_suffix_received.
              Seq.equal
                client_full_sent
                (B.append client_prefix_sent client_suffix_sent) /\
              Seq.equal
                client_full_received
                (B.append client_prefix_received client_suffix_received) /\
              CS.conn_events_sent_seal_replay
                client_model0
                client_prefix
                client_prefix_sent
                client_prefix_received
                client_mid /\
              CS.conn_events_sent_seal_replay
                client_mid
                client_rest
                client_suffix_sent
                client_suffix_received
                client.CS.cs_model /\
              CS.conn_events_received_decode_replay
                client_model0
                client_prefix
                client_prefix_sent
                client_prefix_received
                client_mid /\
              CS.conn_events_received_decode_replay
                client_mid
                client_rest
                client_suffix_sent
                client_suffix_received
                client.CS.cs_model
            returns paired_no_tail_normalized_cleartext_replay_suffixes_clean16 client server
            with _.
            (
              PWSeg.lemma_conn_events_sent_seal_replay_client_cleartext_handshake_prefix_final_model
                client_model0
                client_start
                client_ch
                client_sh
                client_shared
                client_model1
                client_model2
                client_model3
                client_model4
                client_prefix_sent
                client_prefix_received
                client_mid;
              assert (client_mid == client_model4);
              assert (
                Seq.equal server_prefix_sent client_prefix_received /\
                Seq.equal client_prefix_sent server_prefix_received);
              PWR.lemma_paired_replay_suffixes_equal_from_equal_prefixes
                server_full_sent
                server_full_received
                client_full_sent
                client_full_received
                server_prefix_sent
                server_prefix_received
                server_suffix_sent
                server_suffix_received
                client_prefix_sent
                client_prefix_received
                client_suffix_sent
                client_suffix_received;
              assert (Seq.equal server_suffix_sent client_suffix_received);
              assert (Seq.equal client_suffix_sent server_suffix_received);
              introduce exists
                (client_start':CS.handshake_start)
                (client_ch':GCH.clientHello)
                (client_sh':GSH.serverHello)
                (client_shared':C.x25519_shared_secret)
                (client_model1':CS.connection_model)
                (client_model2':CS.connection_model)
                (client_model3':CS.connection_model)
                (client_model4':CS.connection_model)
                (client_rest':list CS.conn_event)
                (server_ch':GCH.clientHello)
                (selection':CS.server_handshake_selection)
                (server_shared':C.x25519_shared_secret)
                (server_sh':GSH.serverHello)
                (server_model1':CS.connection_model)
                (server_model2':CS.connection_model)
                (server_model3':CS.connection_model)
                (server_model4':CS.connection_model)
                (server_model5':CS.connection_model)
                (server_rest':list CS.conn_event)
                (server_suffix_sent':B.bytes)
                (server_suffix_received':B.bytes)
                (client_suffix_sent':B.bytes)
                (client_suffix_received':B.bytes).
                CS.step_model
                  client_model0
                  (CS.ConnLocalEvent (CS.LocalStartHandshake client_start')) ==
                  Some client_model1' /\
                CS.step_model
                  client_model1'
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Sent;
                    CL.message_value = M.TlsHandshake (M.ClientHello client_ch');
                  }) == Some client_model2' /\
                CS.step_model
                  client_model2'
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ServerHello client_sh');
                  }) == Some client_model3' /\
                CS.step_model
                  client_model3'
                  (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret client_shared')) ==
                  Some client_model4' /\
                CS.step_model
                  server_model0
                  (CS.ConnLocalEvent CS.LocalStartServer) == Some server_model1' /\
                CS.step_model
                  server_model1'
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Received;
                    CL.message_value = M.TlsHandshake (M.ClientHello server_ch');
                  }) == Some server_model2' /\
                CS.step_model
                  server_model2'
                  (CS.ConnLocalEvent (CS.LocalSelectServerParameters selection')) ==
                  Some server_model3' /\
                CS.step_model
                  server_model3'
                  (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared')) ==
                  Some server_model4' /\
                CS.step_model
                  server_model4'
                  (CS.ConnNetworkEvent {
                    CL.message_direction = CL.Sent;
                    CL.message_value = M.TlsHandshake (M.ServerHello server_sh');
                  }) == Some server_model5' /\
                FStar.List.Tot.append
                  (PWSeg.server_cleartext_handshake_prefix_events
                    server_ch'
                    selection'
                    server_shared'
                    server_sh')
                  server_rest' == server.CS.cs_event_log /\
                FStar.List.Tot.append
                  (PWSeg.client_cleartext_handshake_prefix_events
                    client_start'
                    client_ch'
                    client_sh'
                    client_shared')
                  client_rest' == client.CS.cs_event_log /\
                Seq.equal server_suffix_sent' client_suffix_received' /\
                Seq.equal client_suffix_sent' server_suffix_received' /\
                CS.conn_events_sent_seal_replay
                  server_model5'
                  server_rest'
                  server_suffix_sent'
                  server_suffix_received'
                  server.CS.cs_model /\
                CS.conn_events_received_decode_replay
                  server_model5'
                  server_rest'
                  server_suffix_sent'
                  server_suffix_received'
                  server.CS.cs_model /\
                CS.conn_events_sent_seal_replay
                  client_model4'
                  client_rest'
                  client_suffix_sent'
                  client_suffix_received'
                  client.CS.cs_model /\
                CS.conn_events_received_decode_replay
                  client_model4'
                  client_rest'
                  client_suffix_sent'
                  client_suffix_received'
                  client.CS.cs_model
              with
                client_start
                client_ch
                client_sh
                client_shared
                client_model1
                client_model2
                client_model3
                client_model4
                client_rest
                server_ch
                selection
                server_shared
                server_sh
                server_model1
                server_model2
                server_model3
                server_model4
                server_model5
                server_rest
                server_suffix_sent
                server_suffix_received
                client_suffix_sent
                client_suffix_received
              and ()
            )
          )
        )
      )
    )
  )

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
