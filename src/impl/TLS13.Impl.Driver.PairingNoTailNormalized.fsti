module TLS13.Impl.Driver.PairingNoTailNormalized

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CVE = TLS13.ConnectionState.ClientCertificateVerifyEvent
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
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
module PSNB = TLS13.Impl.Driver.PairingStagedNormalizedBoundary
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation
module Seq = FStar.Seq
module SCVE = TLS13.ConnectionState.ServerCertificateVerifyEvent
module SM = Common.StateMachine
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module T = TLS13.Types
module WF = Common.WireFormat
module WFSM = Common.WireFormatStateMachine
module WFL = TLS13.Spec.WireFormatLemmas

(**
  Clean no-tail byte-trace inputs for the intended top-level theorem.

  This predicate deliberately does not mention:
  - exact [PairingTraceShape] event-log shape,
  - exact cross-endpoint ClientHello/ServerHello record equality,
  - caller-supplied protected projection/replay witnesses.

  The remaining theorem in this module is an intermediate milestone: it still
  requires the separately-proved normalized replay boundary.  The open proof
  obligation is to derive that boundary from the clean inputs below.
**)
noextract
let paired_supported_no_tail_valid_byte_traces_clean
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  client_initial == CS.initial client_initial.CS.cs_model.CS.model_config /\
  server_initial == CS.initial server_initial.CS.cs_model.CS.model_config /\
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
  Seq.equal server_sent client_received /\
  PNT.paired_no_tail_application_ready_boundary client server /\
  WFL.supported_client_config_wire_profile
    client.CS.cs_model.CS.model_config /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server

noextract
let paired_supported_no_tail_valid_byte_traces_clean16
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  client_initial == CS.initial client_initial.CS.cs_model.CS.model_config /\
  server_initial == CS.initial server_initial.CS.cs_model.CS.model_config /\
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
  Seq.equal server_sent client_received /\
  PNT.paired_no_tail_application_ready_boundary16 client server /\
  WFL.supported_client_config_wire_profile
    client.CS.cs_model.CS.model_config /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server

val lemma_clean_no_tail_valid_byte_traces_preserve_connection_state_consistent
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

val lemma_clean16_no_tail_valid_byte_traces_preserve_connection_state_consistent
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

val lemma_clean16_no_tail_valid_byte_traces_preserve_connection_state_replay_consistent
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

noextract
let paired_no_tail_role_local_start_and_final_witnesses
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCS.client_no_tail_start_spine client /\
  PNTCS.client_no_tail_final_model_witnesses client /\
  PNTSS.server_no_tail_start_spine server /\
  PNTSS.server_no_tail_final_model_witnesses server

noextract
let paired_no_tail_role_local_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCS.client_no_tail_start_spine client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_start_and_final_witnesses16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCS.client_no_tail_start_spine client /\
  PNTCS.client_no_tail_final_model_witnesses client /\
  PNTSS.server_no_tail_start_spine16 server /\
  PNTSS.server_no_tail_final_model_witnesses server

noextract
let paired_no_tail_role_local_client_two_handshake_installs_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_start client_ch client_sh client_shared e4 e5 client_rest.
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
      client_rest /\
    PNI.client_no_tail_handshake_traffic_install_event e4 /\
    PNI.client_no_tail_handshake_traffic_install_event e5) /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_client_handshake_install_cover_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_start client_ch client_sh client_shared e4 e5 client_rest.
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
      client_rest /\
    PNTCPS.client_no_tail_two_handshake_install_cover e4 e5) /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let server_second_event_not_change_cipher_spec16
  (server:CS.connection_state)
  : prop =
  exists e1 rest.
    server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer :: e1 :: rest /\
    ~ (exists m.
        e1 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec)

noextract
let server_third_event_not_change_cipher_spec16
  (server:CS.connection_state)
  : prop =
  exists ch e2 rest.
    server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      e2 ::
      rest /\
    ~ (exists m.
        e2 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec)

noextract
let server_fourth_event_not_change_cipher_spec16
  (server:CS.connection_state)
  : prop =
  exists ch selection e3 rest.
    server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
      e3 ::
      rest /\
    ~ (exists m.
        e3 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec)

noextract
let server_fifth_event_not_change_cipher_spec16
  (server:CS.connection_state)
  : prop =
  exists ch selection server_shared e4 rest.
    server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello ch);
      }) ::
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
      CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
      e4 ::
      rest /\
    ~ (exists m.
        e4 == CS.ConnNetworkEvent m /\
        m.CL.message_value == M.TlsChangeCipherSpec)

noextract
let paired_no_tail_role_local_client_first_protected_receive_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCPrS.client_no_tail_first_protected_receive_shape client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_client_second_protected_receive_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCPrS.client_no_tail_second_protected_receive_shape client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_client_certificate_validated_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCPrS.client_no_tail_certificate_validated_shape client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_client_certificate_verify_received_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCVS.client_no_tail_certificate_verify_received_shape client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_client_certificate_signature_verified_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCVS.client_no_tail_certificate_signature_verified_shape client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_client_server_finished_received_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCFS.client_no_tail_server_finished_received_shape client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_client_server_finished_verified_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCFS.client_no_tail_server_finished_verified_shape client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_client_application_installs_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCAS.client_no_tail_application_installs_shape client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let paired_no_tail_role_local_client_finished_sent_server_start_spine16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  PNTCAS.client_no_tail_finished_sent_shape client /\
  PNTSS.server_no_tail_start_spine16 server

noextract
let client_received_certificate_verify_event_split
  (client:CS.connection_state)
  : prop =
  exists prefix cv suffix.
    client.CS.cs_event_log ==
      FStar.List.Tot.append prefix
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      } :: suffix)

noextract
let server_sent_certificate_verify_event_split
  (server:CS.connection_state)
  : prop =
  exists prefix cv suffix.
    server.CS.cs_event_log ==
      FStar.List.Tot.append prefix
      (CS.ConnNetworkEvent {
        CL.message_direction = CL.Sent;
        CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
      } :: suffix)

val lemma_clean16_no_tail_valid_byte_traces_role_local_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_start_and_final_witnesses16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_handshake_install_cover_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_first_protected_receive_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_second_protected_receive_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_certificate_validated_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_certificate_verify_received_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_certificate_signature_verified_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_server_finished_received_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_server_finished_verified_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_application_installs_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_finished_sent_server_start_spine16
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

val lemma_clean16_no_tail_valid_byte_traces_client_sent_cleartext_and_finished_raw_slices
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

val lemma_clean16_no_tail_valid_byte_traces_client_received_cleartext_and_server_flight_raw_slices
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

noextract
let server_sent_cleartext_and_server_flight_raw_slices
  (server:CS.connection_state)
  : prop =
  exists
    (sh:M.server_hello)
    (ee:M.encrypted_extensions)
    (cert:M.certificate_msg)
    (cv:M.certificate_verify)
    (sf:M.finished)
    server_sh_raw
    ee_raw
    cert_raw
    cv_raw
    sf_raw.
    Seq.equal
      server.CS.cs_wire_log.CL.raw_sent
      (B.append
        server_sh_raw
        (B.append ee_raw (B.append cert_raw (B.append cv_raw sf_raw)))) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ServerHello sh))
      server_sh_raw /\
    CS.raw_records_exactly ee_raw T.ApplicationData 1 /\
    CS.raw_records_exactly cert_raw T.ApplicationData 1 /\
    CS.raw_records_exactly cv_raw T.ApplicationData 1 /\
    CS.raw_records_exactly sf_raw T.ApplicationData 1

noextract
let server_received_cleartext_and_client_finished_raw_slices
  (server:CS.connection_state)
  : prop =
  exists (ch:M.client_hello) (cf:M.finished) client_ch_raw client_finished_raw.
    Seq.equal
      server.CS.cs_wire_log.CL.raw_received
      (B.append client_ch_raw client_finished_raw) /\
    CS.cleartext_tls_message_raw
      (M.TlsHandshake (M.ClientHello ch))
      client_ch_raw /\
    CS.raw_records_exactly client_finished_raw T.ApplicationData 1

val lemma_clean16_no_tail_valid_byte_traces_server_sent_cleartext_and_server_flight_raw_slices
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

val lemma_clean16_no_tail_valid_byte_traces_server_received_cleartext_and_client_finished_raw_slices
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

(**
  Under the clean16 paired inputs, the client has recorded a genuine
  [hs_certificate_verify] witness.  The old server-side model-level
  local-sign bypass is closed ([CS.LocalSignCertificateVerify] no longer marks
  [hs_certificate_verify_verified]), but this client witness is still not by
  itself the full paired-byte-trace inversion needed for the normalized server
  protected-flight boundary: that final step must connect the protected raw
  ciphertext slices to the server's logged [Sent CertificateVerify] event and
  rule out extra no-op records in the clean/canonical trace.
**)
val lemma_clean16_no_tail_valid_byte_traces_client_certificate_verify_witness
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

val lemma_clean16_no_tail_valid_byte_traces_client_received_certificate_verify_event
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

val lemma_clean16_no_tail_valid_byte_traces_client_received_certificate_verify_event_split
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

val lemma_clean16_no_tail_valid_byte_traces_server_sent_certificate_verify_event
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

val lemma_clean16_no_tail_valid_byte_traces_server_sent_certificate_verify_event_split
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

noextract
let paired_no_tail_role_local_client_two_handshake_installs_server_start_spine16_and_client_certificate_verify_witness
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  paired_no_tail_role_local_client_two_handshake_installs_server_start_spine16
    client
    server /\
  Some? client.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_start_spine16_and_client_certificate_verify_witness
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

noextract
let paired_no_tail_role_local_cleartext_prefixes
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_start client_ch client_sh client_rest.
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
      client_rest) /\
  (exists server_ch server_rest.
    server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
      }) ::
      server_rest)

noextract
let paired_no_tail_role_local_client_shared_prefix
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_start client_ch client_sh client_shared client_rest.
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
      client_rest) /\
  (exists server_ch server_rest.
    server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
      }) ::
      server_rest)

noextract
let paired_no_tail_role_local_client_shared_server_selection_prefix
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_start client_ch client_sh client_shared client_rest.
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
      client_rest) /\
  (exists server_ch selection server_rest.
    server.CS.cs_event_log ==
      CS.ConnLocalEvent CS.LocalStartServer ::
      CS.ConnNetworkEvent ({
        CL.message_direction = CL.Received;
        CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
      }) ::
      CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
      server_rest)

noextract
let paired_no_tail_role_local_client_shared_server_shared_prefix
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_start client_ch client_sh client_shared client_rest.
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
        client_rest) /\
  (exists server_ch selection server_shared server_rest.
      server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
        server_rest)

noextract
let paired_no_tail_role_local_client_handshake_install_server_shared_prefix
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_start client_ch client_sh client_shared client_install client_rest.
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
        client_install ::
        client_rest /\
    PNI.client_no_tail_handshake_traffic_install_event client_install) /\
  (exists server_ch selection server_shared server_rest.
    server.CS.cs_event_log ==
        CS.ConnLocalEvent CS.LocalStartServer ::
        CS.ConnNetworkEvent ({
          CL.message_direction = CL.Received;
          CL.message_value = M.TlsHandshake (M.ClientHello server_ch);
        }) ::
        CS.ConnLocalEvent (CS.LocalSelectServerParameters selection) ::
        CS.ConnLocalEvent (CS.LocalDeriveSharedSecret server_shared) ::
        server_rest)

noextract
let paired_no_tail_role_local_client_handshake_install_server_hello_prefix
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_start client_ch client_sh client_shared client_install client_rest.
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
        client_install ::
        client_rest /\
    PNI.client_no_tail_handshake_traffic_install_event client_install) /\
  (exists server_ch selection server_shared server_sh server_rest.
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
        server_rest)

noextract
let paired_no_tail_role_local_client_two_handshake_installs_server_hello_prefix
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_start client_ch client_sh client_shared e4 e5 client_rest.
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
        client_rest /\
    PNI.client_no_tail_handshake_traffic_install_event e4 /\
    PNI.client_no_tail_handshake_traffic_install_event e5) /\
  (exists server_ch selection server_shared server_sh server_rest.
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
        server_rest)

val lemma_clean_no_tail_valid_byte_traces_role_local_start_and_final_witnesses
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

val lemma_clean_no_tail_valid_byte_traces_role_local_cleartext_prefixes
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

val lemma_clean_no_tail_valid_byte_traces_role_local_client_shared_prefix
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

val lemma_clean_no_tail_valid_byte_traces_role_local_client_shared_server_selection_prefix
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

val lemma_clean_no_tail_valid_byte_traces_role_local_client_shared_server_shared_prefix
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

val lemma_clean_no_tail_valid_byte_traces_role_local_client_handshake_install_server_shared_prefix
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

val lemma_clean_no_tail_valid_byte_traces_role_local_client_handshake_install_server_hello_prefix
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

val lemma_clean_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_hello_prefix
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

val lemma_clean_no_tail_valid_byte_traces_client_supported_hello_profile
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

val lemma_clean16_no_tail_valid_byte_traces_client_supported_hello_profile
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

val lemma_clean_no_tail_valid_byte_traces_invert_to_paired_serialized_traces
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

val lemma_clean16_no_tail_valid_byte_traces_invert_to_paired_serialized_traces
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

val lemma_clean16_no_tail_valid_byte_traces_invert_to_paired_wire_message_traces
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

val lemma_clean_no_tail_valid_byte_traces_paired_wire_logs
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

val lemma_clean16_no_tail_valid_byte_traces_paired_wire_logs
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

val lemma_clean16_no_tail_valid_byte_traces_server_second_event_not_change_cipher_spec
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

val lemma_clean16_no_tail_valid_byte_traces_server_third_event_not_change_cipher_spec
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

val lemma_clean16_no_tail_valid_byte_traces_server_fourth_event_not_change_cipher_spec
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

val lemma_clean16_no_tail_valid_byte_traces_server_fifth_event_not_change_cipher_spec
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_prefix
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_server_selection_prefix
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_shared_server_shared_prefix
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_handshake_install_server_hello_prefix
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

val lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_hello_prefix
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

val lemma_clean_no_tail_valid_byte_traces_normalized_cleartext_raw_wire_bridge_from_role_local_prefix
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

val lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_raw_wire_bridge_from_role_local_prefix
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

noextract
let paired_no_tail_normalized_cleartext_raw_wire_bridge_clean16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists
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

noextract
let paired_no_tail_normalized_cleartext_replay_suffixes_clean16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  exists
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
      (PWSeg.server_cleartext_handshake_prefix_events
        server_ch
        selection
        server_shared
        server_sh)
      server_rest == server.CS.cs_event_log /\
    FStar.List.Tot.append
      (PWSeg.client_cleartext_handshake_prefix_events
        client_start
        client_ch
        client_sh
        client_shared)
      client_rest == client.CS.cs_event_log /\
    Seq.equal server_suffix_sent client_suffix_received /\
    Seq.equal client_suffix_sent server_suffix_received /\
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

val lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_raw_wire_bridge
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

val lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_replay_suffixes
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

val lemma_paired_successful_handshake_normalized_replay_shape_from_clean_no_tail_valid_byte_traces_and_normalized_replay_boundary
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

val lemma_paired_successful_handshake_normalized_replay_shape_from_clean16_no_tail_valid_byte_traces_and_normalized_replay_boundary
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

val lemma_client_server_application_record_material_agrees_from_clean_no_tail_valid_byte_traces_and_normalized_replay_boundary
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

val lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_normalized_replay_boundary
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

val lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_normalized_staged_replay_boundary
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
