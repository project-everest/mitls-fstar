module TLS13.Impl.Driver.PairingNoTailServerFlightStaged

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PNTCRR = TLS13.Impl.Driver.PairingNoTailClientReceivedRawShape
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation

(**
  Server-flight split milestone: the server's real wire
  [CertificateVerify] send is in the post-[ServerHello] suffix, not in the
  cleartext prefix.
**)
noextract
let server_post_server_hello_sent_certificate_verify_split
  (server:CS.connection_state)
  : prop =
  exists ch selection server_shared sh e5 e6 rest prefix cv suffix.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
        (PWSeg.server_cleartext_handshake_prefix_events
          ch
          selection
          server_shared
          sh)
        (e5 :: e6 :: rest) /\
    FStar.List.Tot.length rest == 9 /\
    e5 :: e6 :: rest ==
      FStar.List.Tot.append
        prefix
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
        } :: suffix)

(**
  Narrow SERVER encrypted-flight staging package derivable directly from the
  clean16 paired byte-trace assumptions.

  This does not yet construct the full
  [ProtectedWireBase.server_encrypted_flight_replay_events] slice.  It packages
  the verified normalized cleartext suffix replays, paired raw streams, the
  four protected server-flight raw records on both endpoints, the corrected
  post-[ServerHello] length split, and a real [Sent CertificateVerify] event
  inside that post-[ServerHello] suffix.
**)
noextract
let clean16_server_encrypted_flight_staged_milestone
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  CS.paired_wire_logs client server /\
  PNTN.paired_no_tail_normalized_cleartext_replay_suffixes_clean16
    client
    server /\
  PNTPH.server_no_tail_post_server_hello_suffix_shape server /\
  PNTN.server_sent_cleartext_and_server_flight_raw_slices server /\
  PNTCRR.client_received_cleartext_and_server_flight_raw_slices client /\
  PNTN.server_received_cleartext_and_client_finished_raw_slices server /\
  PNTN.server_sent_certificate_verify_event_split server /\
  server_post_server_hello_sent_certificate_verify_split server

val lemma_server_post_server_hello_sent_certificate_verify_split
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTPH.server_no_tail_post_server_hello_suffix_shape server /\
        PNTN.server_sent_certificate_verify_event_split server)
      (ensures
        server_post_server_hello_sent_certificate_verify_split server)

val lemma_clean16_no_tail_valid_byte_traces_server_encrypted_flight_staged_milestone
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
        clean16_server_encrypted_flight_staged_milestone client server)
