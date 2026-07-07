module TLS13.Impl.Driver.PairingNoTailServerFlightStaged

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module PNTCRR = TLS13.Impl.Driver.PairingNoTailClientReceivedRawShape
module PNTN = TLS13.Impl.Driver.PairingNoTailNormalized
module PNTPH = TLS13.Impl.Driver.PairingNoTailServerPostHelloShape
module PWSeg = TLS13.ConnectionState.ProtectedWireSegmentation

#push-options "--split_queries always --z3rlimit 10"

let sent_certificate_verify_event
  (cv:M.certificate_verify)
  : CS.conn_event =
  CS.ConnNetworkEvent {
    CL.message_direction = CL.Sent;
    CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
  }

noextract
let rec list_no_event
  (needle:CS.conn_event)
  (events:list CS.conn_event)
  : Tot prop
    (decreases events)
=
  match events with
  | [] -> True
  | ev :: rest ->
    ev <> needle /\ list_no_event needle rest

let rec lemma_split_after_prefix_no_event
  (prefix:list CS.conn_event)
  (rest:list CS.conn_event)
  (before:list CS.conn_event)
  (cv:M.certificate_verify)
  (after:list CS.conn_event)
  : Lemma
      (requires
        list_no_event (sent_certificate_verify_event cv) prefix /\
        FStar.List.Tot.append prefix rest ==
          FStar.List.Tot.append
            before
            (sent_certificate_verify_event cv :: after))
      (ensures
        exists before' after'.
          rest ==
            FStar.List.Tot.append
              before'
              (sent_certificate_verify_event cv :: after'))
      (decreases prefix)
=
  match prefix with
  | [] ->
    introduce exists (before':list CS.conn_event) (after':list CS.conn_event).
      rest ==
        FStar.List.Tot.append
          before'
          (sent_certificate_verify_event cv :: after')
    with before after and ()
  | ev :: prefix_tail ->
    match before with
    | [] ->
      assert (ev == sent_certificate_verify_event cv);
      assert False
    | before_hd :: before_tail ->
      assert (ev == before_hd);
      assert (
        FStar.List.Tot.append prefix_tail rest ==
          FStar.List.Tot.append
            before_tail
            (sent_certificate_verify_event cv :: after));
      lemma_split_after_prefix_no_event
        prefix_tail
        rest
        before_tail
        cv
        after

let lemma_server_cleartext_prefix_no_sent_certificate_verify
  (ch:M.client_hello)
  (selection:CS.server_handshake_selection)
  (server_shared:C.x25519_shared_secret)
  (sh:M.server_hello)
  (cv:M.certificate_verify)
  : Lemma
      (ensures
        list_no_event
          (sent_certificate_verify_event cv)
          (PWSeg.server_cleartext_handshake_prefix_events
            ch
            selection
            server_shared
            sh))
=
  assert_norm
    (list_no_event
      (sent_certificate_verify_event cv)
      (PWSeg.server_cleartext_handshake_prefix_events
        ch
        selection
        server_shared
        sh))

let lemma_server_post_server_hello_sent_certificate_verify_split
  (server:CS.connection_state)
  : Lemma
      (requires
        PNTPH.server_no_tail_post_server_hello_suffix_shape server /\
        PNTN.server_sent_certificate_verify_event_split server)
      (ensures
        server_post_server_hello_sent_certificate_verify_split server)
=
  eliminate exists
    server_ch
    selection
    server_shared
    server_sh
    e5
    e6
    rest.
    server.CS.cs_event_log ==
      FStar.List.Tot.append
      (PWSeg.server_cleartext_handshake_prefix_events
        server_ch
        selection
        server_shared
        server_sh)
      (e5 :: e6 :: rest) /\
    FStar.List.Tot.length rest == 9
  returns server_post_server_hello_sent_certificate_verify_split server
  with _.
  (
    eliminate exists prefix cv suffix.
      server.CS.cs_event_log ==
        FStar.List.Tot.append
          prefix
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          } :: suffix)
    returns server_post_server_hello_sent_certificate_verify_split server
    with _.
    (
      let server_prefix =
        PWSeg.server_cleartext_handshake_prefix_events
          server_ch
          selection
          server_shared
          server_sh in
      assert (
        sent_certificate_verify_event cv ==
          CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          });
      lemma_server_cleartext_prefix_no_sent_certificate_verify
        server_ch
        selection
        server_shared
        server_sh
        cv;
      lemma_split_after_prefix_no_event
        server_prefix
        (e5 :: e6 :: rest)
        prefix
        cv
        suffix;
      eliminate exists before' after'.
        e5 :: e6 :: rest ==
          FStar.List.Tot.append
            before'
            (sent_certificate_verify_event cv :: after')
      returns server_post_server_hello_sent_certificate_verify_split server
      with _.
      (
        assert (
          e5 :: e6 :: rest ==
            FStar.List.Tot.append
              before'
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
              } :: after'));
        introduce exists
          (ch':M.client_hello)
          (selection':CS.server_handshake_selection)
          (server_shared':C.x25519_shared_secret)
          (sh':M.server_hello)
          (e5':CS.conn_event)
          (e6':CS.conn_event)
          (rest':list CS.conn_event)
          (prefix':list CS.conn_event)
          (cv':M.certificate_verify)
          (suffix':list CS.conn_event).
          server.CS.cs_event_log ==
            FStar.List.Tot.append
              (PWSeg.server_cleartext_handshake_prefix_events
                ch'
                selection'
                server_shared'
                sh')
              (e5' :: e6' :: rest') /\
          FStar.List.Tot.length rest' == 9 /\
          e5' :: e6' :: rest' ==
            FStar.List.Tot.append
              prefix'
              (CS.ConnNetworkEvent {
                CL.message_direction = CL.Sent;
                CL.message_value = M.TlsHandshake (M.CertificateVerify cv');
              } :: suffix')
        with
          server_ch
          selection
          server_shared
          server_sh
          e5
          e6
          rest
          before'
          cv
          after'
        and ()
      )
    )
  )

let lemma_clean16_no_tail_valid_byte_traces_server_encrypted_flight_staged_milestone
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
=
  PNTN.lemma_clean16_no_tail_valid_byte_traces_paired_wire_logs
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_normalized_cleartext_replay_suffixes
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  TLS13.Impl.Driver.PairingNoTailServerPostHelloShape.lemma_clean16_no_tail_valid_byte_traces_server_post_server_hello_suffix_shape
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_server_sent_cleartext_and_server_flight_raw_slices
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_client_received_cleartext_and_server_flight_raw_slices
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_server_received_cleartext_and_client_finished_raw_slices
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  PNTN.lemma_clean16_no_tail_valid_byte_traces_server_sent_certificate_verify_event_split
    client_initial
    server_initial
    client
    server
    client_received
    client_sent
    server_received
    server_sent;
  lemma_server_post_server_hello_sent_certificate_verify_split server

#pop-options
