module TLS13.ConnectionState.ProtectedWireProjection

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CSL = TLS13.ConnectionState.Lemmas
module K = TLS13.Keys
module M = TLS13.Messages
module R = TLS13.Record.Spec
module RD = TLS13.Wire.Spec.RevealDecode
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module T = TLS13.Types
module Tr = TLS13.Transcript
module W = TLS13.Wire.Spec
module WF = TLS13.Wire.Spec.Reveal.Finished
module WFL = TLS13.Spec.WireFormatLemmas
module WRT = TLS13.Wire.Spec.Reveal.FinishedRoundTrip
module WU = TLS13.Wire.Spec.Reveal.Util

open TLS13.Spec.ConnectionState
open TLS13.ConnectionState.ProtectedWireBase

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_wire_equal_from_sent_seal_peer
  (sender:connection_model)
  (receiver:connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
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
        sent_single_protected_message_seal
          sender
          (M.TlsHandshake sent_msg)
          raw /\
        received_single_protected_message_decode
          receiver
          (M.TlsHandshake received_msg)
          raw /\
        protected_handshake_wire_round_trip_message received_msg)
      (ensures
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg))
=
  let sent_tls_msg = M.TlsHandshake sent_msg in
  CSL.lemma_received_record_opened_from_sent_single_protected_message_seal_peer
    sender
    receiver
    sent_tls_msg
    raw;
  eliminate exists (sent_outer:B.bytes).
    W.parse_record raw == Some (T.ApplicationData, sent_outer, B.length raw) /\
    received_record_opened
      receiver
      raw
      sent_outer
      (sent_tls_inner_plaintext_fragment sent_tls_msg)
  returns
    Seq.equal
      (W.serialize_handshake sent_msg)
      (W.serialize_handshake received_msg)
  with _.
  ( eliminate exists
      (received_outer:B.bytes)
      (opened:B.bytes)
      (plaintext:M.plaintext).
      W.parse_record_wire raw ==
        Some (T.ApplicationData, received_outer, B.length raw) /\
      received_record_opened receiver raw received_outer opened /\
      W.parse_plaintext opened == Some plaintext /\
      W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
        Some (M.TlsHandshake received_msg)
    returns
      Seq.equal
        (W.serialize_handshake sent_msg)
        (W.serialize_handshake received_msg)
    with _.
    ( W.lemma_parse_record_implies_parse_record_wire raw;
      assert (received_outer == sent_outer);
      eliminate exists (sent_read_state':R.direction_state).
        R.open_record
          receiver.model_record.record_read
          (record_header_aad raw)
          sent_outer ==
          Some (sent_tls_inner_plaintext_fragment sent_tls_msg, sent_read_state')
      returns
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg)
      with _.
      ( eliminate exists (received_read_state':R.direction_state).
          R.open_record
            receiver.model_record.record_read
            (record_header_aad raw)
            received_outer ==
            Some (opened, received_read_state')
        returns
          Seq.equal
            (W.serialize_handshake sent_msg)
            (W.serialize_handshake received_msg)
        with _.
        ( assert (opened == sent_tls_inner_plaintext_fragment sent_tls_msg);
          W.lemma_serialize_tls_message_handshake sent_msg;
          let sent_plaintext = {
            M.content_type = T.Handshake;
            M.fragment = W.serialize_handshake sent_msg;
          } in
          assert (sent_tls_inner_plaintext_fragment sent_tls_msg ==
                  W.serialize_plaintext sent_plaintext);
          W.lemma_parse_plaintext_serialize_plaintext sent_plaintext;
          assert (W.parse_plaintext
            (sent_tls_inner_plaintext_fragment sent_tls_msg) ==
            Some sent_plaintext);
          assert (plaintext == sent_plaintext);
          assert (W.parse_tls_message
            T.Handshake
            (W.serialize_handshake sent_msg) ==
            Some (M.TlsHandshake received_msg));
          match received_msg with
          | M.EncryptedExtensions _
          | M.Certificate _
          | M.CertificateVerify _ ->
            W.lemma_parse_tls_message_round_trip
              T.Handshake
              (W.serialize_handshake sent_msg)
          | M.Finished fin ->
            WRT.lemma_parse_finished_handshake_round_trip
              (W.serialize_handshake sent_msg)
              fin
          | _ ->
            assert False ) ) ) )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_handshake_wire_equal_from_event_projections_peer
  (sender:connection_model)
  (receiver:connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
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
        Seq.equal raw_sent raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        sent_event_seal_projection
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          raw_sent /\
        received_event_decode_projection
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          raw_received)
      (ensures
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg))
=
  match sent_msg, received_msg with
  | M.EncryptedExtensions _, M.EncryptedExtensions _
  | M.EncryptedExtensions _, M.Certificate _
  | M.EncryptedExtensions _, M.CertificateVerify _
  | M.EncryptedExtensions _, M.Finished _
  | M.Certificate _, M.EncryptedExtensions _
  | M.Certificate _, M.Certificate _
  | M.Certificate _, M.CertificateVerify _
  | M.Certificate _, M.Finished _
  | M.CertificateVerify _, M.EncryptedExtensions _
  | M.CertificateVerify _, M.Certificate _
  | M.CertificateVerify _, M.CertificateVerify _
  | M.CertificateVerify _, M.Finished _
  | M.Finished _, M.EncryptedExtensions _
  | M.Finished _, M.Certificate _
  | M.Finished _, M.CertificateVerify _
  | M.Finished _, M.Finished _ ->
    assert (network_message_is_cleartext CL.Sent (M.TlsHandshake sent_msg) == false);
    assert (network_message_is_cleartext CL.Received (M.TlsHandshake received_msg) == false);
    assert (protected_record_count CL.Sent (M.TlsHandshake sent_msg) == 1);
    assert (protected_record_count CL.Received (M.TlsHandshake received_msg) == 1);
    assert (sent_single_protected_message_seal
      sender
      (M.TlsHandshake sent_msg)
      raw_sent);
    assert (received_single_protected_message_decode
      receiver
      (M.TlsHandshake received_msg)
      raw_received);
    Seq.lemma_eq_elim raw_sent raw_received;
    assert (received_single_protected_message_decode
      receiver
      (M.TlsHandshake received_msg)
      raw_sent);
    lemma_protected_handshake_wire_equal_from_sent_seal_peer
      sender
      receiver
      sent_msg
      received_msg
      raw_sent
  | _, _ ->
    assert False
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_protected_finished_not_certificate_verify_from_event_projections_peer
  (sender:connection_model)
  (receiver:connection_model)
  (fin:M.finished)
  (cv:M.certificate_verify)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
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
        Seq.equal raw_sent raw_received /\
        sent_event_seal_projection
          sender
          (ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished fin);
          })
          raw_sent /\
        received_event_decode_projection
          receiver
          (ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          })
          raw_received)
      (ensures False)
=
  assert (network_message_is_cleartext CL.Sent (M.TlsHandshake (M.Finished fin)) == false);
  assert (network_message_is_cleartext CL.Received (M.TlsHandshake (M.CertificateVerify cv)) == false);
  assert (protected_record_count CL.Sent (M.TlsHandshake (M.Finished fin)) == 1);
  assert (protected_record_count CL.Received (M.TlsHandshake (M.CertificateVerify cv)) == 1);
  assert (sent_single_protected_message_seal
    sender
    (M.TlsHandshake (M.Finished fin))
    raw_sent);
  assert (received_single_protected_message_decode
    receiver
    (M.TlsHandshake (M.CertificateVerify cv))
    raw_received);
  Seq.lemma_eq_elim raw_sent raw_received;
  assert (received_single_protected_message_decode
    receiver
    (M.TlsHandshake (M.CertificateVerify cv))
    raw_sent);
  let sent_tls_msg = M.TlsHandshake (M.Finished fin) in
  CSL.lemma_received_record_opened_from_sent_single_protected_message_seal_peer
    sender
    receiver
    sent_tls_msg
    raw_sent;
  eliminate exists (sent_outer:B.bytes).
    W.parse_record raw_sent == Some (T.ApplicationData, sent_outer, B.length raw_sent) /\
    received_record_opened
      receiver
      raw_sent
      sent_outer
      (sent_tls_inner_plaintext_fragment sent_tls_msg)
  returns
    False
  with _.
  ( eliminate exists
      (received_outer:B.bytes)
      (opened:B.bytes)
      (plaintext:M.plaintext).
      W.parse_record_wire raw_sent ==
        Some (T.ApplicationData, received_outer, B.length raw_sent) /\
      received_record_opened receiver raw_sent received_outer opened /\
      W.parse_plaintext opened == Some plaintext /\
      W.parse_tls_message plaintext.M.content_type plaintext.M.fragment ==
        Some (M.TlsHandshake (M.CertificateVerify cv))
    returns
      False
    with _.
    ( W.lemma_parse_record_implies_parse_record_wire raw_sent;
      assert (received_outer == sent_outer);
      eliminate exists (sent_read_state':R.direction_state).
        R.open_record
          receiver.model_record.record_read
          (record_header_aad raw_sent)
          sent_outer ==
          Some (sent_tls_inner_plaintext_fragment sent_tls_msg, sent_read_state')
      returns
        False
      with _.
      ( eliminate exists (received_read_state':R.direction_state).
          R.open_record
            receiver.model_record.record_read
            (record_header_aad raw_sent)
            received_outer ==
            Some (opened, received_read_state')
        returns
          False
        with _.
        ( assert (opened == sent_tls_inner_plaintext_fragment sent_tls_msg);
          W.lemma_serialize_tls_message_handshake (M.Finished fin);
          let sent_plaintext = {
            M.content_type = T.Handshake;
            M.fragment = W.serialize_handshake (M.Finished fin);
          } in
          assert (sent_tls_inner_plaintext_fragment sent_tls_msg ==
                  W.serialize_plaintext sent_plaintext);
          W.lemma_parse_plaintext_serialize_plaintext sent_plaintext;
          assert (W.parse_plaintext
            (sent_tls_inner_plaintext_fragment sent_tls_msg) ==
            Some sent_plaintext);
          assert (plaintext == sent_plaintext);
          assert (W.parse_tls_message
            T.Handshake
            (W.serialize_handshake (M.Finished fin)) ==
            Some (M.TlsHandshake (M.CertificateVerify cv)));
          WF.lemma_parse_finished_handshake fin;
          assert False ) ) ) )
#pop-options

#push-options "--split_queries always --z3rlimit 10"
let lemma_paired_protected_handshake_wire_equivalent_from_event_projection_pairs
  (client:connection_state)
  (server:connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  : Lemma
      (requires
        paired_protected_handshake_event_projection_pairs
          client
          server
          server_ee
          server_cert
          server_cv
          server_finished
          client_finished)
      (ensures WFL.paired_protected_handshake_wire_equivalent client server)
=
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_encrypted_extensions,
    server_hs.hs_encrypted_extensions,
    client_hs.hs_certificate,
    server_hs.hs_certificate,
    client_hs.hs_certificate_verify,
    server_hs.hs_certificate_verify,
    client_hs.hs_server_finished,
    server_hs.hs_server_finished,
    client_hs.hs_client_finished,
    server_hs.hs_client_finished
  with
  | Some client_ee, Some server_ee_msg,
    Some client_cert, Some server_cert_msg,
    Some client_cv, Some server_cv_msg,
    Some client_sf, Some server_sf,
    Some client_cf, Some server_cf ->
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      server_ee.pm_sender
      server_ee.pm_receiver
      (M.EncryptedExtensions server_ee_msg)
      (M.EncryptedExtensions client_ee)
      server_ee.pm_raw_sent
      server_ee.pm_raw_received;
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      server_cert.pm_sender
      server_cert.pm_receiver
      (M.Certificate server_cert_msg)
      (M.Certificate client_cert)
      server_cert.pm_raw_sent
      server_cert.pm_raw_received;
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      server_cv.pm_sender
      server_cv.pm_receiver
      (M.CertificateVerify server_cv_msg)
      (M.CertificateVerify client_cv)
      server_cv.pm_raw_sent
      server_cv.pm_raw_received;
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      server_finished.pm_sender
      server_finished.pm_receiver
      (M.Finished server_sf)
      (M.Finished client_sf)
      server_finished.pm_raw_sent
      server_finished.pm_raw_received;
    lemma_protected_handshake_wire_equal_from_event_projections_peer
      client_finished.pm_sender
      client_finished.pm_receiver
      (M.Finished client_cf)
      (M.Finished server_cf)
      client_finished.pm_raw_sent
      client_finished.pm_raw_received;
    assert (WFL.paired_protected_handshake_wire_equivalent client server)
  | _, _, _, _, _, _, _, _, _, _ ->
    assert False
#pop-options

let lemma_paired_protected_handshake_event_projection_pairs_intro
  (client:connection_state)
  (server:connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  : Lemma
      (requires
        (match
          client.cs_model.model_handshake.hs_encrypted_extensions,
          server.cs_model.model_handshake.hs_encrypted_extensions,
          client.cs_model.model_handshake.hs_certificate,
          server.cs_model.model_handshake.hs_certificate,
          client.cs_model.model_handshake.hs_certificate_verify,
          server.cs_model.model_handshake.hs_certificate_verify,
          client.cs_model.model_handshake.hs_server_finished,
          server.cs_model.model_handshake.hs_server_finished,
          client.cs_model.model_handshake.hs_client_finished,
          server.cs_model.model_handshake.hs_client_finished
        with
        | Some client_ee, Some server_ee_msg,
          Some client_cert, Some server_cert_msg,
          Some client_cv, Some server_cv_msg,
          Some client_sf, Some server_sf,
          Some client_cf, Some server_cf ->
          protected_handshake_event_projection_pair
            server_ee
            (M.EncryptedExtensions server_ee_msg)
            (M.EncryptedExtensions client_ee) /\
          protected_handshake_event_projection_pair
            server_cert
            (M.Certificate server_cert_msg)
            (M.Certificate client_cert) /\
          protected_handshake_event_projection_pair
            server_cv
            (M.CertificateVerify server_cv_msg)
            (M.CertificateVerify client_cv) /\
          protected_handshake_event_projection_pair
            server_finished
            (M.Finished server_sf)
            (M.Finished client_sf) /\
          protected_handshake_event_projection_pair
            client_finished
            (M.Finished client_cf)
            (M.Finished server_cf)
        | _, _, _, _, _, _, _, _, _, _ ->
          False))
      (ensures
        paired_protected_handshake_event_projection_pairs
          client
          server
          server_ee
          server_cert
          server_cv
          server_finished
          client_finished)
=
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_encrypted_extensions,
    server_hs.hs_encrypted_extensions,
    client_hs.hs_certificate,
    server_hs.hs_certificate,
    client_hs.hs_certificate_verify,
    server_hs.hs_certificate_verify,
    client_hs.hs_server_finished,
    server_hs.hs_server_finished,
    client_hs.hs_client_finished,
    server_hs.hs_client_finished
  with
  | Some _, Some _, Some _, Some _, Some _, Some _, Some _, Some _, Some _, Some _ ->
    ()
  | _, _, _, _, _, _, _, _, _, _ ->
    assert False

let lemma_paired_protected_handshake_event_projection_pairs_intro_from_messages
  (client:connection_state)
  (server:connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  : Lemma
      (requires
        (match
          client.cs_model.model_handshake.hs_encrypted_extensions,
          server.cs_model.model_handshake.hs_encrypted_extensions,
          client.cs_model.model_handshake.hs_certificate,
          server.cs_model.model_handshake.hs_certificate,
          client.cs_model.model_handshake.hs_certificate_verify,
          server.cs_model.model_handshake.hs_certificate_verify,
          client.cs_model.model_handshake.hs_server_finished,
          server.cs_model.model_handshake.hs_server_finished,
          client.cs_model.model_handshake.hs_client_finished,
          server.cs_model.model_handshake.hs_client_finished
        with
        | Some client_ee, Some server_ee_msg,
          Some client_cert, Some server_cert_msg,
          Some client_cv, Some server_cv_msg,
          Some client_sf, Some server_sf,
          Some client_cf, Some server_cf ->
          sent_msg0 == M.EncryptedExtensions server_ee_msg /\
          received_msg0 == M.EncryptedExtensions client_ee /\
          sent_msg1 == M.Certificate server_cert_msg /\
          received_msg1 == M.Certificate client_cert /\
          sent_msg2 == M.CertificateVerify server_cv_msg /\
          received_msg2 == M.CertificateVerify client_cv /\
          sent_msg3 == M.Finished server_sf /\
          received_msg3 == M.Finished client_sf /\
          sent_msg4 == M.Finished client_cf /\
          received_msg4 == M.Finished server_cf
        | _, _, _, _, _, _, _, _, _, _ ->
          False) /\
        protected_handshake_event_projection_pair
          server_ee
          sent_msg0
          received_msg0 /\
        protected_handshake_event_projection_pair
          server_cert
          sent_msg1
          received_msg1 /\
        protected_handshake_event_projection_pair
          server_cv
          sent_msg2
          received_msg2 /\
        protected_handshake_event_projection_pair
          server_finished
          sent_msg3
          received_msg3 /\
        protected_handshake_event_projection_pair
          client_finished
          sent_msg4
          received_msg4)
      (ensures
        paired_protected_handshake_event_projection_pairs
          client
          server
          server_ee
          server_cert
          server_cv
          server_finished
          client_finished)
=
  let client_hs = client.cs_model.model_handshake in
  let server_hs = server.cs_model.model_handshake in
  match
    client_hs.hs_encrypted_extensions,
    server_hs.hs_encrypted_extensions,
    client_hs.hs_certificate,
    server_hs.hs_certificate,
    client_hs.hs_certificate_verify,
    server_hs.hs_certificate_verify,
    client_hs.hs_server_finished,
    server_hs.hs_server_finished,
    client_hs.hs_client_finished,
    server_hs.hs_client_finished
  with
  | Some client_ee, Some server_ee_msg,
    Some client_cert, Some server_cert_msg,
    Some client_cv, Some server_cv_msg,
    Some client_sf, Some server_sf,
    Some client_cf, Some server_cf ->
    assert (sent_msg0 == M.EncryptedExtensions server_ee_msg);
    assert (received_msg0 == M.EncryptedExtensions client_ee);
    assert (sent_msg1 == M.Certificate server_cert_msg);
    assert (received_msg1 == M.Certificate client_cert);
    assert (sent_msg2 == M.CertificateVerify server_cv_msg);
    assert (received_msg2 == M.CertificateVerify client_cv);
    assert (sent_msg3 == M.Finished server_sf);
    assert (received_msg3 == M.Finished client_sf);
    assert (sent_msg4 == M.Finished client_cf);
    assert (received_msg4 == M.Finished server_cf);
    lemma_paired_protected_handshake_event_projection_pairs_intro
      client
      server
      server_ee
      server_cert
      server_cv
      server_finished
      client_finished
  | _, _, _, _, _, _, _, _, _, _ ->
    assert False

let lemma_paired_protected_handshake_event_projection_pair_witnesses_intro_from_messages
  (client:connection_state)
  (server:connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  : Lemma
      (requires
        (match
          client.cs_model.model_handshake.hs_encrypted_extensions,
          server.cs_model.model_handshake.hs_encrypted_extensions,
          client.cs_model.model_handshake.hs_certificate,
          server.cs_model.model_handshake.hs_certificate,
          client.cs_model.model_handshake.hs_certificate_verify,
          server.cs_model.model_handshake.hs_certificate_verify,
          client.cs_model.model_handshake.hs_server_finished,
          server.cs_model.model_handshake.hs_server_finished,
          client.cs_model.model_handshake.hs_client_finished,
          server.cs_model.model_handshake.hs_client_finished
        with
        | Some client_ee, Some server_ee_msg,
          Some client_cert, Some server_cert_msg,
          Some client_cv, Some server_cv_msg,
          Some client_sf, Some server_sf,
          Some client_cf, Some server_cf ->
          sent_msg0 == M.EncryptedExtensions server_ee_msg /\
          received_msg0 == M.EncryptedExtensions client_ee /\
          sent_msg1 == M.Certificate server_cert_msg /\
          received_msg1 == M.Certificate client_cert /\
          sent_msg2 == M.CertificateVerify server_cv_msg /\
          received_msg2 == M.CertificateVerify client_cv /\
          sent_msg3 == M.Finished server_sf /\
          received_msg3 == M.Finished client_sf /\
          sent_msg4 == M.Finished client_cf /\
          received_msg4 == M.Finished server_cf
        | _, _, _, _, _, _, _, _, _, _ ->
          False) /\
        protected_handshake_event_projection_pair
          server_ee
          sent_msg0
          received_msg0 /\
        protected_handshake_event_projection_pair
          server_cert
          sent_msg1
          received_msg1 /\
        protected_handshake_event_projection_pair
          server_cv
          sent_msg2
          received_msg2 /\
        protected_handshake_event_projection_pair
          server_finished
          sent_msg3
          received_msg3 /\
        protected_handshake_event_projection_pair
          client_finished
          sent_msg4
          received_msg4)
      (ensures
        exists server_ee' server_cert' server_cv' server_finished' client_finished'.
          paired_protected_handshake_event_projection_pairs
            client
            server
            server_ee'
            server_cert'
            server_cv'
            server_finished'
            client_finished')
=
  lemma_paired_protected_handshake_event_projection_pairs_intro_from_messages
    client
    server
    server_ee
    server_cert
    server_cv
    server_finished
    client_finished
    sent_msg0
    received_msg0
    sent_msg1
    received_msg1
    sent_msg2
    received_msg2
    sent_msg3
    received_msg3
    sent_msg4
    received_msg4;
  introduce exists
    (server_ee':protected_message_replay)
    (server_cert':protected_message_replay)
    (server_cv':protected_message_replay)
    (server_finished':protected_message_replay)
    (client_finished':protected_message_replay).
    paired_protected_handshake_event_projection_pairs
      client
      server
      server_ee'
      server_cert'
      server_cv'
      server_finished'
      client_finished'
  with server_ee server_cert server_cv server_finished client_finished
  and ()

let lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_pair_outputs
  (client:connection_state)
  (server:connection_state)
  (sent_msg0:M.handshake_msg)
  (received_msg0:M.handshake_msg)
  (sent_msg1:M.handshake_msg)
  (received_msg1:M.handshake_msg)
  (sent_msg2:M.handshake_msg)
  (received_msg2:M.handshake_msg)
  (sent_msg3:M.handshake_msg)
  (received_msg3:M.handshake_msg)
  (sent_msg4:M.handshake_msg)
  (received_msg4:M.handshake_msg)
  : Lemma
      (requires
        (match
          client.cs_model.model_handshake.hs_encrypted_extensions,
          server.cs_model.model_handshake.hs_encrypted_extensions,
          client.cs_model.model_handshake.hs_certificate,
          server.cs_model.model_handshake.hs_certificate,
          client.cs_model.model_handshake.hs_certificate_verify,
          server.cs_model.model_handshake.hs_certificate_verify,
          client.cs_model.model_handshake.hs_server_finished,
          server.cs_model.model_handshake.hs_server_finished,
          client.cs_model.model_handshake.hs_client_finished,
          server.cs_model.model_handshake.hs_client_finished
        with
        | Some client_ee, Some server_ee_msg,
          Some client_cert, Some server_cert_msg,
          Some client_cv, Some server_cv_msg,
          Some client_sf, Some server_sf,
          Some client_cf, Some server_cf ->
          sent_msg0 == M.EncryptedExtensions server_ee_msg /\
          received_msg0 == M.EncryptedExtensions client_ee /\
          sent_msg1 == M.Certificate server_cert_msg /\
          received_msg1 == M.Certificate client_cert /\
          sent_msg2 == M.CertificateVerify server_cv_msg /\
          received_msg2 == M.CertificateVerify client_cv /\
          sent_msg3 == M.Finished server_sf /\
          received_msg3 == M.Finished client_sf /\
          sent_msg4 == M.Finished client_cf /\
          received_msg4 == M.Finished server_cf
        | _, _, _, _, _, _, _, _, _, _ ->
          False) /\
        (exists server_ee server_cert server_cv server_finished.
          protected_handshake_event_projection_pair
            server_ee
            sent_msg0
            received_msg0 /\
          protected_handshake_event_projection_pair
            server_cert
            sent_msg1
            received_msg1 /\
          protected_handshake_event_projection_pair
            server_cv
            sent_msg2
            received_msg2 /\
          protected_handshake_event_projection_pair
            server_finished
            sent_msg3
            received_msg3) /\
        (exists client_finished.
          protected_handshake_event_projection_pair
            client_finished
            sent_msg4
            received_msg4))
      (ensures
        exists server_ee server_cert server_cv server_finished client_finished.
          paired_protected_handshake_event_projection_pairs
            client
            server
            server_ee
            server_cert
            server_cv
            server_finished
            client_finished)
=
  eliminate exists
    (server_ee:protected_message_replay)
    (server_cert:protected_message_replay)
    (server_cv:protected_message_replay)
    (server_finished:protected_message_replay).
    protected_handshake_event_projection_pair
      server_ee
      sent_msg0
      received_msg0 /\
    protected_handshake_event_projection_pair
      server_cert
      sent_msg1
      received_msg1 /\
    protected_handshake_event_projection_pair
      server_cv
      sent_msg2
      received_msg2 /\
    protected_handshake_event_projection_pair
      server_finished
      sent_msg3
      received_msg3
  returns
    exists server_ee' server_cert' server_cv' server_finished' client_finished'.
      paired_protected_handshake_event_projection_pairs
        client
        server
        server_ee'
        server_cert'
        server_cv'
        server_finished'
        client_finished'
  with _.
  ( eliminate exists (client_finished:protected_message_replay).
      protected_handshake_event_projection_pair
        client_finished
        sent_msg4
        received_msg4
    returns
      exists server_ee' server_cert' server_cv' server_finished' client_finished'.
        paired_protected_handshake_event_projection_pairs
          client
          server
          server_ee'
          server_cert'
          server_cv'
          server_finished'
          client_finished'
    with _.
    ( lemma_paired_protected_handshake_event_projection_pair_witnesses_intro_from_messages
        client
        server
        server_ee
        server_cert
        server_cv
        server_finished
        client_finished
        sent_msg0
        received_msg0
        sent_msg1
        received_msg1
        sent_msg2
        received_msg2
        sent_msg3
        received_msg3
        sent_msg4
        received_msg4 ) )
