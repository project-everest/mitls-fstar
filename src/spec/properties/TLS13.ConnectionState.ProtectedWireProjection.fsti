module TLS13.ConnectionState.ProtectedWireProjection

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module GFin = TLS13.Wire.Generated.Finished
module GCV = TLS13.Wire.Generated.CertificateVerify
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.ConnectionState.ProtectedWireBase

val lemma_protected_handshake_wire_equal_from_sent_seal_peer
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        TLS13.Spec.StateMachine.Canonical.sent_single_protected_message_seal
          sender
          (M.TlsHandshake sent_msg)
          raw /\
        TLS13.Spec.StateMachine.Canonical.received_single_protected_message_decode
          receiver
          (M.TlsHandshake received_msg)
          raw /\
        protected_handshake_wire_round_trip_message received_msg)
      (ensures
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg))

val lemma_protected_handshake_wire_equal_from_event_projections_peer
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (received_msg:M.handshake_msg)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal raw_sent raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          raw_sent /\
        TLS13.Spec.StateMachine.Canonical.received_event_decode_projection
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake received_msg;
          })
          raw_received)
      (ensures
        Seq.equal
          (W.serialize_handshake sent_msg)
          (W.serialize_handshake received_msg))

val lemma_single_protected_message_seal_excludes_protected_head
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (sent_msg:M.handshake_msg)
  (step:CS.protected_handshake_step)
  (raw:B.bytes)
  : Lemma
      (requires
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        protected_handshake_wire_round_trip_message sent_msg /\
        TLS13.Spec.StateMachine.Canonical.sent_single_protected_message_seal
          sender
          (M.TlsHandshake sent_msg)
          raw /\
        step.CS.protected_handshake_head /\
        CS.legal_event receiver (CS.ConnProtectedHandshake step) /\
        TLS13.Spec.StateMachine.Canonical.received_event_decode_projection
          receiver
          (CS.ConnProtectedHandshake step)
          raw)
      (ensures False)

val lemma_protected_finished_not_certificate_verify_from_event_projections_peer
  (sender:CS.connection_model)
  (receiver:CS.connection_model)
  (fin:GFin.finished)
  (cv:GCV.certificateVerify)
  (raw_sent:B.bytes)
  (raw_received:B.bytes)
  : Lemma
      (requires
        sender.CS.model_record.CS.record_write.R.seq ==
          receiver.CS.model_record.CS.record_read.R.seq /\
        (match
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material sender.CS.model_record.CS.record_write,
          TLS13.Spec.StateMachine.KeyMaterial.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          TLS13.Spec.StateMachine.KeyMaterial.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal raw_sent raw_received /\
        TLS13.Spec.StateMachine.Canonical.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.Finished fin);
          })
          raw_sent /\
        TLS13.Spec.StateMachine.Canonical.received_event_decode_projection
          receiver
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Received;
            CL.message_value = M.TlsHandshake (M.CertificateVerify cv);
          })
          raw_received)
      (ensures False)


val lemma_paired_protected_handshake_wire_equivalent_from_event_projection_pairs
  (client:CS.connection_state)
  (server:CS.connection_state)
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

val lemma_paired_protected_handshake_event_projection_pairs_intro
  (client:CS.connection_state)
  (server:CS.connection_state)
  (server_ee:protected_message_replay)
  (server_cert:protected_message_replay)
  (server_cv:protected_message_replay)
  (server_finished:protected_message_replay)
  (client_finished:protected_message_replay)
  : Lemma
      (requires
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

val lemma_paired_protected_handshake_event_projection_pairs_intro_from_messages
  (client:CS.connection_state)
  (server:CS.connection_state)
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

val lemma_paired_protected_handshake_event_projection_pair_witnesses_intro_from_messages
  (client:CS.connection_state)
  (server:CS.connection_state)
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

val lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_pair_outputs
  (client:CS.connection_state)
  (server:CS.connection_state)
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
