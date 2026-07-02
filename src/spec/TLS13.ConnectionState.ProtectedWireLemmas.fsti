module TLS13.ConnectionState.ProtectedWireLemmas

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module W = TLS13.Wire.Spec

noextract
let protected_handshake_wire_round_trip_message (msg:M.handshake_msg) : prop =
  match msg with
  | M.EncryptedExtensions _
  | M.Certificate _
  | M.CertificateVerify _
  | M.Finished _ -> True
  | _ -> False

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
          CS.record_direction_material sender.CS.model_record.CS.record_write,
          CS.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        CS.sent_single_protected_message_seal
          sender
          (M.TlsHandshake sent_msg)
          raw /\
        CS.received_single_protected_message_decode
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
          CS.record_direction_material sender.CS.model_record.CS.record_write,
          CS.record_direction_material receiver.CS.model_record.CS.record_read
        with
        | Some sender_write, Some receiver_read ->
          CS.record_key_iv_material_agrees sender_write receiver_read
        | _, _ ->
          False) /\
        Seq.equal raw_sent raw_received /\
        protected_handshake_wire_round_trip_message sent_msg /\
        protected_handshake_wire_round_trip_message received_msg /\
        CS.sent_event_seal_projection
          sender
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake sent_msg;
          })
          raw_sent /\
        CS.received_event_decode_projection
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
