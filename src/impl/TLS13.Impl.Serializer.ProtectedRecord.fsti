module TLS13.Impl.Serializer.ProtectedRecord

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Rec = TLS13.Record
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

fn serialize_protected_handshake_record
  (#msg: erased M.handshake_msg)
  (write_state: Rec.record_state)
  (handshake: array U8.t)
  (handshake_len: SZ.t)
  (network_out: array U8.t)
  (network_out_len: SZ.t)
  (#record_write: erased R.direction_state)
  (#handshake_bytes: erased B.bytes)
  (#old_network: erased B.bytes)
  requires Rec.is_record_state write_state (Ghost.reveal record_write) **
           pts_to handshake (Ghost.reveal handshake_bytes) **
           pts_to network_out (Ghost.reveal old_network) **
           pure (B.length (Ghost.reveal handshake_bytes) == SZ.v handshake_len /\
                 Seq.equal
                   (Ghost.reveal handshake_bytes)
                   (WS.serialize_handshake (Ghost.reveal msg)) /\
                 B.length (Ghost.reveal old_network) == SZ.v network_out_len /\
                 SZ.v handshake_len + 17 <= 16640 /\
                 SZ.v handshake_len + 22 <= SZ.v network_out_len /\
                 Some? (R.seal
                   (Ghost.reveal record_write)
                   (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v handshake_len + 17))
                   {
                     R.content_type = T.Application_data;
                     R.fragment =
                       TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
                         (M.TlsHandshake (Ghost.reveal msg));
                   }))
  returns written: (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures exists* network_bytes.
          Rec.is_record_state write_state (Ghost.reveal record_write) **
          pts_to handshake (Ghost.reveal handshake_bytes) **
          pts_to network_out network_bytes **
          pure (B.length network_bytes == SZ.v network_out_len /\
                SZ.v written == SZ.v handshake_len + 22 /\
                (let raw_prefix = Seq.slice network_bytes 0 (SZ.v written) in
                CS.raw_records_exactly raw_prefix T.Application_data 1 /\
                (exists outer_fragment.
                   WS.parse_record raw_prefix ==
                     Some (T.Application_data, outer_fragment, B.length raw_prefix) /\
                   Seq.equal raw_prefix (WS.serialize_record T.Application_data outer_fragment) /\
                   Seq.equal
                     (TLS13.Spec.StateMachine.Canonical.record_header_aad raw_prefix)
                     (TLS13.Spec.StateMachine.Canonical.application_data_record_header (SZ.v handshake_len + 17)) /\
                   R.seal
                     (Ghost.reveal record_write)
                     (TLS13.Spec.StateMachine.Canonical.record_header_aad raw_prefix)
                     {
                       R.content_type = T.Application_data;
                       R.fragment =
                         TLS13.Spec.StateMachine.Canonical.sent_tls_inner_plaintext_fragment
                           (M.TlsHandshake (Ghost.reveal msg));
                     } ==
                     Some (outer_fragment, R.next_seq (Ghost.reveal record_write)))))
