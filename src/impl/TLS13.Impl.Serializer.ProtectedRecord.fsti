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

fn serialize_application_data_header
  (fragment_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to out 'old_bytes **
           pure (B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 5 /\
                 SZ.v fragment_len <= 16640)
  ensures exists* header_bytes.
          pts_to out header_bytes **
          pure (B.length header_bytes == 5 /\
                Seq.equal
                  (Ghost.reveal header_bytes)
                  (TLS13.Spec.StateMachine.Canonical.application_data_record_header
                    (SZ.v fragment_len)) /\
                WS.parse_record_header (Ghost.reveal header_bytes) ==
                  Some (T.Application_data, SZ.v fragment_len))

fn serialize_raw_record
  (content_type: T.content_type)
  (fragment: array U8.t)
  (fragment_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to fragment 'fragment_bytes **
          pts_to out 'old_out **
          pure (B.length 'old_out == SZ.v out_len /\
                B.length 'fragment_bytes == SZ.v fragment_len /\
                SZ.v fragment_len <= 16640 /\
                SZ.v fragment_len + 5 <= SZ.v out_len)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          pts_to fragment 'fragment_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v fragment_len + 5 /\
               (let raw_prefix =
                  Seq.slice out_bytes 0 (SZ.v written) in
                Seq.equal raw_prefix
                  (WS.serialize_record content_type (Ghost.reveal 'fragment_bytes)) /\
                WS.parse_record raw_prefix ==
                  Some
                    (content_type,
                     (Ghost.reveal 'fragment_bytes),
                     SZ.v written) /\
                CS.raw_records_exactly raw_prefix content_type 1))

fn serialize_raw_application_data_record
  (fragment: array U8.t)
  (fragment_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to fragment 'fragment_bytes **
          pts_to out 'old_out **
          pure (B.length 'old_out == SZ.v out_len /\
                B.length 'fragment_bytes == SZ.v fragment_len /\
                SZ.v fragment_len <= 16640 /\
                SZ.v fragment_len + 5 <= SZ.v out_len)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          pts_to fragment 'fragment_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               SZ.v written == SZ.v fragment_len + 5 /\
               (let raw_prefix =
                  Seq.slice out_bytes 0 (SZ.v written) in
                Seq.equal raw_prefix
                  (WS.serialize_record
                    T.Application_data (Ghost.reveal 'fragment_bytes)) /\
                Seq.equal
                  (TLS13.Spec.StateMachine.Canonical.record_header_aad raw_prefix)
                  (TLS13.Spec.StateMachine.Canonical.application_data_record_header
                    (SZ.v fragment_len)) /\
                WS.parse_record raw_prefix ==
                  Some
                    (T.Application_data,
                     (Ghost.reveal 'fragment_bytes),
                     SZ.v written) /\
                CS.raw_records_exactly raw_prefix T.Application_data 1))

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
