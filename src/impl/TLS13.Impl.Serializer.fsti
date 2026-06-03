module TLS13.Impl.Serializer

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

(**
  Serializer interface at the M/L boundary.

  The first group is a buffer-oriented streaming facade used by the active
  implementation, including a few message-builder helpers that assemble fixed
  protocol inputs.  These signatures preserve the existing driver shape while
  routing the serializer TCB through this module.

  The second group is the L serializer surface.  Each serializer takes an owned
  L value already related to a pure M value and an output byte buffer.  Failure
  is reported as None.  On success, the returned length identifies the emitted
  output prefix, that prefix is the corresponding TLS13.Wire.Spec
  serialization, and the prefix parses back to the same M value.
**)

fn build_server_certificate_verify_input
  (transcript_hash: array U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to transcript_hash 'hash_bytes **
           pts_to out 'old_bytes **
           pure (B.length 'hash_bytes == 32 /\
                 B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 130)
  ensures exists* out_bytes.
          pts_to transcript_hash 'hash_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 130 /\
                B.length 'hash_bytes == 32 /\
                Seq.equal
                  (Ghost.reveal out_bytes)
                  (WS.serialize_server_certificate_verify_input (Ghost.reveal 'hash_bytes)))

fn serialize_client_hello_record_header
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to out 'old_bytes **
          pure (B.length 'old_bytes == SZ.v out_len /\
                SZ.v out_len == 5)
  ensures exists* out_bytes.
          pts_to out out_bytes **
          pure (B.length out_bytes == 5)

fn build_supported_client_hello_localhost
  (random: array U8.t)
  (key_share: array U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to random 'random_bytes **
          pts_to key_share 'key_share_bytes **
          pts_to out 'old_bytes **
          pure (B.length 'random_bytes == 32 /\
                B.length 'key_share_bytes == 32 /\
                B.length 'old_bytes == SZ.v out_len)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to random 'random_bytes **
          pts_to key_share 'key_share_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
               (ok ==> SZ.v out_len >= 130))

fn encode_inner_plaintext_no_padding_slice
  (plain: array U8.t)
  (plain_total_len: SZ.t)
  (plain_offset: SZ.t)
  (plain_len: SZ.t)
  (content_type: U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to plain 'plain_bytes **
           pts_to out 'old_bytes **
           pure (B.length 'plain_bytes == SZ.v plain_total_len /\
                 B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == SZ.v plain_len + 1 /\
                 SZ.v plain_offset + SZ.v plain_len <= SZ.v plain_total_len)
  ensures exists* out_bytes.
          pts_to plain 'plain_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len)

fn serialize_application_data_header
  (fragment_len: U16.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to out 'old_bytes **
           pure (B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 5)
  ensures exists* header_bytes.
          pts_to out header_bytes **
          pure (B.length header_bytes == 5)

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
                Seq.equal raw_prefix (WS.serialize_record T.ApplicationData (Ghost.reveal 'fragment_bytes)) /\
                CS.raw_records_exactly raw_prefix T.ApplicationData 1))

fn serialize_client_finished_application_data_record
  (#fin: M.finished)
  (lfin: L.finished)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_finished lfin fin **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                58 <= SZ.v out_len)
  returns written: (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_finished lfin fin **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v written == 58 /\
                (let raw_prefix = Seq.slice out_bytes 0 (SZ.v written) in
                CS.raw_records_exactly raw_prefix T.ApplicationData 1))

fn serialize_client_finished_outputs
  (lfin: L.finished)
  (handshake_out: array U8.t)
  (network_out: array U8.t)
  (network_out_len: SZ.t)
  requires (exists* fin. L.is_valid_finished lfin fin) **
           pts_to handshake_out 'old_handshake **
           pts_to network_out 'old_network **
           pure (B.length 'old_handshake == 36 /\
                B.length 'old_network == SZ.v network_out_len /\
                58 <= SZ.v network_out_len)
  returns written: (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures exists* fin handshake_bytes network_bytes.
          L.is_valid_finished lfin fin **
          pts_to handshake_out handshake_bytes **
          pts_to network_out network_bytes **
          pure (B.length handshake_bytes == 36 /\
                Seq.equal handshake_bytes (WS.serialize_handshake (M.Finished fin)) /\
                B.length network_bytes == SZ.v network_out_len /\
                SZ.v written == 58 /\
                (let raw_prefix = Seq.slice network_bytes 0 (SZ.v written) in
                CS.raw_records_exactly raw_prefix T.ApplicationData 1))

fn serialize_client_hello
  (#m: M.client_hello)
  (l: L.client_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_client_hello l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_client_hello l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_client_hello m) /\
                   WS.parse_client_hello prefix == Some m
                 | None -> True))

fn serialize_server_hello
  (#m: M.server_hello)
  (l: L.server_hello)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_server_hello l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_server_hello l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_server_hello m) /\
                   WS.parse_server_hello prefix == Some m
                 | None -> True))

fn serialize_encrypted_extensions
  (#m: M.encrypted_extensions)
  (l: L.encrypted_extensions)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_encrypted_extensions l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_encrypted_extensions l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_encrypted_extensions m) /\
                   WS.parse_encrypted_extensions prefix == Some m
                 | None -> True))

fn serialize_certificate_msg
  (#m: M.certificate_msg)
  (l: L.certificate_msg)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_certificate_msg l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_msg l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_certificate_msg m) /\
                   WS.parse_certificate_msg prefix == Some m
                 | None -> True))

fn serialize_certificate_verify
  (#m: M.certificate_verify)
  (l: L.certificate_verify)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_certificate_verify l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_certificate_verify l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_certificate_verify m) /\
                   WS.parse_certificate_verify prefix == Some m
                 | None -> True))

fn serialize_finished
  (#m: M.finished)
  (l: L.finished)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_finished l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_finished l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_finished m) /\
                   WS.parse_finished prefix == Some m
                 | None -> True))

fn serialize_handshake_msg
  (#m: M.handshake_msg)
  (l: L.handshake_msg)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_handshake_msg l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_handshake_msg l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (B.length (WS.serialize_handshake_msg m) <= SZ.v out_len ==>
                 Some? written) /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_handshake_msg m) /\
                   (match WS.parse_handshake_msg prefix with
                    | Some (m', consumed) -> m' == m /\ consumed == SZ.v n
                    | None -> False)
                 | None -> True))

fn serialize_plaintext
  (#m: M.plaintext)
  (l: L.plaintext)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_plaintext l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_plaintext l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_plaintext m) /\
                   WS.parse_plaintext prefix == Some m
                 | None -> True))

fn serialize_sealed_record
  (#m: M.sealed_record)
  (l: L.sealed_record)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_sealed_record l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_sealed_record l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_sealed_record m) /\
                   WS.parse_sealed_record prefix == Some m
                 | None -> True))

fn serialize_application_data
  (#m: B.bytes)
  (l: L.application_data)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_application_data l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_application_data l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   let (ct, wire) = WS.serialize_tls_message (M.TlsApplicationData m) in
                   ct == T.ApplicationData /\
                   Seq.equal prefix wire /\
                   WS.parse_tls_message T.ApplicationData prefix == Some (M.TlsApplicationData m)
                 | None -> True))

fn serialize_tls_message
  (#m: M.tls_message)
  (l: L.tls_message)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_tls_message l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (U8.t & (n:SZ.t{SZ.v n <= SZ.v out_len}))
  ensures exists* out_bytes.
          L.is_valid_tls_message l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some (content_type, n) ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   let (ct, wire) = WS.serialize_tls_message m in
                   L.content_type_matches content_type ct /\
                   Seq.equal prefix wire /\
                   WS.parse_tls_message ct prefix == Some m
                 | None -> True))

fn serialize_tls_record
  (#m: M.tls_record)
  (l: L.tls_record)
  (out: array U8.t)
  (out_len: SZ.t)
  requires L.is_valid_tls_record l m **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len)
  returns written: option (n:SZ.t{SZ.v n <= SZ.v out_len})
  ensures exists* out_bytes.
          L.is_valid_tls_record l m **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (match written with
                 | Some n ->
                   let prefix = Seq.slice out_bytes 0 (SZ.v n) in
                   Seq.equal prefix (WS.serialize_tls_record m) /\
                   (match WS.parse_tls_record prefix with
                    | Some (m', consumed) -> m' == m /\ consumed == SZ.v n
                    | None -> False)
                 | None -> True))
