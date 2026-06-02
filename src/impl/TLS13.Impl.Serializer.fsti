module TLS13.Impl.Serializer

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

(**
  Serializer interface at the M/L boundary.

  Each serializer takes an owned L value already related to a pure M value and
  an output byte buffer.  Failure is reported as None.  On success, the returned
  length identifies the emitted output prefix, that prefix is the corresponding
  TLS13.Wire.Spec serialization, and the prefix parses back to the same M value.
**)

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
