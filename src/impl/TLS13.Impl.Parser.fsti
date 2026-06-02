module TLS13.Impl.Parser

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

(**
  Parser interface at the M/L boundary.

  The first group is a buffer-oriented streaming facade used by the active
  implementation.  These signatures preserve the existing header-first driver
  shape while routing the parser TCB through this module.

  The second group is the allocating L parser surface.  Each parser consumes an
  owned input byte array without modifying it.  On success, it returns an
  extraction-oriented L value together with ownership evidence, and relates that
  L value to the pure M message produced by the corresponding TLS13.Wire.Spec
  parser.
**)

fn parse_supported_server_hello
  (input: array U8.t)
  (input_len: SZ.t)
  (random_out: array U8.t)
  (random_out_len: SZ.t)
  (key_share_out: array U8.t)
  (key_share_out_len: SZ.t)
  requires pts_to input 'input_bytes **
           pts_to random_out 'old_random **
           pts_to key_share_out 'old_key_share **
           pure (B.length 'input_bytes == SZ.v input_len /\
                B.length 'old_random == SZ.v random_out_len /\
                B.length 'old_key_share == SZ.v key_share_out_len /\
                SZ.v random_out_len == 32 /\
                SZ.v key_share_out_len == 32)
  returns ok: bool
  ensures exists* random_bytes key_share_bytes.
          pts_to input 'input_bytes **
          pts_to random_out random_bytes **
          pts_to key_share_out key_share_bytes **
          pure (
            B.length random_bytes == 32 /\
            B.length key_share_bytes == 32 /\
            (ok ==> SZ.v input_len == 90) /\
            (ok <==> Some? (WS.parse_supported_server_hello 'input_bytes)) /\
            (ok ==> (
              let Some sh = WS.parse_supported_server_hello 'input_bytes in
              Seq.equal random_bytes sh.random /\
              Seq.equal key_share_bytes sh.key_share
            ))
          )

fn decode_inner_plaintext_no_padding
  (inner: array U8.t)
  (inner_len: SZ.t)
  (content_type_out: array U8.t)
  (content_type_out_len: SZ.t)
  requires pts_to inner 'inner_bytes **
           pts_to content_type_out 'old_content_type **
           pure (B.length 'inner_bytes == SZ.v inner_len /\
                 B.length 'old_content_type == SZ.v content_type_out_len /\
                 SZ.v inner_len > 0 /\
                 SZ.v content_type_out_len == 1)
  returns payload_len: (p:SZ.t{SZ.v p + 1 == SZ.v inner_len})
  ensures exists* content_type_bytes.
          pts_to inner 'inner_bytes **
          pts_to content_type_out content_type_bytes **
          pure (B.length content_type_bytes == 1)

fn decode_inner_plaintext
  (inner: array U8.t)
  (inner_len: SZ.t)
  (content_type_out: array U8.t)
  (content_type_out_len: SZ.t)
  requires pts_to inner 'inner_bytes **
          pts_to content_type_out 'old_content_type **
          pure (B.length 'inner_bytes == SZ.v inner_len /\
                B.length 'old_content_type == SZ.v content_type_out_len /\
                SZ.v inner_len > 0 /\
                SZ.v content_type_out_len == 1)
  returns payload_len: SZ.t
  ensures exists* content_type_bytes.
          pts_to inner 'inner_bytes **
          pts_to content_type_out content_type_bytes **
          pure (B.length content_type_bytes == 1 /\
               SZ.v payload_len < SZ.v inner_len)

fn parse_record_header
  (header: array U8.t)
  (header_len: SZ.t)
  (content_type_out: array U8.t)
  (content_type_out_len: SZ.t)
  (fragment_len_out: array U8.t)
  (fragment_len_out_len: SZ.t)
  requires pts_to header 'header_bytes **
           pts_to content_type_out 'old_content_type **
           pts_to fragment_len_out 'old_fragment_len **
           pure (B.length 'header_bytes == SZ.v header_len /\
                 B.length 'old_content_type == SZ.v content_type_out_len /\
                 B.length 'old_fragment_len == SZ.v fragment_len_out_len /\
                 SZ.v header_len == 5 /\
                 SZ.v content_type_out_len == 1 /\
                 SZ.v fragment_len_out_len == 2)
  returns ok: bool
  ensures exists* content_type_bytes fragment_len_bytes.
          pts_to header 'header_bytes **
          pts_to content_type_out content_type_bytes **
          pts_to fragment_len_out fragment_len_bytes **
          pure (
            B.length 'header_bytes == 5 /\
            B.length content_type_bytes == 1 /\
            B.length fragment_len_bytes == 2 /\
            Seq.index content_type_bytes 0 == Seq.index 'header_bytes 0 /\
            WS.read_u16 fragment_len_bytes 0 == WS.read_u16 'header_bytes 3 /\
            (ok <==> Some? (WS.parse_record_header 'header_bytes))
          )

fn parse_client_hello
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.client_hello
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             exists* m.
               L.is_valid_client_hello l m **
               pure (WS.parse_client_hello 'input_bytes == Some m)
           | None ->
             pure (WS.parse_client_hello 'input_bytes == None))

fn parse_server_hello
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.server_hello
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             exists* m.
               L.is_valid_server_hello l m **
               pure (WS.parse_server_hello 'input_bytes == Some m)
           | None ->
             pure (WS.parse_server_hello 'input_bytes == None))

fn parse_encrypted_extensions
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.encrypted_extensions
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             exists* m.
               L.is_valid_encrypted_extensions l m **
               pure (WS.parse_encrypted_extensions 'input_bytes == Some m)
           | None ->
             pure (WS.parse_encrypted_extensions 'input_bytes == None))

fn parse_certificate_msg
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.certificate_msg
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             exists* m.
               L.is_valid_certificate_msg l m **
               pure (WS.parse_certificate_msg 'input_bytes == Some m)
           | None ->
             pure (WS.parse_certificate_msg 'input_bytes == None))

fn parse_certificate_verify
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.certificate_verify
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             exists* m.
               L.is_valid_certificate_verify l m **
               pure (WS.parse_certificate_verify 'input_bytes == Some m)
           | None ->
             pure (WS.parse_certificate_verify 'input_bytes == None))

fn parse_finished
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.finished
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             exists* m.
               L.is_valid_finished l m **
               pure (WS.parse_finished 'input_bytes == Some m)
           | None ->
             pure (WS.parse_finished 'input_bytes == None))

fn parse_handshake_msg
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option (L.handshake_msg & (n:SZ.t{SZ.v n <= SZ.v input_len}))
  ensures pts_to input 'input_bytes **
          (match r with
           | Some (l, consumed) ->
             exists* m.
               L.is_valid_handshake_msg l m **
               pure (
                 match WS.parse_handshake_msg 'input_bytes with
                 | Some (m', n) -> m' == m /\ n == SZ.v consumed
                 | None -> False)
           | None ->
             pure (WS.parse_handshake_msg 'input_bytes == None))

fn parse_plaintext
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.plaintext
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             exists* m.
               L.is_valid_plaintext l m **
               pure (WS.parse_plaintext 'input_bytes == Some m)
           | None ->
             pure (WS.parse_plaintext 'input_bytes == None))

fn parse_sealed_record
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.sealed_record
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             exists* m.
               L.is_valid_sealed_record l m **
               pure (WS.parse_sealed_record 'input_bytes == Some m)
           | None ->
             pure (WS.parse_sealed_record 'input_bytes == None))

fn parse_application_data
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.application_data
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             exists* m.
               L.is_valid_application_data l m **
               pure (WS.parse_tls_message T.ApplicationData 'input_bytes == Some (M.TlsApplicationData m))
           | None ->
             pure (WS.parse_tls_message T.ApplicationData 'input_bytes == None))

fn parse_tls_message
  (content_type: U8.t)
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option L.tls_message
  ensures pts_to input 'input_bytes **
          (match r with
           | Some l ->
             (exists* ct m.
               L.is_valid_tls_message l m **
               pure (L.content_type_matches content_type ct /\
                     WS.parse_tls_message ct 'input_bytes == Some m)) **
             pure (exists ct m.
               L.content_type_matches content_type ct /\
               WS.parse_tls_message ct 'input_bytes == Some m) **
             pure (CT.parsed_message_wire_success
               content_type
               (Ghost.reveal 'input_bytes)
               l)
           | None ->
             pure (forall (ct:T.content_type).
               L.content_type_matches content_type ct ==>
               WS.parse_tls_message ct 'input_bytes == None))

fn parse_tls_record
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns r: option (L.tls_record & (n:SZ.t{SZ.v n <= SZ.v input_len}))
  ensures pts_to input 'input_bytes **
          (match r with
           | Some (l, consumed) ->
             exists* m.
               L.is_valid_tls_record l m **
               pure (
                 match WS.parse_tls_record 'input_bytes with
                 | Some (m', n) -> m' == m /\ n == SZ.v consumed
                 | None -> False)
           | None ->
             pure (WS.parse_tls_record 'input_bytes == None))
