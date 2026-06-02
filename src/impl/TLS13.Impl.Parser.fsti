module TLS13.Impl.Parser

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

(**
  Parser interface at the M/L boundary.

  Each parser consumes an owned input byte array without modifying it.  On
  success, it returns an extraction-oriented L value together with ownership
  evidence, and relates that L value to the pure M message produced by the
  corresponding TLS13.Wire.Spec parser.
**)

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
             exists* ct m.
               L.is_valid_tls_message l m **
               pure (L.content_type_matches content_type ct /\
                     WS.parse_tls_message ct 'input_bytes == Some m)
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
