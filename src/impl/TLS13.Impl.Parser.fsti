module TLS13.Impl.Parser

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CR = TLS13.Impl.ConnectionState.Repr
module CT = TLS13.Impl.Client.Types
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module WS = TLS13.Wire.Spec

(**
  Parser interface at the M/L boundary.

  The allocating L parser surface consumes an owned input byte array without
  modifying it.  On success, it returns an extraction-oriented L value together
  with ownership evidence, and relates that L value to the pure M message
  produced by the corresponding TLS13.Wire.Spec parser.
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
             (exists* m.
               L.is_valid_tls_message l m **
               pure (CT.parsed_message_wire_success_for
                 content_type
                 (Ghost.reveal 'input_bytes)
                 l
                 m)) **
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

(**
  Extraction-facing record decoder used by the public client driver API.
  On success it returns an owned exact-length fragment vector plus the same
  parser and raw-delta facts required by the existing message dispatcher.
**)
fn decode_network_record
  (c:CR.connection_state)
  (raw: array U8.t)
  (raw_len: SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_len)
  returns r: L.decoded_network_record_result
  ensures CR.connection_exactly c 'st0 **
          pts_to raw 'raw_bytes **
          (match r with
           | L.NetworkRecordNeedMoreInput -> emp
           | L.NetworkRecordDecodeError -> emp
           | L.NetworkRecordOk decoded ->
            exists* fragment_bytes.
              V.pts_to decoded.L.decoded_record_fragment fragment_bytes **
              (match decoded.L.decoded_record_parsed with
               | Some l ->
                 (exists* m.
                   L.is_valid_tls_message l m **
                   pure (CT.parsed_message_wire_success_for
                     decoded.L.decoded_record_content_type
                     fragment_bytes
                     l
                     m)) **
                 pure (
                   exists ct msg.
                     L.content_type_matches
                       decoded.L.decoded_record_content_type
                       ct /\
                     WS.parse_tls_message ct fragment_bytes == Some msg) **
                 pure (CT.parsed_message_wire_success
                   decoded.L.decoded_record_content_type
                   (Ghost.reveal fragment_bytes)
                   l)
               | None ->
                 pure (forall (ct:T.content_type).
                   L.content_type_matches
                     decoded.L.decoded_record_content_type
                     ct ==>
                   WS.parse_tls_message ct fragment_bytes == None)) **
              pure (
                V.is_full_vec decoded.L.decoded_record_fragment /\
                V.length decoded.L.decoded_record_fragment ==
                  SZ.v decoded.L.decoded_record_fragment_len /\
                B.length fragment_bytes ==
                  SZ.v decoded.L.decoded_record_fragment_len /\
                CT.network_input_wf
                  'st0
                  decoded.L.decoded_record_content_type
                  fragment_bytes
                  (Ghost.reveal 'raw_bytes)))

(**
  Streaming-buffer decoder for extracted drivers.  On success it consumes
  exactly the first complete TLS record in the input buffer, returning owned
  copies of both that raw record prefix and its decoded dispatcher fragment.
  The caller remains responsible for retaining any bytes after consumed_len.
**)
fn decode_network_buffer
  (c:CR.connection_state)
  (raw: array U8.t)
  (raw_len: SZ.t)
  requires CR.connection_exactly c 'st0 **
           pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_len)
  returns r: L.decoded_network_buffer_result
  ensures CR.connection_exactly c 'st0 **
          pts_to raw 'raw_bytes **
          (match r with
           | L.NetworkBufferNeedMoreInput -> emp
           | L.NetworkBufferDecodeError -> emp
           | L.NetworkBufferOk decoded ->
            exists* raw_record_bytes fragment_bytes.
              V.pts_to decoded.L.decoded_buffer_raw_record raw_record_bytes **
              V.pts_to decoded.L.decoded_buffer_fragment fragment_bytes **
              (match decoded.L.decoded_buffer_parsed with
               | Some l ->
                 (exists* m.
                  L.is_valid_tls_message l m **
                  pure (CT.parsed_message_wire_success_for
                    decoded.L.decoded_buffer_content_type
                    fragment_bytes
                    l
                    m)) **
                 pure (
                  exists ct msg.
                    L.content_type_matches
                      decoded.L.decoded_buffer_content_type
                      ct /\
                    WS.parse_tls_message ct fragment_bytes == Some msg) **
                 pure (CT.parsed_message_wire_success
                  decoded.L.decoded_buffer_content_type
                  (Ghost.reveal fragment_bytes)
                  l)
               | None ->
                 pure (forall (ct:T.content_type).
                  L.content_type_matches
                    decoded.L.decoded_buffer_content_type
                    ct ==>
                  WS.parse_tls_message ct fragment_bytes == None)) **
              pure (
                V.is_full_vec decoded.L.decoded_buffer_raw_record /\
                V.length decoded.L.decoded_buffer_raw_record ==
                  SZ.v decoded.L.decoded_buffer_raw_record_len /\
                B.length raw_record_bytes ==
                  SZ.v decoded.L.decoded_buffer_raw_record_len /\
                decoded.L.decoded_buffer_raw_record_len ==
                  decoded.L.decoded_buffer_consumed_len /\
                SZ.v decoded.L.decoded_buffer_consumed_len <=
                  B.length (Ghost.reveal 'raw_bytes) /\
                Seq.equal
                  raw_record_bytes
                  (Seq.slice
                   (Ghost.reveal 'raw_bytes)
                   0
                   (SZ.v decoded.L.decoded_buffer_consumed_len)) /\
                V.is_full_vec decoded.L.decoded_buffer_fragment /\
                V.length decoded.L.decoded_buffer_fragment ==
                  SZ.v decoded.L.decoded_buffer_fragment_len /\
                B.length fragment_bytes ==
                  SZ.v decoded.L.decoded_buffer_fragment_len /\
                CT.network_input_wf
                  'st0
                  decoded.L.decoded_buffer_content_type
                  fragment_bytes
                  raw_record_bytes))
