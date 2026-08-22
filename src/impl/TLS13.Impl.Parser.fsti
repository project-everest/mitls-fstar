module TLS13.Impl.Parser

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
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

  Unused generic message/record parsers are deliberately not exposed here: the
  active extracted client path relies on parse_tls_message plus the network
  decoder helpers below.
**)

fn parse_tls_message
  (content_type: U8.t)
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len /\
                 SZ.v input_len <= L.max_record_fragment_len)
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

fn parse_handshake_prefix
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len /\
                SZ.v input_len <= L.max_record_fragment_len)
  returns r: option L.parsed_handshake_prefix
  ensures pts_to input 'input_bytes **
          (match r with
           | None -> emp
           | Some parsed ->
            exists* msg prefix_bytes.
              V.pts_to parsed.L.parsed_handshake_fragment prefix_bytes **
              L.is_valid_tls_message
                parsed.L.parsed_handshake_message
                (M.TlsHandshake msg) **
              pure (CT.parsed_message_wire_success_for
                0x16uy
                prefix_bytes
                parsed.L.parsed_handshake_message
                (M.TlsHandshake msg)) **
              pure (
                V.is_full_vec parsed.L.parsed_handshake_fragment /\
                V.length parsed.L.parsed_handshake_fragment ==
                  SZ.v parsed.L.parsed_handshake_consumed /\
                B.length prefix_bytes ==
                  SZ.v parsed.L.parsed_handshake_consumed /\
                0 < SZ.v parsed.L.parsed_handshake_consumed /\
                SZ.v parsed.L.parsed_handshake_consumed <=
                  B.length (Ghost.reveal 'input_bytes) /\
                Seq.equal
                  prefix_bytes
                  (Seq.slice
                    (Ghost.reveal 'input_bytes)
                    0
                    (SZ.v parsed.L.parsed_handshake_consumed)) /\
                WS.parse_handshake (Ghost.reveal 'input_bytes) ==
                  Some
                    (msg,
                     SZ.v parsed.L.parsed_handshake_consumed)))

(**
  A one-sided completeness check: it only ever reports [true] when the
  LowParse validator for [handshake] rejects [input] outright, which is
  exactly the case where no prefix of [input] can ever be completed into a
  handshake message by appending more bytes. Reports [false] whenever the
  validator accepts (including when a full [parse_handshake_prefix] would
  still fail downstream, e.g. on an unrepresentable message) so callers must
  treat [false] as "cannot tell".
**)
fn handshake_prefix_absent
  (input: array U8.t)
  (input_len: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len)
  returns absent: bool
  ensures pts_to input 'input_bytes **
          pure (absent ==> WS.parse_handshake (Ghost.reveal 'input_bytes) == None)

fn parse_handshake_prefix_at
  (input: array U8.t)
  (input_len: SZ.t)
  (offset: SZ.t)
  requires pts_to input 'input_bytes **
           pure (B.length 'input_bytes == SZ.v input_len /\
                 SZ.v offset < SZ.v input_len /\
                 SZ.v input_len <= Bounds.max_handshake_flight_len)
  returns r: option L.parsed_handshake_prefix
  ensures pts_to input 'input_bytes **
          (match r with
           | None -> emp
           | Some parsed ->
             exists* msg prefix_bytes.
               V.pts_to parsed.L.parsed_handshake_fragment prefix_bytes **
               L.is_valid_tls_message
                 parsed.L.parsed_handshake_message
                 (M.TlsHandshake msg) **
               pure (CT.parsed_message_wire_success_for
                 0x16uy
                 prefix_bytes
                 parsed.L.parsed_handshake_message
                 (M.TlsHandshake msg)) **
               pure (
                 V.is_full_vec parsed.L.parsed_handshake_fragment /\
                 V.length parsed.L.parsed_handshake_fragment ==
                   SZ.v parsed.L.parsed_handshake_consumed /\
                 B.length prefix_bytes ==
                   SZ.v parsed.L.parsed_handshake_consumed /\
                 0 < SZ.v parsed.L.parsed_handshake_consumed /\
                 SZ.v offset + SZ.v parsed.L.parsed_handshake_consumed <=
                   B.length (Ghost.reveal 'input_bytes) /\
                 Seq.equal
                   prefix_bytes
                   (Seq.slice
                     (Ghost.reveal 'input_bytes)
                     (SZ.v offset)
                     (SZ.v offset +
                       SZ.v parsed.L.parsed_handshake_consumed)) /\
                 WS.parse_handshake
                   (Seq.slice
                     (Ghost.reveal 'input_bytes)
                     (SZ.v offset)
                     (B.length (Ghost.reveal 'input_bytes))) ==
                   Some
                     (msg,
                      SZ.v parsed.L.parsed_handshake_consumed)))
(**
  Extraction-facing record decoder used by the public client driver API.
  On success it returns an owned exact-length fragment vector plus the same
  parser and raw-delta facts required by the existing message dispatcher.  The
  input bytes are also required to parse as exactly one TLS outer record.
  CT.network_input_wf records how the dispatcher fragment relates to that raw
  record: cleartext records expose the outer fragment, while ApplicationData
  records expose a record-layer open result followed by TLSInnerPlaintext
  decoding.
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
           | L.NetworkRecordNeedMoreInput ->
             pure (
               WS.record_prefix_incomplete (Ghost.reveal 'raw_bytes) /\
               WS.parse_record_wire (Ghost.reveal 'raw_bytes) == None)
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
                (exists outer_ct outer_fragment.
                   WS.parse_record_wire (Ghost.reveal 'raw_bytes) ==
                     Some (outer_ct, outer_fragment, B.length (Ghost.reveal 'raw_bytes))) /\
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
  The raw prefix is required to parse as exactly one TLS outer record.
  CT.network_input_wf records how the dispatcher fragment relates to that raw
  record: cleartext records expose the outer fragment, while ApplicationData
  records expose a record-layer open result followed by TLSInnerPlaintext
  decoding.
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
           | L.NetworkBufferNeedMoreInput ->
             pure (
               WS.record_prefix_incomplete (Ghost.reveal 'raw_bytes) /\
               WS.parse_record_wire (Ghost.reveal 'raw_bytes) == None)
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
                0 < SZ.v decoded.L.decoded_buffer_consumed_len /\
                SZ.v decoded.L.decoded_buffer_consumed_len <=
                  B.length (Ghost.reveal 'raw_bytes) /\
                Seq.equal
                  raw_record_bytes
                  (Seq.slice
                   (Ghost.reveal 'raw_bytes)
                   0
                   (SZ.v decoded.L.decoded_buffer_consumed_len)) /\
                (exists outer_ct outer_fragment.
                   WS.parse_record_wire raw_record_bytes ==
                     Some (outer_ct, outer_fragment, B.length raw_record_bytes)) /\
                V.is_full_vec decoded.L.decoded_buffer_fragment /\
                V.length decoded.L.decoded_buffer_fragment ==
                  SZ.v decoded.L.decoded_buffer_fragment_len /\
                B.length fragment_bytes ==
                  SZ.v decoded.L.decoded_buffer_fragment_len /\
                SZ.v decoded.L.decoded_buffer_fragment_len <=
                  L.max_record_fragment_len /\
                CT.network_input_wf
                  'st0
                  decoded.L.decoded_buffer_content_type
                  fragment_bytes
                  raw_record_bytes /\
                (~ decoded.L.decoded_buffer_protected ==>
                  (exists outer_ct.
                    L.content_type_matches
                      decoded.L.decoded_buffer_content_type
                      outer_ct /\
                    WS.parse_record_wire raw_record_bytes ==
                      Some
                        (outer_ct,
                         Ghost.reveal fragment_bytes,
                         B.length raw_record_bytes))) /\
                (decoded.L.decoded_buffer_protected ==>
                  CT.protected_decoder_fragment_relation
                    'st0
                    decoded.L.decoded_buffer_content_type
                    fragment_bytes
                    raw_record_bytes /\
                  (exists outer_fragment.
                    WS.parse_record raw_record_bytes ==
                      Some
                        (T.Application_data,
                         outer_fragment,
                         B.length raw_record_bytes)))))
