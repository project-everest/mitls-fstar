module TLS13.Impl.Serializer

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box }

module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.ConnectionState
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module Rec = TLS13.Record
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
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

fn serialize_client_hello_from_start
  (#start: erased CS.handshake_start)
  (#ch: erased M.client_hello)
  (start_random: V.vec U8.t)
  (start_server_name: V.vec U8.t)
  (start_server_name_len: box SZ.t)
  (start_key_share: V.vec U8.t)
  (start_cipher_suites: V.vec U16.t)
  (start_cipher_suites_len: box SZ.t)
  (start_signature_schemes: V.vec U16.t)
  (start_signature_schemes_len: box SZ.t)
  (client_hello_present: box bool)
  (l: L.client_hello)
  (client_hello_bytes: V.vec U8.t)
  (client_hello_bytes_len: box SZ.t)
  (network_out: array U8.t)
  (network_out_len: SZ.t)
  requires exists* random server_name server_name_len key_share
                  cipher_suites cipher_suites_len
                  signature_schemes signature_schemes_len
                  old_present old_l_random old_l_server_name old_l_key_share
                  old_l_cipher_suites old_l_signature_schemes
                  old_client_hello_bytes_len old_client_hello_bytes old_network_out.
          V.pts_to start_random random **
          V.pts_to start_server_name server_name **
          Box.pts_to start_server_name_len server_name_len **
          V.pts_to start_key_share key_share **
          V.pts_to start_cipher_suites cipher_suites **
          Box.pts_to start_cipher_suites_len cipher_suites_len **
          V.pts_to start_signature_schemes signature_schemes **
          Box.pts_to start_signature_schemes_len signature_schemes_len **
          Box.pts_to client_hello_present old_present **
          V.pts_to l.L.client_hello_random old_l_random **
          V.pts_to l.L.client_hello_server_name old_l_server_name **
          V.pts_to l.L.client_hello_key_share old_l_key_share **
          V.pts_to l.L.client_hello_cipher_suites old_l_cipher_suites **
          V.pts_to l.L.client_hello_signature_schemes old_l_signature_schemes **
          V.pts_to client_hello_bytes old_client_hello_bytes **
          Box.pts_to client_hello_bytes_len old_client_hello_bytes_len **
          pts_to network_out old_network_out **
          pure (old_present == false /\
                V.is_full_vec start_random /\
                V.is_full_vec start_server_name /\
                V.is_full_vec start_key_share /\
                V.is_full_vec start_cipher_suites /\
                V.is_full_vec start_signature_schemes /\
                V.is_full_vec l.L.client_hello_random /\
                V.is_full_vec l.L.client_hello_server_name /\
                V.is_full_vec l.L.client_hello_key_share /\
                V.is_full_vec l.L.client_hello_cipher_suites /\
                V.is_full_vec l.L.client_hello_signature_schemes /\
                V.is_full_vec client_hello_bytes /\
                V.length start_random == 32 /\
                V.length start_server_name == L.max_server_name_len /\
                V.length start_key_share == 32 /\
                V.length start_cipher_suites == L.max_cipher_suites /\
                V.length start_signature_schemes == L.max_signature_schemes /\
                V.length l.L.client_hello_random == 32 /\
                V.length l.L.client_hello_server_name == L.max_server_name_len /\
                V.length l.L.client_hello_key_share == 32 /\
                V.length l.L.client_hello_cipher_suites == L.max_cipher_suites /\
                V.length l.L.client_hello_signature_schemes == L.max_signature_schemes /\
                V.length client_hello_bytes == 512 /\
                B.length random == 32 /\
                B.length server_name == L.max_server_name_len /\
                B.length key_share == 32 /\
                Seq.length cipher_suites == L.max_cipher_suites /\
                Seq.length signature_schemes == L.max_signature_schemes /\
                B.length old_l_random == 32 /\
                B.length old_l_server_name == L.max_server_name_len /\
                B.length old_l_key_share == 32 /\
                Seq.length old_l_cipher_suites == L.max_cipher_suites /\
                Seq.length old_l_signature_schemes == L.max_signature_schemes /\
                B.length old_client_hello_bytes == 512 /\
                B.length old_network_out == SZ.v network_out_len /\
                517 <= SZ.v network_out_len /\
                SZ.v server_name_len <= B.length server_name /\
                SZ.v cipher_suites_len <= Seq.length cipher_suites /\
                SZ.v signature_schemes_len <= Seq.length signature_schemes /\
                Seq.equal random (Ghost.reveal start).CS.start_client_random /\
                B.length (Ghost.reveal start).CS.start_server_name == SZ.v server_name_len /\
                Seq.equal (Ghost.reveal start).CS.start_server_name (Seq.slice server_name 0 (SZ.v server_name_len)) /\
                Seq.equal key_share (Ghost.reveal start).CS.start_client_key_share_public /\
                L.cipher_suites_match
                  cipher_suites
                  (SZ.v cipher_suites_len)
                  (Ghost.reveal start).CS.start_cipher_suites /\
                L.signature_schemes_match
                  signature_schemes
                  (SZ.v signature_schemes_len)
                  (Ghost.reveal start).CS.start_signature_schemes /\
                Ghost.reveal ch == {
                  M.random = (Ghost.reveal start).CS.start_client_random;
                  M.server_name = Some (Ghost.reveal start).CS.start_server_name;
                  M.key_share = (Ghost.reveal start).CS.start_client_key_share_public;
                  M.cipher_suites = (Ghost.reveal start).CS.start_cipher_suites;
                  M.signature_schemes = (Ghost.reveal start).CS.start_signature_schemes;
                })
  returns written: (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures exists* random server_name server_name_len key_share
                 cipher_suites cipher_suites_len
                 signature_schemes signature_schemes_len
                 handshake_bytes network_out_bytes handshake_len.
          V.pts_to start_random random **
          V.pts_to start_server_name server_name **
          Box.pts_to start_server_name_len server_name_len **
          V.pts_to start_key_share key_share **
          V.pts_to start_cipher_suites cipher_suites **
          Box.pts_to start_cipher_suites_len cipher_suites_len **
          V.pts_to start_signature_schemes signature_schemes **
          Box.pts_to start_signature_schemes_len signature_schemes_len **
          Box.pts_to client_hello_present true **
          V.pts_to l.L.client_hello_random random **
          V.pts_to l.L.client_hello_server_name server_name **
          V.pts_to l.L.client_hello_key_share key_share **
          V.pts_to l.L.client_hello_cipher_suites cipher_suites **
          V.pts_to l.L.client_hello_signature_schemes signature_schemes **
          V.pts_to client_hello_bytes handshake_bytes **
          Box.pts_to client_hello_bytes_len handshake_len **
          pts_to network_out network_out_bytes **
          pure (V.is_full_vec start_random /\
               V.is_full_vec start_server_name /\
               V.is_full_vec start_key_share /\
               V.is_full_vec start_cipher_suites /\
               V.is_full_vec start_signature_schemes /\
               V.is_full_vec l.L.client_hello_random /\
               V.is_full_vec l.L.client_hello_server_name /\
               V.is_full_vec l.L.client_hello_key_share /\
               V.is_full_vec l.L.client_hello_cipher_suites /\
               V.is_full_vec l.L.client_hello_signature_schemes /\
               V.is_full_vec client_hello_bytes /\
               V.length start_random == 32 /\
               V.length start_server_name == L.max_server_name_len /\
               V.length start_key_share == 32 /\
               V.length start_cipher_suites == L.max_cipher_suites /\
               V.length start_signature_schemes == L.max_signature_schemes /\
               V.length l.L.client_hello_random == 32 /\
               V.length l.L.client_hello_server_name == L.max_server_name_len /\
               V.length l.L.client_hello_key_share == 32 /\
               V.length l.L.client_hello_cipher_suites == L.max_cipher_suites /\
               V.length l.L.client_hello_signature_schemes == L.max_signature_schemes /\
               V.length client_hello_bytes == 512 /\
               B.length random == 32 /\
               B.length server_name == L.max_server_name_len /\
               B.length key_share == 32 /\
               Seq.length cipher_suites == L.max_cipher_suites /\
               Seq.length signature_schemes == L.max_signature_schemes /\
               B.length handshake_bytes == 512 /\
               B.length network_out_bytes == SZ.v network_out_len /\
               SZ.v server_name_len <= B.length server_name /\
               SZ.v cipher_suites_len <= Seq.length cipher_suites /\
               SZ.v signature_schemes_len <= Seq.length signature_schemes /\
               Seq.equal random (Ghost.reveal start).CS.start_client_random /\
               B.length (Ghost.reveal start).CS.start_server_name == SZ.v server_name_len /\
               Seq.equal (Ghost.reveal start).CS.start_server_name (CL.raw_slice server_name 0 (SZ.v server_name_len)) /\
               Seq.equal key_share (Ghost.reveal start).CS.start_client_key_share_public /\
               L.cipher_suites_match
                 cipher_suites
                 (SZ.v cipher_suites_len)
                 (Ghost.reveal start).CS.start_cipher_suites /\
               L.signature_schemes_match
                 signature_schemes
                 (SZ.v signature_schemes_len)
                 (Ghost.reveal start).CS.start_signature_schemes /\
               Seq.equal random (Ghost.reveal ch).M.random /\
               L.optional_byte_prefix_matches
                 true
                 server_name
                 server_name_len
                 (Ghost.reveal ch).M.server_name /\
               Seq.equal key_share (Ghost.reveal ch).M.key_share /\
               L.cipher_suites_match
                 cipher_suites
                 (SZ.v cipher_suites_len)
                 (Ghost.reveal ch).M.cipher_suites /\
               L.signature_schemes_match
                 signature_schemes
                 (SZ.v signature_schemes_len)
                 (Ghost.reveal ch).M.signature_schemes /\
               SZ.v handshake_len == B.length (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch))) /\
               SZ.v handshake_len <= B.length handshake_bytes /\
               Seq.equal
                 (CL.raw_slice handshake_bytes 0 (SZ.v handshake_len))
                 (WS.serialize_handshake (M.ClientHello (Ghost.reveal ch))) /\
               SZ.v written ==
                 B.length (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello (Ghost.reveal ch)))) /\
               5 <= SZ.v written /\
               SZ.v written <= B.length network_out_bytes /\
               Seq.equal
                 (CL.raw_slice network_out_bytes 0 (SZ.v written))
                 (CS.serialized_cleartext_tls_message (M.TlsHandshake (M.ClientHello (Ghost.reveal ch)))) /\
               CS.raw_records_exactly
                 (CL.raw_slice network_out_bytes 0 (SZ.v written))
                 T.Handshake
                 1)

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
  (fragment_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to out 'old_bytes **
           pure (B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 5 /\
                 SZ.v fragment_len <= 16640)
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
  (write_state: Rec.record_state)
  (lfin: L.finished)
  (handshake_out: array U8.t)
  (network_out: array U8.t)
  (network_out_len: SZ.t)
  requires Rec.is_record_state write_state 'record_write **
           (exists* fin. L.is_valid_finished lfin fin) **
           pts_to handshake_out 'old_handshake **
           pts_to network_out 'old_network **
           pure (B.length 'old_handshake == 36 /\
                B.length 'old_network == SZ.v network_out_len /\
                58 <= SZ.v network_out_len)
  returns written: (n:SZ.t{SZ.v n <= SZ.v network_out_len})
  ensures exists* fin handshake_bytes network_bytes.
          Rec.is_record_state write_state 'record_write **
          L.is_valid_finished lfin fin **
          pts_to handshake_out handshake_bytes **
          pts_to network_out network_bytes **
          pure (B.length handshake_bytes == 36 /\
                Seq.equal handshake_bytes (WS.serialize_handshake (M.Finished fin)) /\
                B.length network_bytes == SZ.v network_out_len /\
                SZ.v written == 58 /\
                (let raw_prefix = Seq.slice network_bytes 0 (SZ.v written) in
                CS.raw_records_exactly raw_prefix T.ApplicationData 1))

fn serialize_finished_handshake
  (#fin: erased M.finished)
  (lfin: L.finished)
  (handshake_out: array U8.t)
  (handshake_out_len: SZ.t)
  requires L.is_valid_finished lfin (Ghost.reveal fin) **
           pts_to handshake_out 'old_handshake **
           pure (B.length 'old_handshake == SZ.v handshake_out_len /\
                 SZ.v handshake_out_len == 36)
  returns written: (n:SZ.t{SZ.v n <= SZ.v handshake_out_len})
  ensures exists* handshake_bytes.
          L.is_valid_finished lfin (Ghost.reveal fin) **
          pts_to handshake_out handshake_bytes **
          pure (B.length handshake_bytes == 36 /\
                SZ.v written == 36 /\
                Seq.equal handshake_bytes (WS.serialize_handshake (M.Finished (Ghost.reveal fin))))

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
