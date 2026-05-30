module TLS13.Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8

type parse_error = T.tls_error

val read_u16:
  input:B.bytes ->
  pos:nat{pos + 2 <= B.length input} ->
  GTot nat

val lemma_read_u16_definition:
  input:B.bytes ->
  pos:nat{pos + 2 <= B.length input} ->
  Lemma (read_u16 input pos ==
         U8.v (Seq.index input pos) * 256 +
         U8.v (Seq.index input (pos + 1)))

val parse_handshake:
  input:B.bytes ->
  GTot (option (H.handshake_msg & nat))

val parse_supported_server_hello:
  input:B.bytes ->
  GTot (option H.server_hello)

val parse_certificate_leaf_der:
  input:B.bytes ->
  GTot (option B.bytes)

val parse_certificate_verify:
  input:B.bytes ->
  GTot (option H.certificate_verify)

val serialize_supported_client_hello:
  hello:H.client_hello ->
  GTot B.bytes

val serialize_handshake:
  msg:H.handshake_msg ->
  GTot B.bytes

val serialize_server_certificate_verify_input:
  transcript_hash:B.bytes ->
  GTot B.bytes

val parse_record:
  input:B.bytes ->
  GTot (option (T.content_type & R.sealed_record & nat))

val parse_record_header:
  input:B.bytes ->
  GTot (option (T.content_type & nat))

val serialize_record:
  content_type:T.content_type ->
  fragment:B.bytes ->
  GTot B.bytes

val lemma_parse_record_serializes:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record input with
      | Some (content_type, fragment, consumed) ->
        consumed > 0 /\
        consumed <= B.length input /\
        consumed == B.length (serialize_record content_type fragment) /\
        Seq.equal (serialize_record content_type fragment)
                  (Seq.slice input 0 consumed)
      | None -> True))
