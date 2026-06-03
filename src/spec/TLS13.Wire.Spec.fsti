module TLS13.Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module SHC = TLS13.ServerHello.Checks
module T = TLS13.Types
module U8 = FStar.UInt8

(**
  Wire-level M/L boundary.

  The high-level model (M) is the pure message layer from TLS13.Messages,
  TLS13.Types, TLS13.StateMachine, and TLS13.ConnectionLog.
  The low-level representation (L) for supported wire formats is the
  extraction-oriented TLS13.Impl.Messages layer plus byte-buffer streaming
  views where the active implementation is still header-first.

  Pulse parsers/serializers should be exposed through TLS13.Impl.Parser and
  TLS13.Impl.Serializer and state their correctness by referring to the parse_*
  and serialize_* functions in this module.  The older framing modules are
  implementation backends only, not the public M/L codec boundary.
**)

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

val parse_client_hello:
  input:B.bytes ->
  GTot (option M.client_hello)

val parse_server_hello:
  input:B.bytes ->
  GTot (option M.server_hello)

val parse_certificate_msg:
  input:B.bytes ->
  GTot (option M.certificate_msg)

val parse_encrypted_extensions:
  input:B.bytes ->
  GTot (option M.encrypted_extensions)

val parse_certificate_verify:
  input:B.bytes ->
  GTot (option M.certificate_verify)

val parse_finished:
  input:B.bytes ->
  GTot (option M.finished)

val parse_key_update:
  input:B.bytes ->
  GTot (option M.key_update_request)

val parse_handshake:
  input:B.bytes ->
  GTot (option (M.handshake_msg & nat))

val parse_handshake_msg:
  input:B.bytes ->
  GTot (option (M.handshake_msg & nat))

val parse_supported_server_hello:
  input:B.bytes ->
  GTot (option M.server_hello)

val lemma_parse_supported_server_hello_ok:
  input:B.bytes ->
  Lemma (Some? (parse_supported_server_hello input) <==>
         SHC.server_hello_ok input)

val lemma_parse_supported_server_hello_fields:
  input:B.bytes ->
  Lemma
    (requires SHC.server_hello_ok input)
    (ensures (
      match parse_supported_server_hello input with
      | Some sh ->
        Seq.equal sh.M.random (Seq.slice input 6 38) /\
        ((SHC.server_hello_ok_52 input /\
          Seq.equal sh.M.key_share (Seq.slice input 52 84)) \/
         (SHC.server_hello_ok_58 input /\
          Seq.equal sh.M.key_share (Seq.slice input 58 90)))
      | None -> False))

val parse_certificate_leaf_der:
  input:B.bytes ->
  GTot (option B.bytes)

val serialize_client_hello:
  hello:M.client_hello ->
  GTot B.bytes

val serialize_server_hello:
  hello:M.server_hello ->
  GTot B.bytes

val serialize_encrypted_extensions:
  ee:M.encrypted_extensions ->
  GTot B.bytes

val serialize_certificate_msg:
  cert:M.certificate_msg ->
  GTot B.bytes

val serialize_certificate_verify:
  cv:M.certificate_verify ->
  GTot B.bytes

val serialize_finished:
  fin:M.finished ->
  GTot B.bytes

val serialize_supported_client_hello:
  hello:M.client_hello ->
  GTot B.bytes

val serialize_handshake:
  msg:M.handshake_msg ->
  GTot B.bytes

val serialize_handshake_msg:
  msg:M.handshake_msg ->
  GTot B.bytes

val lemma_serialize_finished_len:
  fin:M.finished ->
  Lemma (B.length (serialize_finished fin) == 32 /\
         B.length (serialize_handshake (M.Finished fin)) == 36 /\
         B.length (serialize_handshake_msg (M.Finished fin)) == 36)

val lemma_serialize_server_hello_len:
  sh:M.server_hello ->
  Lemma (B.length (serialize_handshake (M.ServerHello sh)) == 90 /\
         B.length (serialize_handshake_msg (M.ServerHello sh)) == 90)

val serialize_server_certificate_verify_input:
  transcript_hash:B.bytes ->
  GTot B.bytes

val lemma_serialize_server_certificate_verify_input_len32:
  transcript_hash:B.bytes{B.length transcript_hash == 32} ->
  Lemma (Seq.equal
    (serialize_server_certificate_verify_input transcript_hash)
    (H.certificate_verify_input transcript_hash))

val parse_record:
  input:B.bytes ->
  GTot (option (T.content_type & M.sealed_record & nat))

val parse_record_header:
  input:B.bytes ->
  GTot (option (T.content_type & nat))

val lemma_parse_record_header_some_iff:
  input:B.bytes{B.length input == 5} ->
  Lemma (Some? (parse_record_header input) <==>
    ((Seq.index input 0 = 0x14uy ||
      Seq.index input 0 = 0x15uy ||
      Seq.index input 0 = 0x16uy ||
      Seq.index input 0 = 0x17uy) &&
     Seq.index input 1 = 0x03uy &&
     Seq.index input 2 = 0x03uy &&
     read_u16 input 3 <= 16640))

val serialize_record:
  content_type:T.content_type ->
  fragment:B.bytes ->
  GTot B.bytes

val lemma_parse_record_serialize_record:
  content_type:T.content_type ->
  fragment:B.bytes{B.length fragment <= 16640} ->
  Lemma
    (B.length (serialize_record content_type fragment) == 5 + B.length fragment /\
     parse_record (serialize_record content_type fragment) ==
      Some (content_type, fragment, B.length (serialize_record content_type fragment)))

val parse_plaintext:
  input:B.bytes ->
  GTot (option M.plaintext)

val serialize_plaintext:
  pt:M.plaintext ->
  GTot B.bytes

val parse_sealed_record:
  input:B.bytes ->
  GTot (option M.sealed_record)

val serialize_sealed_record:
  record:M.sealed_record ->
  GTot B.bytes

val parse_tls_message:
  content_type:T.content_type ->
  fragment:B.bytes ->
  GTot (option M.tls_message)

val serialize_tls_message:
  msg:M.tls_message ->
  GTot (T.content_type & B.bytes)

val parse_tls_record:
  input:B.bytes ->
  GTot (option (M.tls_record & nat))

val serialize_tls_record:
  record:M.tls_record ->
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
