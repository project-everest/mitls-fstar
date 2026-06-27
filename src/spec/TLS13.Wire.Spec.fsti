module TLS13.Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module GCE = TLS13.Wire.Generated.CertificateEntry
module GCert = TLS13.Wire.Generated.Certificate
module GCH = TLS13.Wire.Generated.ClientHello
module GCS = TLS13.Wire.Generated.CipherSuite
module GCV = TLS13.Wire.Generated.CertificateVerify
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GESN = TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
module GESA = TLS13.Wire.Generated.ExtensionClientHello_extension_data_signature_algorithms
module GESK = TLS13.Wire.Generated.ExtensionClientHello_extension_data_key_share
module GESV = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_versions
module GESG = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_groups
module GHS = TLS13.Wire.Generated.Handshake
module GNG = TLS13.Wire.Generated.NamedGroup
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GSN = TLS13.Wire.Generated.ServerName
module GHN = TLS13.Wire.Generated.HostName
module GSS = TLS13.Wire.Generated.SignatureScheme
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module LP = LowParse.Spec
module SHC = TLS13.ServerHello.Checks

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
  GTot (n:nat{n < 65536})

val lemma_read_u16_definition:
  input:B.bytes ->
  pos:nat{pos + 2 <= B.length input} ->
  Lemma (read_u16 input pos ==
         U8.v (Seq.index input pos) * 256 +
         U8.v (Seq.index input (pos + 1)))

val read_u24:
  input:B.bytes ->
  pos:nat{pos + 3 <= B.length input} ->
  GTot nat

val lemma_read_u24_one:
  input:B.bytes{B.length input >= 4} ->
  Lemma (read_u24 input 1 == 1 <==>
         (U8.v (Seq.index input 1) == 0 /\
          U8.v (Seq.index input 2) == 0 /\
          U8.v (Seq.index input 3) == 1))

val parse_ignored_post_handshake:
  input:B.bytes ->
  GTot (option B.bytes)

val lemma_parse_ignored_post_handshake_def:
  input:B.bytes ->
  Lemma (parse_ignored_post_handshake input ==
    (if B.length input >= 4 &&
        U8.v (Seq.index input 0) = 4 &&
        (U8.v (Seq.index input 1) * 65536 +
         U8.v (Seq.index input 2) * 256 +
         U8.v (Seq.index input 3)) + 4 = B.length input
     then Some (Seq.slice input 4 (B.length input))
     else None))

val parse_key_update:
  input:B.bytes ->
  GTot (option M.key_update_request)

val lemma_parse_key_update_def:
  input:B.bytes ->
  Lemma (parse_key_update input ==
    (if B.length input = 5 &&
        U8.v (Seq.index input 0) = 24 &&
        U8.v (Seq.index input 1) = 0 &&
        U8.v (Seq.index input 2) = 0 &&
        U8.v (Seq.index input 3) = 1
     then (match U8.v (Seq.index input 4) with
           | 0 -> Some M.UpdateNotRequested
           | 1 -> Some M.UpdateRequested
           | _ -> None)
     else None))

val synth_handshake_msg_of:
  h:GHS.handshake ->
  GTot (option M.handshake_msg)

val parse_handshake:
  input:B.bytes ->
  GTot (option (M.handshake_msg & nat))

val parse_handshake_msg:
  input:B.bytes ->
  GTot (option (M.handshake_msg & nat))

val serialize_handshake:
  msg:M.handshake_msg ->
  GTot B.bytes

val serialize_handshake_msg:
  msg:M.handshake_msg ->
  GTot B.bytes

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

val parse_record_wire:
  input:B.bytes ->
  GTot (option (T.content_type & M.sealed_record & nat))

val lemma_parse_record_implies_parse_record_wire:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record input with
      | Some (content_type, fragment, consumed) ->
        parse_record_wire input == Some (content_type, fragment, consumed)
      | None -> True))

val lemma_parse_record_wire_some_consumed_positive:
  input:B.bytes ->
  content_type:T.content_type ->
  fragment:M.sealed_record ->
  consumed:nat ->
  Lemma
    (requires parse_record_wire input == Some (content_type, fragment, consumed))
    (ensures consumed > 0 /\ consumed <= B.length input)

val parse_record_header:
  input:B.bytes ->
  GTot (option (T.content_type & nat))

val lemma_parse_record_header_some_iff:
  input:B.bytes{B.length input == 5} ->
  Lemma (Some? (parse_record_header input) <==>
    ((Seq.index input 0 = 0x00uy ||
      Seq.index input 0 = 0x14uy ||
      Seq.index input 0 = 0x15uy ||
      Seq.index input 0 = 0x16uy ||
      Seq.index input 0 = 0x17uy) &&
     Seq.index input 1 = 0x03uy &&
     (Seq.index input 2 = 0x03uy ||
      (Seq.index input 0 = 0x16uy && Seq.index input 2 = 0x01uy)) &&
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

val lemma_parse_plaintext_serialize_plaintext:
  pt:M.plaintext ->
  Lemma (parse_plaintext (serialize_plaintext pt) == Some pt)

(* --- Branch-specific (LTL/pairing) bespoke ServerHello field parser.  Parses a
       canonical fixed-layout ChaCha20 ServerHello, extracting the 32-byte random
       and the x25519 key_share by byte offset (52- or 58-byte key_share
       position).  Retargeted off the deleted M.server_hello projection record
       onto this local field-view record. --- *)
type supported_server_hello = {
  random: B.bytes_of_len 32;
  key_share: B.bytes_of_len 32;
  cipher_suite: T.cipher_suite;
}

val parse_supported_server_hello:
  input:B.bytes ->
  GTot (option supported_server_hello)

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
        sh.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256 /\
        Seq.equal sh.random (Seq.slice input 6 38) /\
        ((SHC.server_hello_ok_52 input /\
          Seq.equal sh.key_share (Seq.slice input 52 84)) \/
         (SHC.server_hello_ok_58 input /\
          Seq.equal sh.key_share (Seq.slice input 58 90)))
      | None -> False))

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

(* The generated [Invalid] content type (wire byte 0) never carries a TLS
   message: the spec parser rejects it.  Exposed so consumers can discharge the
   "no content type matches" obligation for an unknown record content type. *)
val lemma_parse_tls_message_invalid_none:
  fragment:B.bytes ->
  Lemma (parse_tls_message T.Invalid fragment == None)

val lemma_parse_handshake_none_of_lp_none:
  fragment:B.bytes ->
  Lemma
    (requires LP.parse GHS.handshake_parser fragment == None)
    (ensures parse_handshake fragment == None)

val lemma_parse_handshake_none_of_synth_none:
  fragment:B.bytes ->
  v:GHS.handshake ->
  consumed:LP.consumed_length fragment ->
  Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, consumed) /\
              synth_handshake_msg_of v == None)
    (ensures parse_handshake fragment == None)

val lemma_ptm_handshake_fallback:
  fragment:B.bytes ->
  Lemma
    (requires parse_handshake fragment == None)
    (ensures parse_tls_message T.Handshake fragment ==
      (match parse_key_update fragment with
       | Some req -> Some (M.TlsKeyUpdate req)
       | None ->
         (match parse_ignored_post_handshake fragment with
          | Some body -> Some (M.TlsIgnoredPostHandshake body)
          | None -> None)))

val serialize_tls_message:
  msg:M.tls_message ->
  GTot (T.content_type & B.bytes)

val lemma_serialize_tls_message_handshake:
  hs:M.handshake_msg ->
  Lemma (serialize_tls_message (M.TlsHandshake hs) == (T.Handshake, serialize_handshake hs))

val lemma_serialize_tls_message_application_data:
  data:B.bytes ->
  Lemma (serialize_tls_message (M.TlsApplicationData data) == (T.Application_data, data))

val lemma_serialize_tls_message_close_notify:
  unit ->
  Lemma (serialize_tls_message (M.TlsAlert T.Close_notify) ==
    (T.Alert, B.of_list [2uy; 0uy]))

val lemma_serialize_tls_message_change_cipher_spec:
  unit ->
  Lemma (serialize_tls_message M.TlsChangeCipherSpec ==
    (T.Change_cipher_spec, B.singleton 1uy))

val lemma_serialize_tls_message_key_update_not_requested:
  unit ->
  Lemma (serialize_tls_message (M.TlsKeyUpdate M.UpdateNotRequested) ==
    (T.Handshake, B.of_list [24uy; 0uy; 0uy; 1uy; 0uy]))

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

val lemma_parse_record_fragment_bound:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record input with
      | Some (_, fragment, _) -> B.length fragment <= 16640
      | None -> True))

val lemma_parse_record_wire_fragment_bound:
  input:B.bytes ->
  Lemma
    (ensures (
      match parse_record_wire input with
      | Some (_, fragment, _) -> B.length fragment <= 16640
      | None -> True))

val lemma_parse_tls_message_round_trip:
  content_type:T.content_type ->
  fragment:B.bytes ->
  Lemma
    (ensures (
      match parse_tls_message content_type fragment with
      | Some (M.TlsHandshake (M.ClientHello ch)) ->
        Seq.equal fragment (serialize_handshake (M.ClientHello ch))
      | Some (M.TlsHandshake (M.ServerHello sh)) ->
        Seq.equal fragment (serialize_handshake (M.ServerHello sh))
      | Some (M.TlsHandshake (M.EncryptedExtensions ee)) ->
        Seq.equal fragment (serialize_handshake (M.EncryptedExtensions ee))
      | Some (M.TlsHandshake (M.Certificate c)) ->
        Seq.equal fragment (serialize_handshake (M.Certificate c))
      | Some (M.TlsHandshake (M.CertificateVerify cv)) ->
        Seq.equal fragment (serialize_handshake (M.CertificateVerify cv))
      | _ -> True))
