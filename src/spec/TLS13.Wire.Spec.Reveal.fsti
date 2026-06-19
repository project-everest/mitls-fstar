module TLS13.Wire.Spec.Reveal

(**
  Spec-reveal helper for the M/L parser implementation (TLS13.Impl.Parser).

  TLS13.Wire.Spec exposes [parse_tls_message]/[parse_record]/[parse_handshake]
  as abstract vals, and only one behavioural lemma
  ([lemma_parse_tls_message_round_trip]).  The implementation in
  TLS13.Impl.Parser needs the per-content-type definitional behaviour of
  [parse_tls_message] (and the connection between the QuackyDucky handshake
  parser and [parse_handshake]) to discharge its post-conditions.

  TLS13.Impl.Parser cannot [friend TLS13.Wire.Spec] itself, because its
  interface transitively depends on TLS13.Wire.Spec (through
  TLS13.Impl.Client.Types / TLS13.Impl.Messages) as a non-friend dependence.
  This module instead friends TLS13.Wire.Spec and re-exports the needed facts
  as lemmas referring only to spec/generated types (B/M/T/GHS), which
  TLS13.Impl.Parser then consumes as an ordinary non-friend dependence.
*)

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module T = TLS13.Types
module H = TLS13.Handshake.Spec
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module WS = TLS13.Wire.Spec
module GHS = TLS13.Wire.Generated.Handshake
module GSS = TLS13.Wire.Generated.SignatureScheme
module GCS = TLS13.Wire.Generated.CipherSuite
module GCV = TLS13.Wire.Generated.CertificateVerify
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GPN = TLS13.Wire.Generated.ProtocolName
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GNG = TLS13.Wire.Generated.NamedGroup
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GCert = TLS13.Wire.Generated.Certificate
module GCE = TLS13.Wire.Generated.CertificateEntry
module LP = LowParse.Spec

(* --- non-handshake content-type arms ------------------------------------ *)

val byte:
  n:nat ->
  GTot U8.t

val lemma_ptm_change_cipher_spec (fragment:B.bytes)
  : Lemma (ensures WS.parse_tls_message T.ChangeCipherSpec fragment ==
                   (if B.length fragment = 1 && U8.v (Seq.index fragment 0) = 1
                    then Some M.TlsChangeCipherSpec
                    else None))

val lemma_ptm_application_data (fragment:B.bytes)
  : Lemma (ensures WS.parse_tls_message T.ApplicationData fragment ==
                   Some (M.TlsApplicationData fragment))

(* parse_plaintext strips the trailing content-type byte, so the recovered
   fragment is exactly one byte shorter than the decrypted TLSInnerPlaintext. *)
val lemma_parse_plaintext_fragment_len (input:B.bytes)
  : Lemma (ensures (match WS.parse_plaintext input with
                    | Some pt -> B.length pt.M.fragment + 1 == B.length input
                    | None -> True))

val u8:
  n:nat ->
  GTot B.bytes

val u16:
  n:nat ->
  GTot B.bytes

val u24:
  n:nat ->
  GTot B.bytes

val content_type_byte:
  ct:T.content_type ->
  GTot U8.t

val lemma_content_type_byte_value:
  ct:T.content_type ->
  Lemma (match ct with
         | T.ChangeCipherSpec -> U8.v (content_type_byte ct) == 0x14
         | T.Alert -> U8.v (content_type_byte ct) == 0x15
         | T.Handshake -> U8.v (content_type_byte ct) == 0x16
         | T.ApplicationData -> U8.v (content_type_byte ct) == 0x17)

val serialize_record_header:
  content_type:T.content_type ->
  fragment_len:nat ->
  GTot B.bytes

val lemma_serialize_record_reveal:
  content_type:T.content_type ->
  fragment:B.bytes ->
  Lemma (Seq.equal
    (WS.serialize_record content_type fragment)
    (B.append (serialize_record_header content_type (B.length fragment)) fragment))

val lemma_serialize_application_data_header_reveal:
  fragment_len:nat ->
  Lemma (Seq.equal
    (serialize_record_header T.ApplicationData fragment_len)
    (CS.application_data_record_header fragment_len))

val lemma_serialize_handshake_record_header_reveal:
  fragment_len:nat ->
  Lemma (Seq.equal
    (serialize_record_header T.Handshake fragment_len)
    (B.of_list [
      0x16uy; 0x03uy; 0x03uy;
      byte (fragment_len / 256);
      byte fragment_len
    ]))

val lemma_application_data_record_aad:
  fragment:B.bytes{B.length fragment <= 16640} ->
  Lemma (Seq.equal
    (CS.record_header_aad (WS.serialize_record T.ApplicationData fragment))
    (CS.application_data_record_header (B.length fragment)))

val lemma_serialize_application_data_record_reveal:
  fragment:B.bytes ->
  Lemma (Seq.equal
    (WS.serialize_record T.ApplicationData fragment)
    (B.append (CS.application_data_record_header (B.length fragment)) fragment))

val lemma_application_data_record_header:
  fragment_len:nat{fragment_len <= 16640} ->
  Lemma (Seq.equal
    (CS.application_data_record_header fragment_len)
    (serialize_record_header T.ApplicationData fragment_len))

val application_data_record_header_bytes:
  fragment_len:nat ->
  GTot (b:B.bytes{B.length b == 5})

val lemma_application_data_record_header_bytes:
  fragment_len:nat{fragment_len <= 16640} ->
  Lemma (Seq.equal
    (CS.application_data_record_header fragment_len)
    (application_data_record_header_bytes fragment_len))

val lemma_application_data_record_header_bytes_reveal:
  fragment_len:nat ->
  Lemma (Seq.equal
    (application_data_record_header_bytes fragment_len)
    (B.of_list [
      0x17uy;
      0x03uy;
      0x03uy;
      byte (fragment_len / 256);
      byte fragment_len
    ]))

val lemma_serialize_plaintext_reveal:
  pt:M.plaintext ->
  Lemma (Seq.equal
    (WS.serialize_plaintext pt)
    (B.append pt.M.fragment (B.singleton (content_type_byte pt.M.content_type))))

val lemma_plaintext_roundtrip_reveal:
  ct:T.content_type ->
  fragment:B.bytes ->
  Lemma (Seq.equal
           (WS.serialize_plaintext { M.content_type = ct; M.fragment = fragment })
           (B.append fragment (B.singleton (content_type_byte ct))) /\
         WS.parse_plaintext (B.append fragment (B.singleton (content_type_byte ct))) ==
           Some { M.content_type = ct; M.fragment = fragment })

val lemma_serialize_finished_reveal:
  fin:M.finished ->
  Lemma (Seq.equal
    (WS.serialize_handshake (M.Finished fin))
    (B.append (B.of_list [20uy; 0uy; 0uy; 32uy]) fin.M.verify_data))

(* Parse-serialise round trip for Finished: serialising a Finished message and
   then parsing it gives back the original message.  Combined with
   lemma_serialize_finished_reveal this lets callers prove the concrete byte
   array they built is both the right serialisation AND parses correctly. *)
val lemma_parse_finished_handshake:
  fin:M.finished ->
  Lemma (WS.parse_tls_message T.Handshake (WS.serialize_handshake (M.Finished fin)) ==
         Some (M.TlsHandshake (M.Finished fin)))

val lemma_serialize_server_certificate_verify_input_reveal:
  transcript_hash:B.bytes{B.length transcript_hash == 32} ->
  Lemma (Seq.equal
    (WS.serialize_server_certificate_verify_input transcript_hash)
    (TLS13.Handshake.Spec.certificate_verify_input transcript_hash))

val certificate_verify_context_with_zero:
  b:B.bytes{B.length b == 34}

val lemma_certificate_verify_context_with_zero_literal:
  unit ->
  Lemma (Seq.equal
    certificate_verify_context_with_zero
    (B.of_list [
      0x54uy; 0x4cuy; 0x53uy; 0x20uy; 0x31uy; 0x2euy; 0x33uy; 0x2cuy;
      0x20uy; 0x73uy; 0x65uy; 0x72uy; 0x76uy; 0x65uy; 0x72uy; 0x20uy;
      0x43uy; 0x65uy; 0x72uy; 0x74uy; 0x69uy; 0x66uy; 0x69uy; 0x63uy;
      0x61uy; 0x74uy; 0x65uy; 0x56uy; 0x65uy; 0x72uy; 0x69uy; 0x66uy;
      0x79uy; 0uy
    ]))

val certificate_verify_context_byte:
  i:nat{i < 34} ->
  GTot U8.t

val lemma_certificate_verify_context_byte:
  i:nat{i < 34} ->
  Lemma (Seq.index certificate_verify_context_with_zero i ==
         certificate_verify_context_byte i)

val lemma_certificate_verify_context_index_0: unit -> Lemma (Seq.index certificate_verify_context_with_zero 0 == 0x54uy)
val lemma_certificate_verify_context_index_1: unit -> Lemma (Seq.index certificate_verify_context_with_zero 1 == 0x4cuy)
val lemma_certificate_verify_context_index_2: unit -> Lemma (Seq.index certificate_verify_context_with_zero 2 == 0x53uy)
val lemma_certificate_verify_context_index_3: unit -> Lemma (Seq.index certificate_verify_context_with_zero 3 == 0x20uy)
val lemma_certificate_verify_context_index_4: unit -> Lemma (Seq.index certificate_verify_context_with_zero 4 == 0x31uy)
val lemma_certificate_verify_context_index_5: unit -> Lemma (Seq.index certificate_verify_context_with_zero 5 == 0x2euy)
val lemma_certificate_verify_context_index_6: unit -> Lemma (Seq.index certificate_verify_context_with_zero 6 == 0x33uy)
val lemma_certificate_verify_context_index_7: unit -> Lemma (Seq.index certificate_verify_context_with_zero 7 == 0x2cuy)
val lemma_certificate_verify_context_index_8: unit -> Lemma (Seq.index certificate_verify_context_with_zero 8 == 0x20uy)
val lemma_certificate_verify_context_index_9: unit -> Lemma (Seq.index certificate_verify_context_with_zero 9 == 0x73uy)
val lemma_certificate_verify_context_index_10: unit -> Lemma (Seq.index certificate_verify_context_with_zero 10 == 0x65uy)
val lemma_certificate_verify_context_index_11: unit -> Lemma (Seq.index certificate_verify_context_with_zero 11 == 0x72uy)
val lemma_certificate_verify_context_index_12: unit -> Lemma (Seq.index certificate_verify_context_with_zero 12 == 0x76uy)
val lemma_certificate_verify_context_index_13: unit -> Lemma (Seq.index certificate_verify_context_with_zero 13 == 0x65uy)
val lemma_certificate_verify_context_index_14: unit -> Lemma (Seq.index certificate_verify_context_with_zero 14 == 0x72uy)
val lemma_certificate_verify_context_index_15: unit -> Lemma (Seq.index certificate_verify_context_with_zero 15 == 0x20uy)
val lemma_certificate_verify_context_index_16: unit -> Lemma (Seq.index certificate_verify_context_with_zero 16 == 0x43uy)
val lemma_certificate_verify_context_index_17: unit -> Lemma (Seq.index certificate_verify_context_with_zero 17 == 0x65uy)
val lemma_certificate_verify_context_index_18: unit -> Lemma (Seq.index certificate_verify_context_with_zero 18 == 0x72uy)
val lemma_certificate_verify_context_index_19: unit -> Lemma (Seq.index certificate_verify_context_with_zero 19 == 0x74uy)
val lemma_certificate_verify_context_index_20: unit -> Lemma (Seq.index certificate_verify_context_with_zero 20 == 0x69uy)
val lemma_certificate_verify_context_index_21: unit -> Lemma (Seq.index certificate_verify_context_with_zero 21 == 0x66uy)
val lemma_certificate_verify_context_index_22: unit -> Lemma (Seq.index certificate_verify_context_with_zero 22 == 0x69uy)
val lemma_certificate_verify_context_index_23: unit -> Lemma (Seq.index certificate_verify_context_with_zero 23 == 0x63uy)
val lemma_certificate_verify_context_index_24: unit -> Lemma (Seq.index certificate_verify_context_with_zero 24 == 0x61uy)
val lemma_certificate_verify_context_index_25: unit -> Lemma (Seq.index certificate_verify_context_with_zero 25 == 0x74uy)
val lemma_certificate_verify_context_index_26: unit -> Lemma (Seq.index certificate_verify_context_with_zero 26 == 0x65uy)
val lemma_certificate_verify_context_index_27: unit -> Lemma (Seq.index certificate_verify_context_with_zero 27 == 0x56uy)
val lemma_certificate_verify_context_index_28: unit -> Lemma (Seq.index certificate_verify_context_with_zero 28 == 0x65uy)
val lemma_certificate_verify_context_index_29: unit -> Lemma (Seq.index certificate_verify_context_with_zero 29 == 0x72uy)
val lemma_certificate_verify_context_index_30: unit -> Lemma (Seq.index certificate_verify_context_with_zero 30 == 0x69uy)
val lemma_certificate_verify_context_index_31: unit -> Lemma (Seq.index certificate_verify_context_with_zero 31 == 0x66uy)
val lemma_certificate_verify_context_index_32: unit -> Lemma (Seq.index certificate_verify_context_with_zero 32 == 0x79uy)
val lemma_certificate_verify_context_index_33: unit -> Lemma (Seq.index certificate_verify_context_with_zero 33 == 0uy)

val lemma_serialize_server_certificate_verify_input_bytes:
  transcript_hash:B.bytes{B.length transcript_hash == 32} ->
  Lemma (Seq.equal
    (WS.serialize_server_certificate_verify_input transcript_hash)
    (B.append
      (B.append (Seq.create 64 0x20uy) certificate_verify_context_with_zero)
      transcript_hash))

val lemma_serialize_client_hello_reveal:
  hello:M.client_hello ->
  Lemma (Seq.equal
    (WS.serialize_handshake (M.ClientHello hello))
    (B.append
      (B.of_list [1uy])
      (B.append
        (u24 (B.length (WS.serialize_client_hello hello)))
        (WS.serialize_client_hello hello))))

val client_hello_byte:
  n:nat ->
  GTot B.byte

val client_hello_common_extensions_bytes:
  key_share:B.bytes ->
  GTot B.bytes

val client_hello_server_name_extension_bytes:
  hostname:B.bytes ->
  GTot B.bytes

val client_hello_extensions_bytes:
  hostname:B.bytes ->
  key_share:B.bytes ->
  GTot B.bytes

val client_hello_prefix_bytes:
  body_len:nat ->
  extensions_len:nat ->
  random:B.bytes ->
  GTot B.bytes

val client_hello_body_bytes:
  random:B.bytes ->
  hostname:B.bytes ->
  key_share:B.bytes ->
  GTot B.bytes

val client_hello_handshake_bytes:
  random:B.bytes ->
  hostname:B.bytes ->
  key_share:B.bytes ->
  GTot B.bytes

val lemma_client_hello_common_extensions_bytes_reveal:
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (Seq.equal
    (client_hello_common_extensions_bytes key_share)
    (B.append
      (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])
      (B.append
        (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])
        (B.append
          (B.append
            (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
            key_share)
          (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy])))))

val lemma_client_hello_extensions_bytes_shape:
  hostname:B.bytes{B.length hostname <= 255} ->
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (Seq.equal
    (client_hello_extensions_bytes hostname key_share)
    (B.append
      (client_hello_server_name_extension_bytes hostname)
      (client_hello_common_extensions_bytes key_share)))

val lemma_client_hello_server_name_extension_bytes_reveal:
  hostname:B.bytes{0 < B.length hostname /\ B.length hostname <= 255} ->
  Lemma (Seq.equal
    (client_hello_server_name_extension_bytes hostname)
    (B.append
      (B.of_list [
        0uy; 0uy;
        client_hello_byte ((5 + B.length hostname) / 256);
        client_hello_byte (5 + B.length hostname);
        client_hello_byte ((3 + B.length hostname) / 256);
        client_hello_byte (3 + B.length hostname);
        0uy;
        client_hello_byte (B.length hostname / 256);
        client_hello_byte (B.length hostname)])
      hostname))

val lemma_client_hello_server_name_extension_bytes_empty:
  hostname:B.bytes{B.length hostname == 0} ->
  Lemma (Seq.equal (client_hello_server_name_extension_bytes hostname) B.empty)

val lemma_client_hello_prefix_bytes_reveal:
  body_len:nat ->
  extensions_len:nat ->
  random:B.bytes{B.length random == 32} ->
  Lemma (Seq.equal
    (client_hello_prefix_bytes body_len extensions_len random)
    (B.append
      (B.of_list [
        1uy;
        client_hello_byte (body_len / 65536);
        client_hello_byte (body_len / 256);
        client_hello_byte body_len;
        0x03uy; 0x03uy])
      (B.append
        random
        (B.of_list [
          0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
          client_hello_byte (extensions_len / 256);
          client_hello_byte extensions_len]))))

val lemma_client_hello_common_extensions_len:
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (B.length (client_hello_common_extensions_bytes key_share) == 65)

val lemma_client_hello_server_name_extension_len:
  hostname:B.bytes{B.length hostname <= 255} ->
  Lemma (B.length (client_hello_server_name_extension_bytes hostname) ==
    (if B.length hostname == 0 then 0 else 9 + B.length hostname))

val lemma_client_hello_extensions_len:
  hostname:B.bytes{B.length hostname <= 255} ->
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (B.length (client_hello_extensions_bytes hostname key_share) ==
    65 + (if B.length hostname == 0 then 0 else 9 + B.length hostname))

val lemma_client_hello_handshake_bytes_prefix:
  random:B.bytes{B.length random == 32} ->
  hostname:B.bytes{B.length hostname <= 255} ->
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (Seq.equal
    (client_hello_handshake_bytes random hostname key_share)
    (B.append
      (client_hello_prefix_bytes
        (43 + B.length (client_hello_extensions_bytes hostname key_share))
        (B.length (client_hello_extensions_bytes hostname key_share))
        random)
      (client_hello_extensions_bytes hostname key_share)))

val lemma_client_hello_handshake_bytes_reveal:
  hello:M.client_hello{B.length hello.M.random == 32 /\
                       B.length hello.M.key_share == 32 /\
                       (match hello.M.server_name with
                        | Some h -> B.length h <= 255
                        | None -> True)} ->
  Lemma (Seq.equal
    (WS.serialize_handshake (M.ClientHello hello))
    (client_hello_handshake_bytes
      hello.M.random
      (match hello.M.server_name with
       | Some h -> h
       | None -> B.empty)
      hello.M.key_share))

val lemma_ptm_alert (fragment:B.bytes)
  : Lemma (ensures (
      if B.length fragment == 2
      then
        WS.parse_tls_message T.Alert fragment ==
          (match U8.v (Seq.index fragment 1) with
           | 0   -> Some (M.TlsAlert T.CloseNotify)
           | 10  -> Some (M.TlsAlert T.UnexpectedMessage)
           | 20  -> Some (M.TlsAlert T.BadRecordMac)
           | 40  -> Some (M.TlsAlert T.HandshakeFailure)
           | 46  -> Some (M.TlsAlert T.CertificateUnknown)
           | 47  -> Some (M.TlsAlert T.IllegalParameter)
           | 50  -> Some (M.TlsAlert T.DecodeError)
           | 51  -> Some (M.TlsAlert T.DecryptError)
           | 70  -> Some (M.TlsAlert T.ProtocolVersion)
           | 110 -> Some (M.TlsAlert T.UnsupportedExtension)
           | _   -> None)
      else WS.parse_tls_message T.Alert fragment == None))

(* --- handshake arm: connect the QD parser to parse_tls_message ---------- *)

(* Re-export of the internal [synth_handshake_msg_of]. *)
inline_for_extraction
let handshake_synth (h:GHS.handshake) : GTot (option M.handshake_msg) =
  WS.synth_handshake_msg_of h

(* Re-export of the internal cipher-suite / signature-scheme synths so the
   implementation can name the high-level field values. *)
inline_for_extraction
let synth_cipher_suite (c:GCS.cipherSuite) : GTot T.cipher_suite =
  WS.synth_cipher_suite c

inline_for_extraction
let synth_signature_scheme (s:GSS.signatureScheme) : GTot T.signature_scheme =
  WS.synth_signature_scheme s

(* The signature-scheme synth maps the generated enum to the abstract type
   per-constructor; exposed so the implementation can pick a matching wire u16. *)
val lemma_synth_signature_scheme (s:GSS.signatureScheme)
  : Lemma (ensures synth_signature_scheme s ==
                   (match s with
                    | GSS.Ecdsa_secp256r1_sha256 -> T.EcdsaSecp256r1Sha256
                    | GSS.Rsa_pss_rsae_sha256 -> T.RsaPssRsaeSha256
                    | GSS.Ed25519 -> T.Ed25519
                    | GSS.Unknown_signatureScheme v -> T.UnsupportedSignatureScheme (U16.v v)))

(* If the generated handshake parser yields [v] consuming the whole fragment
   and [handshake_synth v == Some m], then [parse_tls_message] of a Handshake
   record produces exactly [TlsHandshake m]. *)
val lemma_ptm_handshake_some (fragment:B.bytes) (v:GHS.handshake) (m:M.handshake_msg)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, B.length fragment) /\
              handshake_synth v == Some m)
    (ensures WS.parse_tls_message T.Handshake fragment == Some (M.TlsHandshake m))

(* Per-constructor reveals of [handshake_synth]. *)

val lemma_handshake_synth_finished (b:GHS.handshake_body_finished)
  : Lemma (ensures handshake_synth (GHS.Body_finished b) ==
                   Some (M.Finished ({ M.verify_data = (b <: B.bytes_of_len 32) })))

(* CertificateVerify: the synth is guarded by the 4096-byte signature bound.
   When the wire signature fits, the M value carries the verbatim wire body
   (the serialization of the parsed handshake value). *)
val lemma_handshake_synth_certificate_verify (b:GHS.handshake_body_certificate_verify)
  : Lemma (ensures handshake_synth (GHS.Body_certificate_verify b) ==
                   (if B.length (b.GCV.signature <: B.bytes) <= M.signature_max_len
                    then Some (M.CertificateVerify ({
                           M.scheme = synth_signature_scheme b.GCV.algorithm;
                           M.signature = (b.GCV.signature <: B.bytes);
                           M.body = LP.serialize GHS.handshake_serializer (GHS.Body_certificate_verify b) }))
                    else None))

(* Key_update handshake values never synth to a handshake message: the spec
   routes them through the byte-level [parse_key_update] fallback instead. *)
val lemma_handshake_synth_key_update (b:GHS.handshake_body_key_update)
  : Lemma (ensures handshake_synth (GHS.Body_key_update b) == None)

(* A client never legitimately receives a ClientHello; synth maps it to None. *)
val lemma_handshake_synth_client_hello (b:GHS.handshake_body_client_hello)
  : Lemma (ensures handshake_synth (GHS.Body_client_hello b) == None)(* --- byte-level fallback formats (outside the QD handshake grammar) ------ *)

(* Re-export of the internal [parse_ignored_post_handshake] (not in the frozen
   TLS13.Wire.Spec interface). *)
let reveal_parse_ignored_post_handshake (input:B.bytes) : GTot (option B.bytes) =
  WS.parse_ignored_post_handshake input

(* Byte-level definition of [parse_key_update]: a 5-byte [24;0;0;1;req] envelope. *)
val lemma_parse_key_update_def (input:B.bytes)
  : Lemma (ensures WS.parse_key_update input ==
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

(* Byte-level definition of [parse_ignored_post_handshake]: a msg_type-4 envelope
   with a 3-byte length field. *)
val lemma_parse_ignored_post_handshake_def (input:B.bytes)
  : Lemma (ensures WS.parse_ignored_post_handshake input ==
      (if B.length input >= 4 &&
          U8.v (Seq.index input 0) = 4 &&
          (U8.v (Seq.index input 1) * 65536 +
           U8.v (Seq.index input 2) * 256 +
           U8.v (Seq.index input 3)) + 4 = B.length input
       then Some (Seq.slice input 4 (B.length input))
       else None))

(* --- handshake-arm routing into the byte-level fallbacks ----------------- *)

(* If the QD handshake parser does not parse [fragment], then [parse_handshake]
   fails too. *)
val lemma_parse_handshake_none_of_lp_none (fragment:B.bytes)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == None)
    (ensures WS.parse_handshake fragment == None)

(* If the QD handshake parser yields [v] but [handshake_synth v == None], then
   [parse_handshake] fails. *)
val lemma_parse_handshake_none_of_synth_none (fragment:B.bytes) (v:GHS.handshake) (consumed:LP.consumed_length fragment)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, consumed) /\
              handshake_synth v == None)
    (ensures WS.parse_handshake fragment == None)

(* When [parse_handshake] fails, [parse_tls_message] of a Handshake record is the
   byte-level key_update / ignored-post-handshake fallback. *)
val lemma_ptm_handshake_fallback (fragment:B.bytes)
  : Lemma
    (requires WS.parse_handshake fragment == None)
    (ensures WS.parse_tls_message T.Handshake fragment ==
      (match WS.parse_key_update fragment with
       | Some req -> Some (M.TlsKeyUpdate req)
       | None ->
         (match WS.parse_ignored_post_handshake fragment with
          | Some body -> Some (M.TlsIgnoredPostHandshake body)
          | None -> None)))

(* If the QD handshake parser succeeds but does not consume the whole fragment,
   then [parse_tls_message] of a Handshake record is None. The proof routes
   through [TLS13.Wire.Spec.NonExact] (which friends the generated handshake
   grammar to expose the message-type tag byte). *)

(* --- EncryptedExtensions: per-constructor synth reveals ----------------- *)

(* Re-export of the internal [synth_encrypted_extensions] (scan for the first
   ALPN extension). *)
let reveal_synth_encrypted_extensions (l:list GEEE.extensionEncryptedExtensions)
  : GTot (option M.encrypted_extensions) =
  WS.synth_encrypted_extensions l

(* Re-export of the internal [alpn_first_name] (first protocol name of an ALPN
   extension, as raw bytes). *)
let reveal_alpn_first_name
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  : GTot (option B.bytes) =
  WS.alpn_first_name pnl

(* The EncryptedExtensions arm of [synth_handshake_msg_of]: when the extension
   list synthesises an [encrypted_extensions], the carried M value's body is
   overridden with the verbatim wire bytes of the parsed handshake value. *)
val lemma_handshake_synth_encrypted_extensions (b:GHS.handshake_body_encrypted_extensions)
  : Lemma (ensures handshake_synth (GHS.Body_encrypted_extensions b) ==
                   (match reveal_synth_encrypted_extensions b with
                    | Some x -> Some (M.EncryptedExtensions ({ x with
                        M.body = LP.serialize GHS.handshake_serializer (GHS.Body_encrypted_extensions b) }))
                    | None -> None))

(* The empty extension list synthesises an EncryptedExtensions with no ALPN. *)
val lemma_synth_ee_nil (_:unit)
  : Lemma (ensures reveal_synth_encrypted_extensions []
                   == Some ({ M.negotiated_alpn = None; M.body = TLS13.Bytes.empty }))

(* A non-ALPN head extension is skipped: the synth of the whole list equals the
   synth of the tail. *)
val lemma_synth_ee_cons_non_alpn
  (e:GEEE.extensionEncryptedExtensions)
  (tl:list GEEE.extensionEncryptedExtensions)
  : Lemma
    (requires not (GEEE.Extension_data_application_layer_protocol_negotiation? e))
    (ensures reveal_synth_encrypted_extensions (e :: tl)
             == reveal_synth_encrypted_extensions tl)

(* An ALPN head extension fixes the result to the first protocol name. *)
val lemma_synth_ee_cons_alpn
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  (tl:list GEEE.extensionEncryptedExtensions)
  : Lemma
    (ensures reveal_synth_encrypted_extensions
               (GEEE.Extension_data_application_layer_protocol_negotiation pnl :: tl)
             == (match reveal_alpn_first_name pnl with
                 | Some name -> Some ({ M.negotiated_alpn = Some name; M.body = TLS13.Bytes.empty })
                 | None -> None))

(* --- Pure list-suffix helpers for the EncryptedExtensions scan loop ------- *)

(* The [i]-th suffix of a list (a local [drop]: FStar.List.Tot has none). *)
val list_drop:
  #a:Type ->
  n:nat ->
  l:list a ->
  Tot (list a)

(* Stepping the suffix exposes the head element at index [i]. *)
val lemma_list_drop_index (#a:Type) (l:list a) (i:nat)
  : Lemma (requires i < FStar.List.Tot.length l)
          (ensures list_drop i l == FStar.List.Tot.index l i :: list_drop (i + 1) l)

(* Dropping the whole length leaves the empty list. *)
val lemma_list_drop_length (#a:Type) (l:list a)
  : Lemma (ensures list_drop (FStar.List.Tot.length l) l == [])

(* The first protocol name of a non-empty list is its head element's bytes. *)
val lemma_alpn_first_name_index0
  (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  : Lemma
    (requires FStar.List.Tot.length (pnl <: list GPN.protocolName) > 0)
    (ensures reveal_alpn_first_name pnl ==
             Some (FStar.List.Tot.index (pnl <: list GPN.protocolName) 0 <: B.bytes))

(* --- ServerHello reveal interface --------------------------------------- *)

(* Re-export of the internal [key_exchange_to_key32]: a key_share entry yields a
   32-byte key only when its raw bytes are exactly 32 long. *)
val reveal_key_exchange_to_key32 (ke:GKSE.keyShareEntry_key_exchange)
  : GTot (option (B.bytes_of_len 32))

(* Definitional unfolding of [reveal_key_exchange_to_key32]: a key_share entry
   yields [Some] (the raw bytes) exactly when those bytes are 32 long. *)
val lemma_reveal_key_exchange_to_key32 (ke:GKSE.keyShareEntry_key_exchange)
  : Lemma (ensures reveal_key_exchange_to_key32 ke ==
                   (if B.length (ke <: B.bytes) = 32
                    then Some ((ke <: B.bytes) <: B.bytes_of_len 32)
                    else None))

(* Re-export of the internal [sh_key_share] scan: walk the ServerHello extension
   list, requiring an x25519/32-byte key_share AND a TLS_1p3 supported_versions. *)
val reveal_sh_key_share
  (l:list GESH.extensionServerHello)
  (saw_supported_versions:bool)
  (key_share:option (B.bytes_of_len 32))
  : GTot (option (B.bytes_of_len 32))

(* Empty extension list: the key is accepted only if a TLS_1p3 supported_versions
   extension was seen. *)
val lemma_sh_key_share_nil
  (saw_supported_versions:bool)
  (key_share:option (B.bytes_of_len 32))
  : Lemma (ensures reveal_sh_key_share [] saw_supported_versions key_share ==
                   (if saw_supported_versions then key_share else None))

(* One-step unfolding of the scan on a head extension. *)
val lemma_sh_key_share_cons
  (e:GESH.extensionServerHello)
  (tl:list GESH.extensionServerHello)
  (saw_supported_versions:bool)
  (key_share:option (B.bytes_of_len 32))
  : Lemma (ensures reveal_sh_key_share (e :: tl) saw_supported_versions key_share ==
      (match e with
       | GESH.Extension_data_supported_versions sv ->
         if GPV.TLS_1p3? sv then reveal_sh_key_share tl true key_share else None
       | GESH.Extension_data_key_share kse ->
         if GNG.X25519? kse.GKSE.group
         then (match reveal_key_exchange_to_key32 kse.GKSE.key_exchange with
               | Some k -> reveal_sh_key_share tl saw_supported_versions (Some k)
               | None -> None)
         else None
       | _ -> reveal_sh_key_share tl saw_supported_versions key_share))

(* [handshake_synth] of a ServerHello whose legacy_version is not 0x0303: None. *)
val lemma_handshake_synth_server_hello_bad_version (b:GHS.handshake_body_server_hello)
  : Lemma (requires not (GPV.TLS_1p2? b.GSH.legacy_version))
          (ensures handshake_synth (GHS.Body_server_hello b) == None)

(* [handshake_synth] of a HelloRetryRequest ServerHello (magic random) maps to
   the dedicated [M.HelloRetryRequest] message. *)
val lemma_handshake_synth_server_hello_hrr
  (b:GHS.handshake_body_server_hello)
  (shb:GSHBody.serverHelloBody)
  : Lemma (requires GPV.TLS_1p2? b.GSH.legacy_version /\
                    b.GSH.body == GSHB.HelloRetryRequest shb)
          (ensures handshake_synth (GHS.Body_server_hello b) == Some M.HelloRetryRequest)

(* [handshake_synth] of a normal ServerHello: guarded by compression==0, the
   key_share scan, and the server_hello_max_len body bound; the carried body is
   the verbatim wire serialization. *)
val lemma_handshake_synth_server_hello_sh
  (b:GHS.handshake_body_server_hello)
  (sf:GSHB.serverHello_body_false)
  : Lemma (requires GPV.TLS_1p2? b.GSH.legacy_version /\
                    b.GSH.body == GSHB.ServerHello_body_false sf)
          (ensures handshake_synth (GHS.Body_server_hello b) ==
      (if U8.v sf.GSHB.value.GSHBody.legacy_compression_method <> 0 then None
       else match reveal_sh_key_share sf.GSHB.value.GSHBody.extensions false None with
            | Some ks ->
              if B.length (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello b))
                 <= M.server_hello_max_len
              then Some (M.ServerHello ({
                     M.random = (sf.GSHB.tag <: B.bytes_of_len 32);
                     M.key_share = ks;
                     M.cipher_suite = synth_cipher_suite sf.GSHB.value.GSHBody.cipher_suite;
                     M.body = LP.serialize GHS.handshake_serializer (GHS.Body_server_hello b) }))
              else None
            | None -> None))

(* --- Certificate: per-constructor synth reveals ------------------------- *)

(* Re-export of the internal [synth_cert_chain]: the list of [cert_data] DER
   blobs from a certificate_list. *)
val reveal_synth_cert_chain (l:list GCE.certificateEntry)
  : GTot (list B.bytes)

(* Re-export of the internal [cert_chain_total_bytes]: the total length of all
   the [cert_data] blobs in a chain. *)
val reveal_cert_chain_total_bytes (chain:list B.bytes)
  : GTot nat

(* [synth_cert_chain] of the empty list is empty. *)
val lemma_synth_cert_chain_nil (_:unit)
  : Lemma (ensures reveal_synth_cert_chain [] == [])

(* One-step unfolding of [synth_cert_chain] on a head entry: the head's
   [cert_data] is prepended to the synth of the tail. *)
val lemma_synth_cert_chain_cons (e:GCE.certificateEntry) (tl:list GCE.certificateEntry)
  : Lemma (ensures reveal_synth_cert_chain (e :: tl) ==
                   (e.GCE.cert_data <: B.bytes) :: reveal_synth_cert_chain tl)

(* [synth_cert_chain] preserves list length (it is a map). *)
val lemma_synth_cert_chain_length (l:list GCE.certificateEntry)
  : Lemma (ensures FStar.List.Tot.length (reveal_synth_cert_chain l) ==
                   FStar.List.Tot.length l)

(* [cert_chain_total_bytes] of the empty chain is zero. *)
val lemma_cert_chain_total_bytes_nil (_:unit)
  : Lemma (ensures reveal_cert_chain_total_bytes [] == 0)

(* Appending one blob at the back adds its length to the total. *)
val lemma_cert_chain_total_bytes_snoc (chain:list B.bytes) (x:B.bytes)
  : Lemma (ensures reveal_cert_chain_total_bytes (FStar.List.Tot.append chain [x]) ==
                   reveal_cert_chain_total_bytes chain + B.length x)

(* The total bytes of a chain dominate the prefix total plus the next blob. *)
val lemma_cert_chain_total_bytes_prefix_le
  (prefix:list B.bytes) (x:B.bytes) (rest:list B.bytes)
  : Lemma (ensures reveal_cert_chain_total_bytes prefix + B.length x <=
                   reveal_cert_chain_total_bytes
                     (FStar.List.Tot.append prefix (x :: rest)))

(* The Certificate arm of [synth_handshake_msg_of]: when the synthesised chain
   fits the fixed-size low-level representation (<= certificate_chain_max_entries
   entries and <= certificate_chain_max_bytes total cert bytes) it yields an
   [M.Certificate] whose body is the verbatim wire serialization; otherwise the
   message is rejected ([None]). *)
val lemma_handshake_synth_certificate (b:GHS.handshake_body_certificate)
  : Lemma (ensures handshake_synth (GHS.Body_certificate b) ==
            (let chain = reveal_synth_cert_chain
                           (b.GCert.certificate_list <: list GCE.certificateEntry) in
             if FStar.List.Tot.length chain <= M.certificate_chain_max_entries &&
                reveal_cert_chain_total_bytes chain <= M.certificate_chain_max_bytes
             then Some (M.Certificate ({ M.chain = chain;
                    M.body = LP.serialize GHS.handshake_serializer (GHS.Body_certificate b) }))
             else None))
