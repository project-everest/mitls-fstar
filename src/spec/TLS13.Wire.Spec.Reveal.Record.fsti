module TLS13.Wire.Spec.Reveal.Record

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

val byte: n:nat -> GTot U8.t

val lemma_byte_value:
  n:nat ->
  Lemma (U8.v (byte n) == n % 256)

val lemma_ptm_change_cipher_spec:
  fragment:B.bytes ->
  Lemma (ensures WS.parse_tls_message T.Change_cipher_spec fragment ==
    (if B.length fragment = 1 && U8.v (Seq.index fragment 0) = 1
     then Some M.TlsChangeCipherSpec
     else None))

val lemma_ptm_application_data:
  fragment:B.bytes ->
  Lemma (ensures WS.parse_tls_message T.Application_data fragment ==
    Some (M.TlsApplicationData fragment))

val lemma_parse_plaintext_fragment_len:
  input:B.bytes ->
  Lemma (ensures (match WS.parse_plaintext input with
                  | Some pt -> B.length pt.M.fragment + 1 == B.length input
                  | None -> True))

val u8: n:nat -> GTot B.bytes
val u16: n:nat -> GTot B.bytes
val u24: n:nat -> GTot B.bytes

val content_type_byte:
  ct:T.content_type ->
  GTot U8.t

val lemma_content_type_byte_value:
  ct:T.content_type ->
  Lemma (match ct with
         | T.Invalid -> U8.v (content_type_byte ct) == 0x00
         | T.Change_cipher_spec -> U8.v (content_type_byte ct) == 0x14
         | T.Alert -> U8.v (content_type_byte ct) == 0x15
         | T.Handshake -> U8.v (content_type_byte ct) == 0x16
         | T.Application_data -> U8.v (content_type_byte ct) == 0x17)

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
    (serialize_record_header T.Application_data fragment_len)
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
    (CS.record_header_aad (WS.serialize_record T.Application_data fragment))
    (CS.application_data_record_header (B.length fragment)))

val lemma_serialize_application_data_record_reveal:
  fragment:B.bytes ->
  Lemma (Seq.equal
    (WS.serialize_record T.Application_data fragment)
    (B.append (CS.application_data_record_header (B.length fragment)) fragment))

val lemma_application_data_record_header:
  fragment_len:nat{fragment_len <= 16640} ->
  Lemma (Seq.equal
    (CS.application_data_record_header fragment_len)
    (serialize_record_header T.Application_data fragment_len))

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

val lemma_parse_application_data_record_header_bytes:
  fragment_len:nat{fragment_len <= 16640} ->
  Lemma (WS.parse_record_header (application_data_record_header_bytes fragment_len) ==
         Some (T.Application_data, fragment_len))

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
