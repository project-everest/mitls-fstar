module TLS13.Wire.Spec.Reveal.Util

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

val byte:
  n:nat ->
  GTot (b:U8.t{U8.v b == n % 256})

val u8: n:nat -> GTot B.bytes
val u16: n:nat -> GTot B.bytes
val u24: n:nat -> GTot B.bytes

val content_type_byte: ct:T.content_type -> GTot U8.t

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
  GTot (header:B.bytes{
    B.length header == 5 /\
    Seq.equal header
      (B.append
        (B.singleton (content_type_byte content_type))
        (B.append (u16 0x0303) (u16 fragment_len)))})

val lemma_slice_append_left:
  #a:eqtype ->
  prefix:Seq.seq a ->
  suffix:Seq.seq a ->
  Lemma (ensures Seq.equal (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) prefix)

val lemma_singleton_of_list:
  b:U8.t ->
  Lemma (Seq.equal (B.singleton b) (B.of_list [b]))

val lemma_of_list_append:
  l1:list U8.t ->
  l2:list U8.t ->
  Lemma (ensures Seq.equal (Seq.append (B.of_list l1) (B.of_list l2))
                             (B.of_list (l1 `FStar.List.Tot.append` l2)))

val lemma_olcons:
  a:list U8.t ->
  b:list U8.t ->
  s:Seq.seq U8.t ->
  Lemma (Seq.equal (Seq.append (B.of_list a) (Seq.append (B.of_list b) s))
                   (Seq.append (B.of_list (FStar.List.Tot.append a b)) s))

val lemma_byte_0: unit -> Lemma (byte 0 == 0uy)
val lemma_byte_1: unit -> Lemma (byte 1 == 1uy)
val lemma_byte_3: unit -> Lemma (byte 3 == 0x03uy)
val lemma_byte_20: unit -> Lemma (byte 20 == 20uy)
val lemma_byte_32: unit -> Lemma (byte 32 == 32uy)
val lemma_byte_0303_lo: unit -> Lemma (byte 0x0303 == 0x03uy)

val lemma_content_type_change_cipher_spec_byte:
  unit -> Lemma (content_type_byte T.Change_cipher_spec == 0x14uy)

val lemma_content_type_alert_byte:
  unit -> Lemma (content_type_byte T.Alert == 0x15uy)

val lemma_content_type_handshake_byte:
  unit -> Lemma (content_type_byte T.Handshake == 0x16uy)

val lemma_content_type_application_data_byte:
  unit -> Lemma (content_type_byte T.Application_data == 0x17uy)

val lemma_u8_reveal:
  n:nat ->
  Lemma (Seq.equal (u8 n) (B.singleton (byte n)))

val lemma_u16_reveal:
  n:nat ->
  Lemma (Seq.equal (u16 n) (B.of_list [byte (n / 256); byte n]))

val lemma_u24_reveal:
  n:nat ->
  Lemma (Seq.equal (u24 n) (B.of_list [byte (n / 65536); byte (n / 256); byte n]))

val lemma_u16_of_bytes:
  hi:U8.t ->
  lo:U8.t ->
  Lemma (Seq.equal
    (u16 (U8.v hi * 256 + U8.v lo))
    (B.of_list [hi; lo]))

val lemma_serialize_record_reveal:
  content_type:T.content_type ->
  fragment:B.bytes{B.length fragment <= 16640} ->
  Lemma (Seq.equal
    (WS.serialize_record content_type fragment)
    (B.append
      (serialize_record_header content_type (B.length fragment))
      fragment))

val lemma_serialize_record_head:
  content_type:T.content_type ->
  fragment:B.bytes{B.length fragment <= 16640} ->
  Lemma (ensures
    B.length (WS.serialize_record content_type fragment) > 0 /\
    Seq.index (WS.serialize_record content_type fragment) 0 ==
      content_type_byte content_type)

val lemma_serialize_record_legacy_version:
  content_type:T.content_type ->
  fragment:B.bytes{B.length fragment <= 16640} ->
  Lemma (ensures
    B.length (WS.serialize_record content_type fragment) >= 3 /\
    Seq.index (WS.serialize_record content_type fragment) 1 == 0x03uy /\
    Seq.index (WS.serialize_record content_type fragment) 2 == 0x03uy)

val lemma_serialize_record_fragment_length:
  content_type:T.content_type ->
  fragment:B.bytes{B.length fragment <= 16640} ->
  Lemma
    (requires
      B.length (WS.serialize_record content_type fragment) >= 5)
    (ensures
      WS.read_u16 (WS.serialize_record content_type fragment) 3 ==
        B.length fragment)

val lemma_serialize_record_prefix_from_header:
  raw:B.bytes ->
  content_type:T.content_type ->
  fragment_len:nat ->
  Lemma
    (requires
      fragment_len <= 16640 /\
      5 + fragment_len <= B.length raw /\
      Seq.index raw 0 == content_type_byte content_type /\
      Seq.index raw 1 == 0x03uy /\
      Seq.index raw 2 == 0x03uy /\
      U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) ==
        fragment_len)
    (ensures Seq.equal
      (WS.serialize_record
        content_type
        (Seq.slice raw 5 (5 + fragment_len)))
      (Seq.slice raw 0 (5 + fragment_len)))
