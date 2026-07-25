module TLS13.Wire.Spec.Reveal.Util

friend TLS13.Wire.Generated.ContentType
friend TLS13.Wire.Generated.ProtocolVersion
friend TLS13.Wire.Generated.TLSCiphertext_encrypted_record
friend TLS13.Wire.Generated.TLSCiphertext
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module E = FStar.Endianness
module GCT = TLS13.Wire.Generated.ContentType
module GCTX = TLS13.Wire.Generated.TLSCiphertext
module GCTXF = TLS13.Wire.Generated.TLSCiphertext_encrypted_record
module GPV = TLS13.Wire.Generated.ProtocolVersion
module LP = LowParse.Spec
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module T = TLS13.Types
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

let byte n = WS.byte n

let u8 n = WS.u8 n

let u16 n = WS.u16 n

let u24 n = WS.u24 n

let content_type_byte ct = WS.byte (WS.content_type_to_byte ct)

let lemma_content_type_byte_value ct =
  match ct with
  | T.Invalid -> WS.lemma_byte_v 0
  | T.Change_cipher_spec -> WS.lemma_byte_v 20
  | T.Alert -> WS.lemma_byte_v 21
  | T.Handshake -> WS.lemma_byte_v 22
  | T.Application_data -> WS.lemma_byte_v 23

let serialize_record_header content_type fragment_len =
  B.append
    (u8 (WS.content_type_to_byte content_type))
    (B.append (u16 0x0303) (u16 fragment_len))

#push-options "--fuel 8 --ifuel 2 --z3rlimit 80"
let lemma_slice_append_left (#a:eqtype) (prefix:Seq.seq a) (suffix:Seq.seq a)
  : Lemma (ensures Seq.equal (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) prefix)
=
  Seq.lemma_len_append prefix suffix;
  Seq.lemma_len_slice (Seq.append prefix suffix) 0 (Seq.length prefix);
  assert (forall (i:nat{i < Seq.length prefix}).
    Seq.index (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) i ==
    Seq.index prefix i);
  Seq.lemma_eq_intro (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) prefix
#pop-options

let lemma_singleton_of_list (b:U8.t)
  : Lemma (Seq.equal (B.singleton b) (B.of_list [b]))
=
  Seq.lemma_seq_of_list_induction [b]

let rec lemma_of_list_append (l1 l2: list U8.t)
  : Lemma (ensures Seq.equal (Seq.append (B.of_list l1) (B.of_list l2))
                             (B.of_list (l1 `FStar.List.Tot.append` l2)))
          (decreases l1)
=
  match l1 with
  | [] ->
    Seq.lemma_seq_of_list_induction ([] <: list U8.t);
    Seq.append_empty_l (B.of_list l2)
  | hd :: tl ->
    lemma_of_list_append tl l2;
    Seq.lemma_seq_of_list_induction (hd :: (tl `FStar.List.Tot.append` l2));
    Seq.lemma_seq_of_list_induction (hd :: tl);
    Seq.append_assoc (Seq.create 1 hd) (B.of_list tl) (B.of_list l2)

let lemma_olcons (a b: list U8.t) (s: Seq.seq U8.t)
  : Lemma (Seq.equal (Seq.append (B.of_list a) (Seq.append (B.of_list b) s))
                     (Seq.append (B.of_list (FStar.List.Tot.append a b)) s))
=
  lemma_of_list_append a b;
  Seq.append_assoc (B.of_list a) (B.of_list b) s

let lemma_byte_0 () =
  WS.lemma_byte_v 0;
  assert_norm (U8.v 0uy == 0);
  assert (U8.v (WS.byte 0) == U8.v 0uy);
  U8.v_inj (WS.byte 0) 0uy

let lemma_byte_1 () =
  WS.lemma_byte_v 1;
  assert_norm (U8.v 1uy == 1);
  assert (U8.v (WS.byte 1) == U8.v 1uy);
  U8.v_inj (WS.byte 1) 1uy

let lemma_byte_3 () =
  WS.lemma_byte_v 3;
  assert_norm (U8.v 0x03uy == 3);
  assert (U8.v (WS.byte 3) == U8.v 0x03uy);
  U8.v_inj (WS.byte 3) 0x03uy

let lemma_byte_20 () =
  WS.lemma_byte_v 20;
  assert_norm (U8.v 20uy == 20);
  assert (U8.v (WS.byte 20) == U8.v 20uy);
  U8.v_inj (WS.byte 20) 20uy

let lemma_byte_32 () =
  WS.lemma_byte_v 32;
  assert_norm (U8.v 32uy == 32);
  assert (U8.v (WS.byte 32) == U8.v 32uy);
  U8.v_inj (WS.byte 32) 32uy

let lemma_byte_0303_lo () =
  WS.lemma_byte_v 0x0303;
  assert_norm (0x0303 % 256 == 3);
  assert_norm (U8.v 0x03uy == 3);
  assert (U8.v (WS.byte 0x0303) == U8.v 0x03uy);
  U8.v_inj (WS.byte 0x0303) 0x03uy

let lemma_content_type_change_cipher_spec_byte () =
  lemma_content_type_byte_value T.Change_cipher_spec;
  assert_norm (U8.v 0x14uy == 20);
  assert (U8.v (content_type_byte T.Change_cipher_spec) == U8.v 0x14uy);
  U8.v_inj (content_type_byte T.Change_cipher_spec) 0x14uy

let lemma_content_type_alert_byte () =
  lemma_content_type_byte_value T.Alert;
  assert_norm (U8.v 0x15uy == 21);
  assert (U8.v (content_type_byte T.Alert) == U8.v 0x15uy);
  U8.v_inj (content_type_byte T.Alert) 0x15uy

let lemma_content_type_handshake_byte () =
  lemma_content_type_byte_value T.Handshake;
  assert_norm (U8.v 0x16uy == 22);
  assert (U8.v (content_type_byte T.Handshake) == U8.v 0x16uy);
  U8.v_inj (content_type_byte T.Handshake) 0x16uy

let lemma_content_type_application_data_byte () =
  lemma_content_type_byte_value T.Application_data;
  assert_norm (U8.v 0x17uy == 23);
  assert (U8.v (content_type_byte T.Application_data) == U8.v 0x17uy);
  U8.v_inj (content_type_byte T.Application_data) 0x17uy

let lemma_u8_reveal (n:nat)
  : Lemma (Seq.equal (u8 n) (B.singleton (byte n)))
= ()

let lemma_u16_reveal (n:nat)
  : Lemma (Seq.equal (u16 n) (B.of_list [byte (n / 256); byte n]))
= ()

let lemma_u24_reveal (n:nat)
  : Lemma (Seq.equal (u24 n) (B.of_list [byte (n / 65536); byte (n / 256); byte n]))
= ()

let lemma_u16_n_to_be (n:nat{n < 65536})
  : Lemma (Seq.equal (E.n_to_be 2 n) (u16 n))
=
  lemma_u16_reveal n;
  WS.lemma_byte_v n;
  WS.lemma_byte_v (n / 256);
  assert (B.length (u16 n) == 2);
  E.reveal_be_to_n (u16 n);
  E.reveal_be_to_n (Seq.slice (u16 n) 0 1);
  E.reveal_be_to_n (Seq.slice (Seq.slice (u16 n) 0 1) 0 0);
  assert (E.be_to_n (u16 n) == n);
  E.be_to_n_inj (E.n_to_be 2 n) (u16 n)

let lemma_u16_of_bytes (hi lo:U8.t)
  : Lemma (Seq.equal
      (u16 (U8.v hi * 256 + U8.v lo))
      (B.of_list [hi; lo]))
=
  let n = U8.v hi * 256 + U8.v lo in
  let bs = B.of_list [hi; lo] in
  lemma_u16_n_to_be n;
  E.reveal_be_to_n bs;
  assert (B.length bs == 2);
  assert (E.be_to_n bs == n);
  E.be_to_n_inj (E.n_to_be 2 n) bs

let lemma_content_type_repr (content_type:T.content_type)
  : Lemma (
      LP.enum_repr_of_key GCT.contentType_enum content_type ==
      content_type_byte content_type)
=
  lemma_content_type_byte_value content_type;
  match content_type with
  | T.Invalid ->
    assert_norm (
      U8.v (LP.enum_repr_of_key GCT.contentType_enum T.Invalid) == 0);
    U8.v_inj
      (LP.enum_repr_of_key GCT.contentType_enum T.Invalid)
      (content_type_byte T.Invalid)
  | T.Change_cipher_spec ->
    assert_norm (
      U8.v (LP.enum_repr_of_key
        GCT.contentType_enum T.Change_cipher_spec) == 20);
    U8.v_inj
      (LP.enum_repr_of_key GCT.contentType_enum T.Change_cipher_spec)
      (content_type_byte T.Change_cipher_spec)
  | T.Alert ->
    assert_norm (
      U8.v (LP.enum_repr_of_key GCT.contentType_enum T.Alert) == 21);
    U8.v_inj
      (LP.enum_repr_of_key GCT.contentType_enum T.Alert)
      (content_type_byte T.Alert)
  | T.Handshake ->
    assert_norm (
      U8.v (LP.enum_repr_of_key GCT.contentType_enum T.Handshake) == 22);
    U8.v_inj
      (LP.enum_repr_of_key GCT.contentType_enum T.Handshake)
      (content_type_byte T.Handshake)
  | T.Application_data ->
    assert_norm (
      U8.v (LP.enum_repr_of_key
        GCT.contentType_enum T.Application_data) == 23);
    U8.v_inj
      (LP.enum_repr_of_key GCT.contentType_enum T.Application_data)
      (content_type_byte T.Application_data)

#push-options "--fuel 8 --ifuel 2 --z3rlimit 20"
let lemma_serialize_record_reveal
  (content_type:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma (Seq.equal
      (WS.serialize_record content_type fragment)
      (B.append
        (serialize_record_header content_type (B.length fragment))
        fragment))
=
  let record : GCTX.tLSCiphertext = {
    GCTX.opaque_type = content_type;
    GCTX.legacy_record_version = GPV.TLS_1p2;
    GCTX.encrypted_record =
      (fragment <: GCTXF.tLSCiphertext_encrypted_record);
  } in
  GCTX.synth_tLSCiphertext_injective ();
  GCTX.synth_tLSCiphertext_inverse ();
  LP.serialize_synth_eq
    GCTX.tLSCiphertext'_parser
    GCTX.synth_tLSCiphertext
    GCTX.tLSCiphertext'_serializer
    GCTX.synth_tLSCiphertext_recip
    ()
    record;
  LP.serialize_nondep_then_eq
    (GCT.contentType_serializer `LP.serialize_nondep_then`
      GPV.protocolVersion_serializer)
    GCTXF.tLSCiphertext_encrypted_record_serializer
    ((content_type, GPV.TLS_1p2), fragment);
  LP.serialize_nondep_then_eq
    GCT.contentType_serializer
    GPV.protocolVersion_serializer
    (content_type, GPV.TLS_1p2);
  GCT.lemma_synth_contentType_inj ();
  GCT.lemma_synth_contentType_inv ();
  LP.serialize_synth_eq
    GCT.parse_contentType_key
    GCT.synth_contentType
    GCT.serialize_contentType_key
    GCT.synth_contentType_inv
    ()
    content_type;
  LP.serialize_enum_key_eq
    GCT.contentType_repr_serializer
    GCT.contentType_enum
    content_type;
  lemma_content_type_repr content_type;
  LP.serialize_u8_spec (content_type_byte content_type);
  GPV.lemma_synth_protocolVersion_inj ();
  GPV.lemma_synth_protocolVersion_inv ();
  LP.serialize_synth_eq
    GPV.parse_protocolVersion_key
    GPV.synth_protocolVersion
    GPV.serialize_protocolVersion_key
    GPV.synth_protocolVersion_inv
    ()
    GPV.TLS_1p2;
  LP.serialize_enum_key_eq
    GPV.protocolVersion_repr_serializer
    GPV.protocolVersion_enum
    GPV.TLS_1p2;
  assert_norm (
    LP.enum_repr_of_key GPV.protocolVersion_enum GPV.TLS_1p2 == 771us);
  LP.serialize_u16_spec_be 771us;
  lemma_u16_n_to_be 0x0303;
  LP.serialize_bounded_seq_vlbytes_bytes_eq 0 16640 fragment;
  LP.serialize_bounded_integer_spec
    2
    (U32.uint_to_t (B.length fragment));
  lemma_u16_n_to_be (B.length fragment);
  WS.lemma_serialize_record_generated content_type fragment;
  Seq.append_assoc
    (u8 (WS.content_type_to_byte content_type))
    (u16 0x0303)
    (B.append (u16 (B.length fragment)) fragment)
#pop-options

let lemma_serialize_record_head
  (content_type:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma (ensures
    B.length (WS.serialize_record content_type fragment) > 0 /\
    Seq.index (WS.serialize_record content_type fragment) 0 ==
      content_type_byte content_type)
=
  lemma_serialize_record_reveal content_type fragment;
  lemma_u8_reveal (WS.content_type_to_byte content_type);
  assert (Seq.equal
    (WS.serialize_record content_type fragment)
    (B.append
      (u8 (WS.content_type_to_byte content_type))
      (B.append (u16 0x0303) (B.append (u16 (B.length fragment)) fragment))));
  assert (B.length (u8 (WS.content_type_to_byte content_type)) == 1);
  assert (B.length (WS.serialize_record content_type fragment) > 0);
  assert (Seq.index (WS.serialize_record content_type fragment) 0 ==
    Seq.index (u8 (WS.content_type_to_byte content_type)) 0);
  assert (Seq.index (u8 (WS.content_type_to_byte content_type)) 0 ==
    content_type_byte content_type)

let lemma_serialize_record_legacy_version
  (content_type:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma (ensures
    B.length (WS.serialize_record content_type fragment) >= 3 /\
    Seq.index (WS.serialize_record content_type fragment) 1 == 0x03uy /\
    Seq.index (WS.serialize_record content_type fragment) 2 == 0x03uy)
=
  lemma_serialize_record_reveal content_type fragment;
  lemma_u8_reveal (WS.content_type_to_byte content_type);
  lemma_u16_of_bytes 0x03uy 0x03uy;
  assert (B.length (u8 (WS.content_type_to_byte content_type)) == 1);
  assert (B.length (u16 0x0303) == 2);
  assert (B.length (WS.serialize_record content_type fragment) ==
    5 + B.length fragment);
  assert (Seq.index (WS.serialize_record content_type fragment) 1 == 0x03uy);
  assert (Seq.index (WS.serialize_record content_type fragment) 2 == 0x03uy)

let lemma_serialize_record_fragment_length
  (content_type:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
    (requires
      B.length (WS.serialize_record content_type fragment) >= 5)
    (ensures
      WS.read_u16 (WS.serialize_record content_type fragment) 3 ==
        B.length fragment)
=
  lemma_serialize_record_reveal content_type fragment;
  lemma_u8_reveal (WS.content_type_to_byte content_type);
  WS.lemma_read_u16_u16 (B.length fragment);
  WS.lemma_read_u16_definition
    (WS.serialize_record content_type fragment)
    3;
  assert (WS.read_u16 (WS.serialize_record content_type fragment) 3 ==
    WS.read_u16 (u16 (B.length fragment)) 0)

#push-options "--fuel 8 --ifuel 2 --z3rlimit 20"
let lemma_serialize_record_prefix_from_header
  (raw:B.bytes)
  (content_type:T.content_type)
  (fragment_len:nat)
  : Lemma
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
=
  let fragment = Seq.slice raw 5 (5 + fragment_len) in
  let prefix = Seq.slice raw 0 (5 + fragment_len) in
  let raw_header = Seq.slice raw 0 5 in
  let serialized_header = serialize_record_header content_type fragment_len in
  Seq.lemma_len_slice raw 5 (5 + fragment_len);
  assert (B.length fragment == fragment_len);
  lemma_serialize_record_reveal content_type fragment;
  lemma_u8_reveal (WS.content_type_to_byte content_type);
  lemma_u16_of_bytes 0x03uy 0x03uy;
  lemma_u16_of_bytes (Seq.index raw 3) (Seq.index raw 4);
  lemma_singleton_of_list (content_type_byte content_type);
  lemma_of_list_append
    [content_type_byte content_type]
    [0x03uy; 0x03uy; Seq.index raw 3; Seq.index raw 4];
  lemma_of_list_append
    [0x03uy; 0x03uy]
    [Seq.index raw 3; Seq.index raw 4];
  Seq.lemma_len_slice raw 0 5;
  Seq.lemma_eq_intro
    serialized_header
    raw_header;
  Seq.lemma_len_slice raw 0 (5 + fragment_len);
  SeqP.slice_slice raw 0 (5 + fragment_len) 0 5;
  SeqP.slice_slice
    raw
    0
    (5 + fragment_len)
    5
    (5 + fragment_len);
  Seq.lemma_split prefix 5;
  assert (Seq.equal
    (B.append raw_header fragment)
    prefix);
  Seq.lemma_eq_elim serialized_header raw_header
#pop-options
