module TLS13.Wire.Spec.Reveal.ServerHello.Parseback
friend TLS13.Wire.Generated.ProtocolVersion
friend TLS13.Wire.Generated.Random
friend TLS13.Wire.Generated.CipherSuite
friend TLS13.Wire.Generated.ExtensionType
friend TLS13.Wire.Generated.NamedGroup
friend TLS13.Wire.Generated.SupportedVersionsServerHello
friend TLS13.Wire.Generated.ExtensionServerHello_extension_data_supported_versions
friend TLS13.Wire.Generated.KeyShareEntry_key_exchange
friend TLS13.Wire.Generated.KeyShareEntry
friend TLS13.Wire.Generated.KeyShareServerHello
friend TLS13.Wire.Generated.ExtensionServerHello_extension_data_key_share
friend TLS13.Wire.Generated.ExtensionServerHello
friend TLS13.Wire.Generated.ServerHelloBody_legacy_session_id_echo
friend TLS13.Wire.Generated.ServerHelloBody_extensions
friend TLS13.Wire.Generated.ServerHelloBody
friend TLS13.Wire.Generated.ServerHello_body
friend TLS13.Wire.Generated.ServerHello
friend TLS13.Wire.Generated.Handshake_body_server_hello
friend TLS13.Wire.Generated.HandshakeType
friend TLS13.Wire.Generated.Handshake
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.Spec
module LSeqB = LowParse.Pulse.SeqBytes
module WS = TLS13.Wire.Spec
module WSR = TLS13.Wire.Spec.Reveal
module WSRU = TLS13.Wire.Spec.Reveal.Util
module CHP = TLS13.Wire.Spec.Reveal.ClientHello.Parseback
module PBU = TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Util
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GCS = TLS13.Wire.Generated.CipherSuite
module GNG = TLS13.Wire.Generated.NamedGroup
module GET = TLS13.Wire.Generated.ExtensionType
module GSVSH = TLS13.Wire.Generated.SupportedVersionsServerHello
module GESHSV = TLS13.Wire.Generated.ExtensionServerHello_extension_data_supported_versions
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GKSEKE = TLS13.Wire.Generated.KeyShareEntry_key_exchange
module GKSSH = TLS13.Wire.Generated.KeyShareServerHello
module GESHK = TLS13.Wire.Generated.ExtensionServerHello_extension_data_key_share
module GSHSID = TLS13.Wire.Generated.ServerHelloBody_legacy_session_id_echo
module GSHExt = TLS13.Wire.Generated.ServerHelloBody_extensions
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSH = TLS13.Wire.Generated.ServerHello
module HT = TLS13.Wire.Generated.HandshakeType
module GHS = TLS13.Wire.Generated.Handshake

let byte_literal (n:nat) (b:U8.t)
  : Lemma
      (requires U8.v b == n % 256)
      (ensures WS.byte n == b)
=
  WS.lemma_byte_v n;
  assert_norm (WS.byte n == U8.uint_to_t (n % 256));
  assert (U8.v (WS.byte n) == U8.v b);
  U8.v_inj (WS.byte n) b

let u8_literal (n:nat) (b:U8.t)
  : Lemma
      (requires U8.v b == n % 256)
      (ensures Seq.equal (WS.u8 n) (B.of_list [b]))
=
  byte_literal n b;
  assert (WS.u8 n == B.singleton (WS.byte n));
  WSRU.lemma_singleton_of_list b

let u16_literal (n:nat) (hi lo:U8.t)
  : Lemma
      (requires U8.v hi == (n / 256) % 256 /\
                U8.v lo == n % 256)
      (ensures Seq.equal (WS.u16 n) (B.of_list [hi; lo]))
=
  byte_literal (n / 256) hi;
  byte_literal n lo;
  assert (WS.u16 n == B.of_list [WS.byte (n / 256); WS.byte n])

let u24_literal (n:nat) (b0 b1 b2:U8.t)
  : Lemma
      (requires U8.v b0 == (n / 65536) % 256 /\
                U8.v b1 == (n / 256) % 256 /\
                U8.v b2 == n % 256)
      (ensures Seq.equal (WS.u24 n) (B.of_list [b0; b1; b2]))
=
  byte_literal (n / 65536) b0;
  byte_literal (n / 256) b1;
  byte_literal n b2;
  assert (WS.u24 n == B.of_list [WS.byte (n / 65536); WS.byte (n / 256); WS.byte n])

let wsr_byte_literal (n:nat) (b:U8.t)
  : Lemma
      (requires U8.v b == n % 256)
      (ensures WSR.byte n == b)
=
  WSR.lemma_byte_value n;
  assert (U8.v (WSR.byte n) == U8.v b);
  U8.v_inj (WSR.byte n) b

let wsr_u24_literal (n:nat) (b0 b1 b2:U8.t)
  : Lemma
      (requires U8.v b0 == (n / 65536) % 256 /\
                U8.v b1 == (n / 256) % 256 /\
                U8.v b2 == n % 256)
      (ensures Seq.equal (WSR.u24 n) (B.of_list [b0; b1; b2]))
=
  WSR.lemma_u24_reveal n;
  wsr_byte_literal (n / 65536) b0;
  wsr_byte_literal (n / 256) b1;
  wsr_byte_literal n b2;
  assert (B.of_list [WSR.byte (n / 65536); WSR.byte (n / 256); WSR.byte n] ==
          B.of_list [b0; b1; b2])

let lemma_bounded_int_3_u24 = CHP.lemma_bounded_int_3_u24

let lemma_of_list_append_raw = PBU.lemma_of_list_append_raw
let lemma_bounded_int_1_raw = PBU.lemma_bounded_int_1_raw
let lemma_bounded_int_2_fits_raw = PBU.lemma_bounded_int_2_fits_raw
let lemma_bounded_int_2_raw = PBU.lemma_bounded_int_2_raw
let lemma_u8_uint_to_t_eq_raw = PBU.lemma_u8_uint_to_t_eq_raw
let lemma_u16_parts_fit_raw = PBU.lemma_u16_parts_fit_raw
let lemma_serialize_u16_bytes_raw = PBU.lemma_serialize_u16_bytes_raw
let lemma_vldata_unfold_raw = PBU.lemma_vldata_unfold_raw
let lemma_vldata_strong_unfold_raw = PBU.lemma_vldata_strong_unfold_raw
let lemma_olcons_raw = PBU.lemma_olcons_raw

let lemma_seq_equal_sym (#a:Type) (x y:Seq.seq a)
  : Lemma
      (requires Seq.equal x y)
      (ensures Seq.equal y x)
=
  Seq.lemma_eq_elim x y;
  Seq.lemma_eq_refl y x

let lemma_seq_equal_trans (#a:Type) (x y z:Seq.seq a)
  : Lemma
      (requires Seq.equal x y /\ Seq.equal y z)
      (ensures Seq.equal x z)
=
  Seq.lemma_eq_elim x y;
  Seq.lemma_eq_elim y z;
  Seq.lemma_eq_refl x z

#push-options "--split_queries always --fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_lp_protocol_version_tls12 ()
  : Lemma (Seq.equal (LP.serialize GPV.protocolVersion_serializer GPV.TLS_1p2)
                     (B.of_list [0x03uy; 0x03uy]))
=
  GPV.lemma_synth_protocolVersion_inj ();
  GPV.lemma_synth_protocolVersion_inv ();
  LP.serialize_synth_eq _ GPV.synth_protocolVersion GPV.serialize_protocolVersion_key GPV.synth_protocolVersion_inv () GPV.TLS_1p2;
  assert_norm (GPV.synth_protocolVersion_inv GPV.TLS_1p2 == GPV.TLS_1p2);
  LP.serialize_enum_key_eq GPV.protocolVersion_repr_serializer GPV.protocolVersion_enum GPV.TLS_1p2;
  assert_norm (LP.enum_repr_of_key GPV.protocolVersion_enum GPV.TLS_1p2 == 771us);
  lemma_u16_parts_fit_raw 771us;
  lemma_serialize_u16_bytes_raw 771us;
  assert_norm (U16.v 771us / 256 == 3);
  assert_norm (U16.v 771us % 256 == 3);
  lemma_u8_uint_to_t_eq_raw 3 0x03uy

let lemma_lp_protocol_version_tls13 ()
  : Lemma (Seq.equal (LP.serialize GPV.protocolVersion_serializer GPV.TLS_1p3)
                     (B.of_list [0x03uy; 0x04uy]))
=
  GPV.lemma_synth_protocolVersion_inj ();
  GPV.lemma_synth_protocolVersion_inv ();
  LP.serialize_synth_eq _ GPV.synth_protocolVersion GPV.serialize_protocolVersion_key GPV.synth_protocolVersion_inv () GPV.TLS_1p3;
  assert_norm (GPV.synth_protocolVersion_inv GPV.TLS_1p3 == GPV.TLS_1p3);
  LP.serialize_enum_key_eq GPV.protocolVersion_repr_serializer GPV.protocolVersion_enum GPV.TLS_1p3;
  assert_norm (LP.enum_repr_of_key GPV.protocolVersion_enum GPV.TLS_1p3 == 772us);
  lemma_u16_parts_fit_raw 772us;
  lemma_serialize_u16_bytes_raw 772us;
  assert_norm (U16.v 772us / 256 == 3);
  assert_norm (U16.v 772us % 256 == 4);
  lemma_u8_uint_to_t_eq_raw 3 0x03uy;
  lemma_u8_uint_to_t_eq_raw 4 0x04uy

let lemma_lp_cipher_suite_chacha ()
  : Lemma (Seq.equal (LP.serialize GCS.cipherSuite_serializer GCS.TLS_CHACHA20_POLY1305_SHA256)
                     (B.of_list [0x13uy; 0x03uy]))
=
  GCS.lemma_synth_cipherSuite_inj ();
  GCS.lemma_synth_cipherSuite_inv ();
  LP.serialize_synth_eq _ GCS.synth_cipherSuite GCS.serialize_maybe_cipherSuite_key GCS.synth_cipherSuite_inv () GCS.TLS_CHACHA20_POLY1305_SHA256;
  assert_norm (GCS.synth_cipherSuite_inv GCS.TLS_CHACHA20_POLY1305_SHA256 == LP.Known GCS.TLS_CHACHA20_POLY1305_SHA256);
  LP.serialize_maybe_enum_key_eq GCS.cipherSuite_repr_serializer GCS.cipherSuite_enum (LP.Known GCS.TLS_CHACHA20_POLY1305_SHA256);
  assert_norm (LP.repr_of_maybe_enum_key GCS.cipherSuite_enum (LP.Known GCS.TLS_CHACHA20_POLY1305_SHA256) == 4867us);
  lemma_u16_parts_fit_raw 4867us;
  lemma_serialize_u16_bytes_raw 4867us;
  lemma_u8_uint_to_t_eq_raw 0x13 0x13uy;
  lemma_u8_uint_to_t_eq_raw 0x03 0x03uy

let lemma_lp_named_group_x25519 ()
  : Lemma (Seq.equal (LP.serialize GNG.namedGroup_serializer GNG.X25519)
                     (B.of_list [0uy; 0x1duy]))
=
  GNG.lemma_synth_namedGroup_inj ();
  GNG.lemma_synth_namedGroup_inv ();
  LP.serialize_synth_eq _ GNG.synth_namedGroup GNG.serialize_maybe_namedGroup_key GNG.synth_namedGroup_inv () GNG.X25519;
  assert_norm (GNG.synth_namedGroup_inv GNG.X25519 == LP.Known GNG.X25519);
  LP.serialize_maybe_enum_key_eq GNG.namedGroup_repr_serializer GNG.namedGroup_enum (LP.Known GNG.X25519);
  assert_norm (LP.repr_of_maybe_enum_key GNG.namedGroup_enum (LP.Known GNG.X25519) == 29us);
  lemma_u16_parts_fit_raw 29us;
  lemma_serialize_u16_bytes_raw 29us;
  lemma_u8_uint_to_t_eq_raw 0 0uy;
  lemma_u8_uint_to_t_eq_raw 29 0x1duy
#pop-options

#restart-solver

private let lemma_lp_extension_server_hello_bytes_raw
  (x:GESH.extensionServerHello)
  (k:LP.dsum_known_key GESH.extensionServerHello_sum)
  (tag_bytes payload:Seq.seq U8.t)
  : Lemma
    (requires
      LP.dsum_tag_of_data GESH.extensionServerHello_sum x == LP.Known k /\
      Seq.equal
        (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                        (LP.dsum_enum GESH.extensionServerHello_sum)) (LP.Known k))
        tag_bytes /\
      Seq.equal
        (LP.serialize (GESH.serialize_extensionServerHello_cases k)
                      (LP.synth_dsum_case_recip GESH.extensionServerHello_sum (LP.Known k) x))
        payload)
    (ensures Seq.equal (LP.serialize GESH.extensionServerHello_serializer x)
                       (Seq.append tag_bytes payload))
=
  LP.serialize_dsum_eq
    GESH.extensionServerHello_sum
    GET.extensionType_repr_serializer
    GESH.parse_extensionServerHello_cases
    GESH.serialize_extensionServerHello_cases
    GESH.extensionServerHello_extension_data_default_parser
    GESH.extensionServerHello_extension_data_default_serializer
    x

private let lemma_lp_ext_tag_raw (k:LP.dsum_known_key GESH.extensionServerHello_sum) (repr:U16.t)
  : Lemma
      (requires
        LP.repr_of_maybe_enum_key (LP.dsum_enum GESH.extensionServerHello_sum) (LP.Known k) == repr /\
        U8.fits (U16.v repr / 256) /\
        U8.fits (U16.v repr % 256))
      (ensures Seq.equal
        (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                        (LP.dsum_enum GESH.extensionServerHello_sum)) (LP.Known k))
        (B.of_list [U8.uint_to_t (U16.v repr / 256); U8.uint_to_t (U16.v repr % 256)]))
=
  LP.serialize_maybe_enum_key_eq GET.extensionType_repr_serializer (LP.dsum_enum GESH.extensionServerHello_sum) (LP.Known k);
  lemma_u16_parts_fit_raw repr;
  lemma_serialize_u16_bytes_raw repr

#push-options "--split_queries always --fuel 8 --ifuel 8 --z3rlimit 100"
let lemma_lp_key_share_entry
  (key:GKSEKE.keyShareEntry_key_exchange{Seq.length key == 32})
  : Lemma (Seq.equal
      (LP.serialize GKSE.keyShareEntry_serializer { GKSE.group = GNG.X25519; GKSE.key_exchange = key })
      (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key))
=
  let e: GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key } in
  lemma_lp_named_group_x25519 ();
  Seq.lemma_eq_elim (LP.serialize GNG.namedGroup_serializer GNG.X25519)
                    (B.of_list [0uy; 0x1duy]);
  LP.serialize_bounded_seq_vlbytes_bytes_eq 1 65535 key;
  lemma_bounded_int_2_fits_raw 32;
  lemma_bounded_int_2_raw 32 0uy 32uy;
  GKSE.synth_keyShareEntry_injective ();
  GKSE.synth_keyShareEntry_inverse ();
  LP.serialize_synth_eq _ GKSE.synth_keyShareEntry GKSE.keyShareEntry'_serializer GKSE.synth_keyShareEntry_recip () e;
  assert (GKSE.synth_keyShareEntry_recip e == (GNG.X25519, key));
  LP.serialize_nondep_then_eq GNG.namedGroup_serializer GKSE.keyShareEntry_key_exchange_serializer (GNG.X25519, key);
  lemma_of_list_append_raw [0uy; 0x1duy] [0uy; 32uy];
  Seq.append_assoc (B.of_list [0uy; 0x1duy]) (B.of_list [0uy; 32uy]) key

let lemma_lp_server_key_share_extension
  (key:GKSEKE.keyShareEntry_key_exchange{Seq.length key == 32})
  : Lemma (Seq.equal
      (LP.serialize GESH.extensionServerHello_serializer
        (GESH.Extension_data_key_share ({ GKSE.group = GNG.X25519; GKSE.key_exchange = key })))
      (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key))
=
  let e: GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key } in
  let x: GESH.extensionServerHello = GESH.Extension_data_key_share e in
  let sum = GESH.extensionServerHello_sum in
  assert_norm (LP.dsum_tag_of_data sum x == LP.Known GET.Key_share);
  assert_norm (LP.repr_of_maybe_enum_key (LP.dsum_enum sum) (LP.Known GET.Key_share) == 51us);
  lemma_u16_parts_fit_raw 51us;
  lemma_lp_ext_tag_raw GET.Key_share 51us;
  lemma_u8_uint_to_t_eq_raw 0 0uy;
  lemma_u8_uint_to_t_eq_raw 51 0x33uy;
  assert (Seq.equal
    (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                    (LP.dsum_enum GESH.extensionServerHello_sum)) (LP.Known GET.Key_share))
    (B.of_list [0uy; 0x33uy]));
  assert_norm (LP.synth_dsum_case_recip sum (LP.Known GET.Key_share) x == e);
  lemma_lp_key_share_entry key;
  Seq.lemma_eq_elim (LP.serialize GKSE.keyShareEntry_serializer e)
                    (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key);
  let v: GESHK.extensionServerHello_extension_data_key_share = e in
  GESHK.extensionServerHello_extension_data_key_share_copyful_synth_injective ();
  GESHK.extensionServerHello_extension_data_key_share_copyful_synth_inverse ();
  LP.serialize_synth_eq _
    GESHK.synth_extensionServerHello_extension_data_key_share
    GESHK.extensionServerHello_extension_data_key_share'_serializer
    GESHK.synth_extensionServerHello_extension_data_key_share_recip
    () v;
  assert (GESHK.synth_extensionServerHello_extension_data_key_share_recip v == v);
  assert (GESHK.extensionServerHello_extension_data_key_share_serializer ==
    LP.serialize_synth _
      GESHK.synth_extensionServerHello_extension_data_key_share
      GESHK.extensionServerHello_extension_data_key_share'_serializer
      GESHK.synth_extensionServerHello_extension_data_key_share_recip
      ());
  assert (LP.serialize GESHK.extensionServerHello_extension_data_key_share_serializer v ==
          LP.serialize GESHK.extensionServerHello_extension_data_key_share'_serializer v);
  lemma_vldata_strong_unfold_raw 0 65535 GKSSH.keyShareServerHello_serializer v;
  assert (GESHK.extensionServerHello_extension_data_key_share'_serializer ==
          LP.serialize_bounded_vldata_strong 0 65535 GKSSH.keyShareServerHello_serializer);
  assert (LP.serialize GKSSH.keyShareServerHello_serializer v ==
          LP.serialize GKSE.keyShareEntry_serializer e);
  Seq.lemma_eq_elim
    (LP.serialize GKSSH.keyShareServerHello_serializer v)
    (LP.serialize GKSE.keyShareEntry_serializer e);
  assert (Seq.equal
    (LP.serialize GKSSH.keyShareServerHello_serializer v)
    (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key));
  Seq.lemma_eq_elim
    (LP.serialize GKSSH.keyShareServerHello_serializer v)
    (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key);
  let entry_header = B.of_list [0uy; 0x1duy; 0uy; 32uy] in
  Seq.lemma_seq_of_list_induction [0uy; 0x1duy; 0uy; 32uy];
  assert_norm (FStar.List.Tot.length [0uy; 0x1duy; 0uy; 32uy] == 4);
  assert (Seq.length entry_header == 4);
  Seq.lemma_len_append entry_header key;
  assert (Seq.length key == 32);
  assert (Seq.length (Seq.append entry_header key) == 36);
  assert (Seq.equal entry_header (B.of_list [0uy; 0x1duy; 0uy; 32uy]));
  assert (Seq.length (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key) == 36);
  assert (Seq.length (LP.serialize GKSSH.keyShareServerHello_serializer v) == 36);
  assert (LP.serialize GESHK.extensionServerHello_extension_data_key_share'_serializer v ==
          Seq.append
            (LP.serialize (LP.serialize_bounded_integer 2) (U32.uint_to_t 36))
            (LP.serialize GKSSH.keyShareServerHello_serializer v));
  lemma_bounded_int_2_fits_raw 36;
  lemma_bounded_int_2_raw 36 0uy 36uy;
  assert (Seq.equal
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share'_serializer v)
    (Seq.append (B.of_list [0uy; 36uy]) (LP.serialize GKSSH.keyShareServerHello_serializer v)));
  Seq.lemma_eq_elim
    (LP.serialize GKSSH.keyShareServerHello_serializer v)
    (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key);
  assert (Seq.equal
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share'_serializer v)
    (Seq.append (B.of_list [0uy; 36uy])
      (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key)));
  lemma_of_list_append_raw [0uy; 36uy] [0uy; 0x1duy; 0uy; 32uy];
  Seq.append_assoc (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key;
  assert (Seq.equal
    (Seq.append (Seq.append (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy])) key)
    (Seq.append (B.of_list [0uy; 36uy]) (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key)));
  lemma_seq_equal_sym
    (Seq.append (Seq.append (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy])) key)
    (Seq.append (B.of_list [0uy; 36uy]) (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key));
  assert (Seq.equal
    (Seq.append (B.of_list [0uy; 36uy]) (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key))
    (Seq.append (Seq.append (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy])) key));
  assert_norm (FStar.List.Tot.append [0uy; 36uy] [0uy; 0x1duy; 0uy; 32uy] ==
               [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  assert (Seq.equal
    (Seq.append (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy]))
    (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]));
  Seq.lemma_eq_elim
    (Seq.append (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy]))
    (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  assert (Seq.equal
    (Seq.append (Seq.append (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy])) key)
    (Seq.append (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key));
  lemma_seq_equal_trans
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share'_serializer v)
    (Seq.append (B.of_list [0uy; 36uy]) (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key))
    (Seq.append (Seq.append (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy])) key);
  lemma_seq_equal_trans
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share'_serializer v)
    (Seq.append (Seq.append (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy])) key)
    (Seq.append (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key);
  assert (Seq.equal
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share'_serializer v)
    (Seq.append (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key));
  assert (Seq.equal
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share_serializer v)
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share'_serializer v));
  lemma_seq_equal_trans
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share_serializer v)
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share'_serializer v)
    (Seq.append (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key);
  assert (Seq.equal
    (LP.serialize GESHK.extensionServerHello_extension_data_key_share_serializer v)
    (Seq.append (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key));
  assert (GESH.serialize_extensionServerHello_cases GET.Key_share
          == GESHK.extensionServerHello_extension_data_key_share_serializer);
  lemma_lp_extension_server_hello_bytes_raw x GET.Key_share
    (B.of_list [0uy; 0x33uy])
    (Seq.append (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key);
  assert_norm (FStar.List.Tot.append [0uy; 0x33uy] [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] ==
               [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  lemma_of_list_append_raw [0uy; 0x33uy] [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy];
  assert (Seq.equal
    (Seq.append (B.of_list [0uy; 0x33uy]) (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]))
    (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]));
  Seq.append_assoc (B.of_list [0uy; 0x33uy]) (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key;
  assert (Seq.equal
    (LP.serialize GESH.extensionServerHello_serializer x)
    (Seq.append (Seq.append (B.of_list [0uy; 0x33uy]) (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])) key));
  Seq.lemma_eq_elim
    (Seq.append (B.of_list [0uy; 0x33uy]) (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]))
    (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  assert (Seq.equal
    (LP.serialize GESH.extensionServerHello_serializer x)
    (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key))

let lemma_lp_server_supported_versions_extension ()
  : Lemma (Seq.equal
      (LP.serialize GESH.extensionServerHello_serializer
        (GESH.Extension_data_supported_versions GPV.TLS_1p3))
      (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))
=
  let x : GESH.extensionServerHello =
   GESH.Extension_data_supported_versions GPV.TLS_1p3 in
  let sum = GESH.extensionServerHello_sum in
  assert_norm (LP.dsum_tag_of_data sum x == LP.Known GET.Supported_versions);
  assert_norm (LP.repr_of_maybe_enum_key (LP.dsum_enum sum) (LP.Known GET.Supported_versions) == 43us);
  lemma_u16_parts_fit_raw 43us;
  lemma_lp_ext_tag_raw GET.Supported_versions 43us;
  lemma_u8_uint_to_t_eq_raw 0 0uy;
  lemma_u8_uint_to_t_eq_raw 43 0x2buy;
  assert (Seq.equal
   (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                   (LP.dsum_enum GESH.extensionServerHello_sum)) (LP.Known GET.Supported_versions))
   (B.of_list [0uy; 0x2buy]));
  assert_norm (LP.synth_dsum_case_recip sum (LP.Known GET.Supported_versions) x == GPV.TLS_1p3);
  lemma_lp_protocol_version_tls13 ();
  Seq.lemma_eq_elim
   (LP.serialize GPV.protocolVersion_serializer GPV.TLS_1p3)
   (B.of_list [0x03uy; 0x04uy]);
  GSVSH.supportedVersionsServerHello_parser_serializer_eq ();
  assert (GSVSH.supportedVersionsServerHello_serializer == GPV.protocolVersion_serializer);
  assert (Seq.equal
   (LP.serialize GSVSH.supportedVersionsServerHello_serializer GPV.TLS_1p3)
   (B.of_list [0x03uy; 0x04uy]));
  let v : GESHSV.extensionServerHello_extension_data_supported_versions =
   GPV.TLS_1p3 in
  lemma_vldata_unfold_raw 0 65535 GSVSH.supportedVersionsServerHello_serializer v;
  lemma_bounded_int_2_fits_raw 2;
  lemma_bounded_int_2_raw 2 0uy 2uy;
  assert (Seq.equal
   (LP.serialize GESHSV.extensionServerHello_extension_data_supported_versions_serializer v)
   (Seq.append (B.of_list [0uy; 2uy])
     (LP.serialize GSVSH.supportedVersionsServerHello_serializer v)));
  Seq.lemma_eq_elim
   (LP.serialize GSVSH.supportedVersionsServerHello_serializer v)
   (B.of_list [0x03uy; 0x04uy]);
  assert (Seq.equal
   (LP.serialize GESHSV.extensionServerHello_extension_data_supported_versions_serializer v)
   (Seq.append (B.of_list [0uy; 2uy]) (B.of_list [0x03uy; 0x04uy])));
  lemma_of_list_append_raw [0uy; 2uy] [0x03uy; 0x04uy];
  assert_norm (FStar.List.Tot.append [0uy; 2uy] [0x03uy; 0x04uy]
              == [0uy; 2uy; 0x03uy; 0x04uy]);
  assert (Seq.equal
   (Seq.append (B.of_list [0uy; 2uy]) (B.of_list [0x03uy; 0x04uy]))
   (B.of_list [0uy; 2uy; 0x03uy; 0x04uy]));
  lemma_seq_equal_trans
   (LP.serialize GESHSV.extensionServerHello_extension_data_supported_versions_serializer v)
   (Seq.append (B.of_list [0uy; 2uy]) (B.of_list [0x03uy; 0x04uy]))
   (B.of_list [0uy; 2uy; 0x03uy; 0x04uy]);
  assert (Seq.equal
   (LP.serialize GESHSV.extensionServerHello_extension_data_supported_versions_serializer v)
   (B.of_list [0uy; 2uy; 0x03uy; 0x04uy]));
  assert (GESH.serialize_extensionServerHello_cases GET.Supported_versions
         == GESHSV.extensionServerHello_extension_data_supported_versions_serializer);
  lemma_lp_extension_server_hello_bytes_raw x GET.Supported_versions
   (B.of_list [0uy; 0x2buy])
   (B.of_list [0uy; 2uy; 0x03uy; 0x04uy]);
  assert (Seq.equal
   (LP.serialize GESH.extensionServerHello_serializer x)
   (Seq.append (B.of_list [0uy; 0x2buy]) (B.of_list [0uy; 2uy; 0x03uy; 0x04uy])));
  assert_norm (FStar.List.Tot.append [0uy; 0x2buy] [0uy; 2uy; 0x03uy; 0x04uy]
              == [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]);
  lemma_of_list_append_raw [0uy; 0x2buy] [0uy; 2uy; 0x03uy; 0x04uy];
  lemma_seq_equal_trans
   (LP.serialize GESH.extensionServerHello_serializer x)
   (Seq.append (B.of_list [0uy; 0x2buy]) (B.of_list [0uy; 2uy; 0x03uy; 0x04uy]))
   (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])
#pop-options

#restart-solver

let lemma_ws_server_key_share_extension_bytes (key:B.bytes)
  : Lemma (Seq.equal
      (WS.server_key_share_extension key)
      (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key))
=
  u16_literal 0x0033 0uy 0x33uy;
  u16_literal 36 0uy 36uy;
  u16_literal 0x001d 0uy 0x1duy;
  u16_literal 32 0uy 32uy;
  assert (WS.server_key_share_extension key ==
    WS.append5 (WS.u16 0x0033) (WS.u16 36) (WS.u16 0x001d) (WS.u16 32) key);
  Seq.lemma_eq_elim (WS.u16 0x0033) (B.of_list [0uy; 0x33uy]);
  Seq.lemma_eq_elim (WS.u16 36) (B.of_list [0uy; 36uy]);
  Seq.lemma_eq_elim (WS.u16 0x001d) (B.of_list [0uy; 0x1duy]);
  Seq.lemma_eq_elim (WS.u16 32) (B.of_list [0uy; 32uy]);
  assert_norm (FStar.List.Tot.append [0uy; 0x1duy] [0uy; 32uy] ==
               [0uy; 0x1duy; 0uy; 32uy]);
  lemma_olcons_raw [0uy; 0x1duy] [0uy; 32uy] key;
  Seq.lemma_eq_elim
    (Seq.append (B.of_list [0uy; 0x1duy]) (Seq.append (B.of_list [0uy; 32uy]) key))
    (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key);
  assert_norm (FStar.List.Tot.append [0uy; 36uy] [0uy; 0x1duy; 0uy; 32uy] ==
               [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  lemma_olcons_raw [0uy; 36uy] [0uy; 0x1duy; 0uy; 32uy] key;
  Seq.lemma_eq_elim
    (Seq.append (B.of_list [0uy; 36uy]) (Seq.append (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key))
    (Seq.append (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key);
  assert_norm (FStar.List.Tot.append [0uy; 0x33uy] [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] ==
               [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  lemma_olcons_raw [0uy; 0x33uy] [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] key;
  Seq.lemma_eq_elim
    (Seq.append (B.of_list [0uy; 0x33uy]) (Seq.append (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key))
    (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key)

let lemma_ws_server_supported_versions_extension_bytes ()
  : Lemma (Seq.equal
      (WS.server_supported_versions_extension ())
      (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))
=
  u16_literal 0x002b 0uy 0x2buy;
  u16_literal 2 0uy 2uy;
  u16_literal 0x0304 0x03uy 0x04uy;
  assert (WS.server_supported_versions_extension () ==
    WS.append3 (WS.u16 0x002b) (WS.u16 2) (WS.u16 0x0304));
  Seq.lemma_eq_elim (WS.u16 0x002b) (B.of_list [0uy; 0x2buy]);
  Seq.lemma_eq_elim (WS.u16 2) (B.of_list [0uy; 2uy]);
  Seq.lemma_eq_elim (WS.u16 0x0304) (B.of_list [0x03uy; 0x04uy]);
  assert_norm (FStar.List.Tot.append [0uy; 2uy] [0x03uy; 0x04uy] ==
               [0uy; 2uy; 0x03uy; 0x04uy]);
  lemma_of_list_append_raw [0uy; 2uy] [0x03uy; 0x04uy];
  Seq.lemma_eq_elim
    (Seq.append (B.of_list [0uy; 2uy]) (B.of_list [0x03uy; 0x04uy]))
    (B.of_list [0uy; 2uy; 0x03uy; 0x04uy]);
  assert_norm (FStar.List.Tot.append [0uy; 0x2buy] [0uy; 2uy; 0x03uy; 0x04uy] ==
               [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]);
  lemma_of_list_append_raw [0uy; 0x2buy] [0uy; 2uy; 0x03uy; 0x04uy];
  Seq.lemma_eq_elim
    (Seq.append (B.of_list [0uy; 0x2buy]) (B.of_list [0uy; 2uy; 0x03uy; 0x04uy]))
    (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])

let canonical_key_exchange
  (key:B.bytes_of_len 32)
  : (ke:GKSEKE.keyShareEntry_key_exchange{ke == key /\ Seq.length ke == 32})
=
  assert (LP.parse_bounded_seq_vlbytes_pred 1 65535 key);
  key

let canonical_key_share_extension
  (key:B.bytes_of_len 32)
  : GESH.extensionServerHello
=
  let ke = canonical_key_exchange key in
  let kse: GKSE.keyShareEntry = {
    GKSE.group = GNG.X25519;
    GKSE.key_exchange = ke;
  } in
  GESH.Extension_data_key_share kse

let canonical_supported_versions_extension (_:unit)
  : GESH.extensionServerHello
=
  GESH.Extension_data_supported_versions GPV.TLS_1p3

let canonical_server_hello_extensions
  (key:B.bytes_of_len 32)
  : GSHBody.serverHelloBody_extensions
=
  let ks = canonical_key_share_extension key in
  let sv = canonical_supported_versions_extension () in
  GESH.extensionServerHello_bytesize_eq ks;
  GESH.extensionServerHello_bytesize_eq sv;
  GSHBody.serverHelloBody_extensions_list_bytesize_cons ks [sv];
  GSHBody.serverHelloBody_extensions_list_bytesize_cons sv [];
  GSHBody.serverHelloBody_extensions_list_bytesize_nil;
  [ks; sv]

let canonical_server_hello_body
  (sh:M.server_hello)
  : GSHBody.serverHelloBody
=
  {
    GSHBody.legacy_session_id_echo = B.empty;
    GSHBody.cipher_suite = GCS.TLS_CHACHA20_POLY1305_SHA256;
    GSHBody.legacy_compression_method = 0uy;
    GSHBody.extensions = canonical_server_hello_extensions sh.M.key_share;
  }

let canonical_server_hello_low
  (sh:M.server_hello)
  : GSH.serverHello
=
  let body = canonical_server_hello_body sh in
  {
    GSH.legacy_version = GPV.TLS_1p2;
    GSH.body = GSHB.serverHello_body_synth sh.M.random body;
  }

#restart-solver

#push-options "--split_queries always --fuel 8 --ifuel 8 --z3rlimit 120"
let lemma_lp_server_hello_extensions
  (key:B.bytes_of_len 32)
  : Lemma (Seq.equal
      (LP.serialize GSHExt.serverHelloBody_extensions_serializer
        (canonical_server_hello_extensions key))
      (Seq.append
        (B.of_list [0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))))
=
  let ks = canonical_key_share_extension key in
  let sv = canonical_supported_versions_extension () in
  assert (canonical_server_hello_extensions key == [ks; sv]);
  lemma_lp_server_key_share_extension (canonical_key_exchange key);
  lemma_lp_server_supported_versions_extension ();
  Seq.lemma_eq_elim (LP.serialize GESH.extensionServerHello_serializer ks)
    (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key);
  Seq.lemma_eq_elim (LP.serialize GESH.extensionServerHello_serializer sv)
    (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]);
  LP.serialize_list_nil GESH.extensionServerHello_parser GESH.extensionServerHello_serializer;
  LP.serialize_list_cons GESH.extensionServerHello_parser GESH.extensionServerHello_serializer sv [];
  LP.serialize_list_cons GESH.extensionServerHello_parser GESH.extensionServerHello_serializer ks [sv];
  lemma_of_list_append_raw [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] [];
  Seq.append_assoc
    (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
    key
    (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]);
  assert (Seq.equal
    (LP.serialize (LP.serialize_list _ GESH.extensionServerHello_serializer) [ks; sv])
    (Seq.append
      (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))));
  let body =
    Seq.append
      (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])) in
  assert (B.length key == 32);
  GSHExt.serverHelloBody_extensions_copyful_synth_injective ();
  GSHExt.serverHelloBody_extensions_copyful_synth_inverse ();
  LP.serialize_synth_eq _
    GSHExt.synth_serverHelloBody_extensions
    GSHExt.serverHelloBody_extensions'_serializer
    GSHExt.synth_serverHelloBody_extensions_recip
    () (canonical_server_hello_extensions key);
  assert (GSHExt.synth_serverHelloBody_extensions_recip
    (canonical_server_hello_extensions key) == [ks; sv]);
  LP.serialize_length (LP.serialize_list _ GESH.extensionServerHello_serializer) [ks; sv];
  assert (Seq.length (LP.serialize (LP.serialize_list _ GESH.extensionServerHello_serializer) [ks; sv]) == 46);
  Seq.lemma_eq_elim (LP.serialize (LP.serialize_list _ GESH.extensionServerHello_serializer) [ks; sv]) body;
  assert (Seq.length body == 46);
  lemma_vldata_strong_unfold_raw 6 65535 (LP.serialize_list _ GESH.extensionServerHello_serializer) [ks; sv];
  lemma_bounded_int_2_fits_raw 46;
  lemma_bounded_int_2_raw 46 0uy 46uy;
  assert_norm (FStar.List.Tot.append [0uy; 46uy] [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] ==
               [0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  lemma_olcons_raw
    [0uy; 46uy]
    [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]
    (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]));
  assert (Seq.equal
    (Seq.append
      (B.of_list [0uy; 46uy])
      (Seq.append
        (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))))
    (Seq.append
      (B.of_list (FStar.List.Tot.append [0uy; 46uy]
        [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]))
      (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))));
  assert_norm (FStar.List.Tot.append [0uy; 46uy]
    [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] ==
    [0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  assert (Seq.equal
    (LP.serialize GSHExt.serverHelloBody_extensions_serializer
      (canonical_server_hello_extensions key))
    (Seq.append
      (B.of_list [0uy; 46uy])
      (Seq.append
        (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])))));
  lemma_olcons_raw
    [0uy; 46uy]
    [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]
    (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]));
  assert (Seq.equal
    (LP.serialize GSHExt.serverHelloBody_extensions_serializer
      (canonical_server_hello_extensions key))
    (Seq.append
      (B.of_list [0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))))

let lemma_lp_server_hello_body_payload
  (sh:M.server_hello{sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256})
  : Lemma (Seq.equal
      (LP.serialize GSHBody.serverHelloBody_serializer
        (canonical_server_hello_body sh))
      (Seq.append
        (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))))
=
  let body = canonical_server_hello_body sh in
  LP.serialize_bounded_seq_vlbytes_bytes_eq 0 32 B.empty;
  lemma_bounded_int_1_raw 0;
  lemma_lp_cipher_suite_chacha ();
  lemma_lp_server_hello_extensions sh.M.key_share;
  Seq.lemma_eq_elim (LP.serialize GCS.cipherSuite_serializer GCS.TLS_CHACHA20_POLY1305_SHA256)
                    (B.of_list [0x13uy; 0x03uy]);
  Seq.lemma_eq_elim (LP.serialize GSHExt.serverHelloBody_extensions_serializer body.GSHBody.extensions)
    (Seq.append
      (B.of_list [0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])));
  GSHBody.synth_serverHelloBody_injective ();
  GSHBody.synth_serverHelloBody_inverse ();
  LP.serialize_synth_eq _ GSHBody.synth_serverHelloBody GSHBody.serverHelloBody'_serializer GSHBody.synth_serverHelloBody_recip () body;
  assert (GSHBody.synth_serverHelloBody_recip body ==
    ((B.empty, GCS.TLS_CHACHA20_POLY1305_SHA256), (0uy, body.GSHBody.extensions)));
  LP.serialize_nondep_then_eq GSHSID.serverHelloBody_legacy_session_id_echo_serializer GCS.cipherSuite_serializer (B.empty, GCS.TLS_CHACHA20_POLY1305_SHA256);
  LP.serialize_nondep_then_eq LP.serialize_u8 GSHExt.serverHelloBody_extensions_serializer (0uy, body.GSHBody.extensions);
  LP.serialize_nondep_then_eq
    (GSHSID.serverHelloBody_legacy_session_id_echo_serializer `LP.serialize_nondep_then` GCS.cipherSuite_serializer)
    (LP.serialize_u8 `LP.serialize_nondep_then` GSHExt.serverHelloBody_extensions_serializer)
    ((B.empty, GCS.TLS_CHACHA20_POLY1305_SHA256), (0uy, body.GSHBody.extensions));
  assert (Seq.equal (LP.serialize GSHSID.serverHelloBody_legacy_session_id_echo_serializer B.empty)
                    (B.of_list [0uy]));
  LP.serialize_u8_spec 0uy;
  assert (Seq.equal (LP.serialize LP.serialize_u8 0uy) (B.of_list [0uy]));
  lemma_of_list_append_raw [0uy] [0x13uy; 0x03uy];
  lemma_of_list_append_raw [0uy; 0x13uy; 0x03uy] [0uy];
  lemma_of_list_append_raw [0uy; 0x13uy; 0x03uy; 0uy] [0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy];
  Seq.append_assoc
    (B.of_list [0uy; 0x13uy; 0x03uy; 0uy])
    (B.of_list [0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
    (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))
#pop-options

#restart-solver

#push-options "--split_queries always --fuel 6 --ifuel 4 --z3rlimit 80"
private let lemma_lp_server_hello_body_low_bytes
  (sh:M.server_hello{sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256})
  : Lemma (Seq.equal
      (LP.serialize
        GSHB.serverHello_body_serializer
        (GSHB.serverHello_body_synth sh.M.random (canonical_server_hello_body sh)))
      (Seq.append
        sh.M.random
        (Seq.append
          (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
          (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])))))
=
  let body = canonical_server_hello_body sh in
  let low_body = GSHB.serverHello_body_synth sh.M.random body in
  lemma_lp_server_hello_body_payload sh;
  Seq.lemma_eq_elim
    (LP.serialize GSHBody.serverHelloBody_serializer body)
    (Seq.append
      (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])));
  LP.serialize_ifthenelse_synth_inverse'
    GSHB.serialize_serverHello_body_param
    sh.M.random
    body;
  assert (GSHB.serialize_serverHello_body_param.LP.serialize_ifthenelse_synth_recip low_body ==
          (| sh.M.random, body |));
  LSeqB.serialize_lseq_bytes_eq 32 sh.M.random;
  assert (GSHB.serverHello_body_random_serializer == LP.serialize_lseq_bytes 32);
  assert (Seq.equal
    (LP.serialize GSHB.serverHello_body_random_serializer sh.M.random)
    sh.M.random);
  assert (GSHB.serialize_serverHello_body_param.LP.serialize_ifthenelse_payload_serializer
            (GSHB.parse_serverHello_body_param.LP.parse_ifthenelse_tag_cond sh.M.random)
          == GSHBody.serverHelloBody_serializer);
  assert (GSHB.serverHello_body_serializer ==
          LP.serialize_ifthenelse GSHB.serialize_serverHello_body_param);
  assert (Seq.equal
    (LP.serialize GSHB.serverHello_body_serializer low_body)
    (Seq.append
      sh.M.random
      (LP.serialize GSHBody.serverHelloBody_serializer body)));
  assert (Seq.equal
    (LP.serialize GSHB.serverHello_body_serializer low_body)
    (Seq.append
      sh.M.random
      (Seq.append
        (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])))))

let lemma_lp_server_hello_low_bytes
  (sh:M.server_hello{sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256})
  : Lemma (Seq.equal
      (LP.serialize GSH.serverHello_serializer (canonical_server_hello_low sh))
      (Seq.append
        (B.of_list [0x03uy; 0x03uy])
        (Seq.append
          sh.M.random
          (Seq.append
            (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
            (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))))))
=
  let body = canonical_server_hello_body sh in
  let low = canonical_server_hello_low sh in
  assert (low.GSH.legacy_version == GPV.TLS_1p2);
  assert (low.GSH.body == GSHB.serverHello_body_synth sh.M.random body);
  lemma_lp_protocol_version_tls12 ();
  lemma_lp_server_hello_body_low_bytes sh;
  Seq.lemma_eq_elim
    (LP.serialize GSHB.serverHello_body_serializer low.GSH.body)
    (Seq.append
      sh.M.random
      (Seq.append
        (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))));
  GSH.synth_serverHello_injective ();
  GSH.synth_serverHello_inverse ();
  LP.serialize_synth_eq _
    GSH.synth_serverHello
    GSH.serverHello'_serializer
    GSH.synth_serverHello_recip
    () low;
  assert (GSH.synth_serverHello_recip low == (GPV.TLS_1p2, low.GSH.body));
  LP.serialize_nondep_then_eq
    GPV.protocolVersion_serializer
    GSHB.serverHello_body_serializer
    (GPV.TLS_1p2, low.GSH.body);
  Seq.lemma_eq_elim
    (LP.serialize GPV.protocolVersion_serializer GPV.TLS_1p2)
    (B.of_list [0x03uy; 0x03uy]);
  assert (Seq.equal
    (LP.serialize GSH.serverHello_serializer low)
    (Seq.append
      (B.of_list [0x03uy; 0x03uy])
      (LP.serialize GSHB.serverHello_body_serializer low.GSH.body)));
  Seq.lemma_eq_elim
    (LP.serialize GSHB.serverHello_body_serializer low.GSH.body)
    (Seq.append
      sh.M.random
      (Seq.append
        (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))));
  assert (Seq.equal
    (LP.serialize GSH.serverHello_serializer low)
    (Seq.append
      (B.of_list [0x03uy; 0x03uy])
      (Seq.append
        sh.M.random
        (Seq.append
          (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
          (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))))));
  ()
#pop-options

#push-options "--split_queries always --fuel 4 --ifuel 2 --z3rlimit 10"
let lemma_ghs_serialize_server_hello_shape
  (low:GSH.serverHello)
  : Lemma
      (requires B.length (LP.serialize GSH.serverHello_serializer low) < 16777216)
      (ensures Seq.equal
        (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello low))
        (B.append
          (B.of_list [2uy])
          (B.append
            (WSR.u24 (B.length (LP.serialize GSH.serverHello_serializer low)))
            (LP.serialize GSH.serverHello_serializer low))))
=
  let body = LP.serialize GSH.serverHello_serializer low in
  LP.serialize_sum_eq
    GHS.handshake_sum HT.handshakeType_repr_serializer GHS.serialize_handshake_cases
    (GHS.Body_server_hello low);
  LP.serialize_enum_key_eq
    HT.handshakeType_repr_serializer HT.handshakeType_enum HT.Server_hello;
  assert_norm (LP.enum_repr_of_key HT.handshakeType_enum HT.Server_hello == 2z);
  LP.serialize_u8_spec 2z;
  assert_norm (GHS.serialize_handshake_cases HT.Server_hello == GHS.handshake_body_server_hello_serializer);
  assert_norm (GHS.handshake_body_server_hello_serializer ==
               LP.serialize_bounded_vldata 0 16777215 GSH.serverHello_serializer);
  lemma_vldata_unfold_raw 0 16777215 GSH.serverHello_serializer low;
  assert_norm (LP.log256' 16777215 == 3);
  LP.serialize_length GSH.serverHello_serializer low;
  assert (B.length body < 16777216);
  assert_norm (pow2 32 == 4294967296);
  assert (U32.fits (B.length body));
  lemma_bounded_int_3_u24 (B.length body);
  Seq.lemma_seq_of_list_induction [2uy];
  let tag =
    LP.serialize
      (LP.serialize_enum_key HT.handshakeType_repr_parser HT.handshakeType_repr_serializer HT.handshakeType_enum)
      HT.Server_hello in
  let blen : n:nat{n < pow2 (8 * 3) /\ U32.fits n} = B.length body in
  let len0 : U32.t = U32.uint_to_t blen in
  U32.vu_inv blen;
  assert (U32.v len0 == blen);
  LP.bounded_integer_prop_equiv 3 len0;
  assert (LP.bounded_integer_prop 3 len0);
  let len : LP.bounded_integer 3 = len0 in
  let lenb = LP.serialize (LP.serialize_bounded_integer 3) len in
  assert (Seq.equal tag (B.of_list [2uy]));
  assert (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello low))
    (B.append tag (B.append lenb body)));
  assert (Seq.equal lenb (WSR.u24 (B.length body)));
  Seq.lemma_eq_elim lenb (WSR.u24 (B.length body));
  assert (Seq.equal (B.append tag (B.append lenb body))
                    (B.append (B.of_list [2uy]) (B.append (WSR.u24 (B.length body)) body)));
  assert (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello low))
    (B.append (B.of_list [2uy]) (B.append (WSR.u24 (B.length body)) body)))
#pop-options

#restart-solver

#push-options "--split_queries always --fuel 6 --ifuel 4 --z3rlimit 80"
private let lemma_ws_server_hello_extensions_bytes (key:B.bytes_of_len 32)
  : Lemma (Seq.equal
      (B.append (WS.server_key_share_extension key) (WS.server_supported_versions_extension ()))
      (Seq.append
        (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))))
=
  lemma_ws_server_key_share_extension_bytes key;
  lemma_ws_server_supported_versions_extension_bytes ();
  Seq.lemma_eq_elim
    (WS.server_key_share_extension key)
    (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key);
  Seq.lemma_eq_elim
    (WS.server_supported_versions_extension ())
    (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]);
  Seq.append_assoc
    (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
    key
    (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])

private let lemma_ws_server_hello_extensions_len (key:B.bytes_of_len 32)
  : Lemma
      (B.length (B.append (WS.server_key_share_extension key) (WS.server_supported_versions_extension ())) == 46)
=
  let extensions =
    B.append (WS.server_key_share_extension key) (WS.server_supported_versions_extension ()) in
  let flat =
    Seq.append
      (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])) in
  lemma_ws_server_hello_extensions_bytes key;
  Seq.lemma_eq_elim extensions flat;
  Seq.lemma_len_append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]);
  Seq.lemma_len_append
    (B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
    (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]));
  assert (B.length extensions == 46)

private let lemma_ws_server_hello_tail_bytes (key:B.bytes_of_len 32)
  : Lemma (Seq.equal
      (Seq.append
        (WS.u8 0)
        (Seq.append
          (WS.u16 0x1303)
          (Seq.append
            (WS.u8 0)
            (Seq.append
              (WS.u16 46)
              (B.append (WS.server_key_share_extension key) (WS.server_supported_versions_extension ()))))))
      (Seq.append
        (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append key (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))))
=
  let sv = B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy] in
  let ext_prefix = B.of_list [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] in
  let extensions = B.append (WS.server_key_share_extension key) (WS.server_supported_versions_extension ()) in
  let ext_flat = Seq.append ext_prefix (Seq.append key sv) in
  lemma_ws_server_hello_extensions_bytes key;
  Seq.lemma_eq_elim extensions ext_flat;
  u8_literal 0 0uy;
  u16_literal 0x1303 0x13uy 0x03uy;
  u16_literal 46 0uy 46uy;
  Seq.lemma_eq_elim (WS.u8 0) (B.of_list [0uy]);
  Seq.lemma_eq_elim (WS.u16 0x1303) (B.of_list [0x13uy; 0x03uy]);
  Seq.lemma_eq_elim (WS.u16 46) (B.of_list [0uy; 46uy]);
  lemma_olcons_raw [0uy] [0x13uy; 0x03uy]
    (Seq.append (B.of_list [0uy])
      (Seq.append (B.of_list [0uy; 46uy]) ext_flat));
  lemma_olcons_raw [0uy; 0x13uy; 0x03uy] [0uy]
    (Seq.append (B.of_list [0uy; 46uy]) ext_flat);
  lemma_olcons_raw [0uy; 0x13uy; 0x03uy; 0uy] [0uy; 46uy] ext_flat;
  lemma_olcons_raw [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy]
    [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]
    (Seq.append key sv);
  assert_norm (FStar.List.Tot.append [0uy] [0x13uy; 0x03uy] ==
    [0uy; 0x13uy; 0x03uy]);
  assert_norm (FStar.List.Tot.append [0uy; 0x13uy; 0x03uy] [0uy] ==
    [0uy; 0x13uy; 0x03uy; 0uy]);
  assert_norm (FStar.List.Tot.append [0uy; 0x13uy; 0x03uy; 0uy] [0uy; 46uy] ==
    [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy]);
  assert_norm (FStar.List.Tot.append
    [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy]
    [0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] ==
    [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]);
  let tail0 =
    Seq.append (B.of_list [0uy])
      (Seq.append (B.of_list [0x13uy; 0x03uy])
        (Seq.append (B.of_list [0uy])
          (Seq.append (B.of_list [0uy; 46uy]) ext_flat))) in
  let tail1 =
    Seq.append (B.of_list [0uy; 0x13uy; 0x03uy])
      (Seq.append (B.of_list [0uy])
        (Seq.append (B.of_list [0uy; 46uy]) ext_flat)) in
  let tail2 =
    Seq.append (B.of_list [0uy; 0x13uy; 0x03uy; 0uy])
      (Seq.append (B.of_list [0uy; 46uy]) ext_flat) in
  let tail3 =
    Seq.append (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy])
      ext_flat in
  let tail4 =
    Seq.append
      (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Seq.append key sv) in
  assert (Seq.equal tail0 tail1);
  assert (Seq.equal tail1 tail2);
  assert (Seq.equal tail2 tail3);
  assert (Seq.equal tail3 tail4);
  lemma_seq_equal_trans tail0 tail1 tail2;
  lemma_seq_equal_trans tail0 tail2 tail3;
  lemma_seq_equal_trans tail0 tail3 tail4;
  assert (Seq.equal
    (Seq.append
      (WS.u8 0)
      (Seq.append
        (WS.u16 0x1303)
        (Seq.append
          (WS.u8 0)
          (Seq.append
            (WS.u16 46)
            extensions))))
    tail0);
  Seq.lemma_eq_elim tail0 tail4;
  ()

private let lemma_ws_server_hello_body_bytes
  (sh:M.server_hello{sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256})
  : Lemma
      (Seq.equal
        (WS.serialize_server_hello sh)
        (Seq.append
          (B.of_list [0x03uy; 0x03uy])
          (Seq.append
            sh.M.random
            (Seq.append
              (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
              (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))))) /\
       B.length (WS.serialize_server_hello sh) == 86)
=
  let extensions =
    B.append (WS.server_key_share_extension sh.M.key_share)
             (WS.server_supported_versions_extension ()) in
  let flat_tail =
    Seq.append
      (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])) in
  lemma_ws_server_hello_extensions_len sh.M.key_share;
  assert (B.length extensions == 46);
  u16_literal 0x0303 0x03uy 0x03uy;
  assert (WS.cipher_suite_to_u16 sh.M.cipher_suite == 0x1303);
  lemma_ws_server_hello_tail_bytes sh.M.key_share;
  let tail =
    Seq.append
      (WS.u8 0)
      (Seq.append
        (WS.u16 (WS.cipher_suite_to_u16 sh.M.cipher_suite))
        (Seq.append
          (WS.u8 0)
          (Seq.append
            (WS.u16 (B.length extensions))
            extensions))) in
  assert (Seq.equal tail flat_tail);
  assert (WS.serialize_server_hello sh ==
    WS.append6
      (WS.u16 0x0303)
      sh.M.random
      (WS.u8 0)
      (WS.u16 (WS.cipher_suite_to_u16 sh.M.cipher_suite))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions));
  Seq.lemma_eq_elim (WS.u16 0x0303) (B.of_list [0x03uy; 0x03uy]);
  assert (Seq.equal
    (WS.serialize_server_hello sh)
    (Seq.append
      (B.of_list [0x03uy; 0x03uy])
      (Seq.append
        sh.M.random
        flat_tail)));
  Seq.lemma_len_append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]);
  Seq.lemma_len_append
    (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
    (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]));
  Seq.lemma_len_append
    sh.M.random
    (Seq.append
      (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
      (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])));
  Seq.lemma_len_append
    (B.of_list [0x03uy; 0x03uy])
    (Seq.append
      sh.M.random
      (Seq.append
        (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy]))));
  assert (B.length (WS.serialize_server_hello sh) == 86);
  ()

private let lemma_ws_server_hello_from_selection_shape
  (sh:M.server_hello{sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256})
  : Lemma (Seq.equal
      (WS.serialize_server_hello_from_selection sh)
      (B.append
        (B.of_list [2uy])
        (B.append
          (WS.u24 (B.length (WS.serialize_server_hello sh)))
          (WS.serialize_server_hello sh))))
=
  let body = WS.serialize_server_hello sh in
  lemma_ws_server_hello_body_bytes sh;
  u8_literal 2 2uy;
  assert (WS.serialize_server_hello_from_selection sh ==
          WS.append3 (WS.u8 2) (WS.u24 (B.length body)) body);
  Seq.lemma_eq_elim (WS.u8 2) (B.of_list [2uy]);
  ()
#pop-options

#push-options "--split_queries always --fuel 4 --ifuel 2 --z3rlimit 50"
let lemma_canonical_server_hello_key_scan
  (key:B.bytes_of_len 32)
  : Lemma
      (WSR.reveal_sh_key_share
        (canonical_server_hello_extensions key)
        false
        None == Some key)
=
  let ks = canonical_key_share_extension key in
  let sv = canonical_supported_versions_extension () in
  WSR.lemma_sh_key_share_cons ks [sv] false None;
  WSR.lemma_reveal_key_exchange_to_key32 (canonical_key_exchange key);
  WSR.lemma_sh_key_share_cons sv [] false (Some key);
  WSR.lemma_sh_key_share_nil true (Some key)
#pop-options

#push-options "--split_queries always --fuel 8 --ifuel 4 --z3rlimit 80"
let lemma_canonical_server_hello_low_serializes
  (sh:M.server_hello{B.length sh.M.body == 0 /\
                     sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256})
  : Lemma
      (Seq.equal
        (LP.serialize
          GHS.handshake_serializer
          (GHS.Body_server_hello (canonical_server_hello_low sh)))
        (WS.serialize_handshake (M.ServerHello sh)))
=
  let low = canonical_server_hello_low sh in
  let low_body = LP.serialize GSH.serverHello_serializer low in
  let ws_body = WS.serialize_server_hello sh in
  let flat =
    Seq.append
      (B.of_list [0x03uy; 0x03uy])
      (Seq.append
        sh.M.random
        (Seq.append
          (B.of_list [0uy; 0x13uy; 0x03uy; 0uy; 0uy; 46uy; 0uy; 0x33uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
          (Seq.append sh.M.key_share (B.of_list [0uy; 0x2buy; 0uy; 2uy; 0x03uy; 0x04uy])))) in
  lemma_lp_server_hello_low_bytes sh;
  lemma_ws_server_hello_body_bytes sh;
  assert (Seq.equal low_body flat);
  assert (Seq.equal ws_body flat);
  lemma_seq_equal_sym ws_body flat;
  lemma_seq_equal_trans low_body flat ws_body;
  assert (Seq.equal low_body ws_body);
  assert (B.length low_body == B.length ws_body);
  assert (B.length ws_body == 86);
  assert (B.length low_body == 86);
  assert (B.length low_body < 16777216);
  lemma_ghs_serialize_server_hello_shape low;
  Seq.lemma_eq_elim low_body ws_body;
  assert (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello low))
    (B.append
      (B.of_list [2uy])
      (B.append (WSR.u24 (B.length ws_body)) ws_body)));
  assert (B.length ws_body == 86);
  wsr_u24_literal 86 0uy 0uy 86uy;
  u24_literal 86 0uy 0uy 86uy;
  assert (Seq.equal (WSR.u24 (B.length ws_body)) (WSR.u24 86));
  assert (Seq.equal (WS.u24 (B.length ws_body)) (WS.u24 86));
  Seq.lemma_eq_elim (WSR.u24 (B.length ws_body)) (WSR.u24 86);
  Seq.lemma_eq_elim (WS.u24 (B.length ws_body)) (WS.u24 86);
  assert (Seq.equal (WSR.u24 (B.length ws_body)) (B.of_list [0uy; 0uy; 86uy]));
  assert (Seq.equal (WS.u24 (B.length ws_body)) (B.of_list [0uy; 0uy; 86uy]));
  lemma_seq_equal_sym (WS.u24 (B.length ws_body)) (B.of_list [0uy; 0uy; 86uy]);
  lemma_seq_equal_trans
    (WSR.u24 (B.length ws_body))
    (B.of_list [0uy; 0uy; 86uy])
    (WS.u24 (B.length ws_body));
  Seq.lemma_eq_elim (WSR.u24 (B.length ws_body)) (WS.u24 (B.length ws_body));
  assert (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello low))
    (B.append
      (B.of_list [2uy])
      (B.append (WS.u24 (B.length ws_body)) ws_body)));
  lemma_ws_server_hello_from_selection_shape sh;
  assert (WS.serialize_handshake (M.ServerHello sh) ==
          WS.serialize_server_hello_from_selection sh);
  lemma_seq_equal_sym
    (WS.serialize_server_hello_from_selection sh)
    (B.append
      (B.of_list [2uy])
      (B.append (WS.u24 (B.length ws_body)) ws_body));
  lemma_seq_equal_trans
    (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello low))
    (B.append
      (B.of_list [2uy])
      (B.append (WSR.u24 (B.length ws_body)) ws_body))
    (WS.serialize_server_hello_from_selection sh);
  Seq.lemma_eq_elim
    (WS.serialize_server_hello_from_selection sh)
    (WS.serialize_handshake (M.ServerHello sh));
  ()
#pop-options

#push-options "--split_queries always --fuel 8 --ifuel 4 --z3rlimit 100"
let lemma_parse_tls_message_serialize_server_hello_key_share
  (sh:M.server_hello{B.length sh.M.body == 0 /\
                     sh.M.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256})
  (parsed_sh:M.server_hello)
  : Lemma
      (requires
        WS.parse_tls_message
          T.Handshake
          (WS.serialize_handshake (M.ServerHello sh)) ==
          Some (M.TlsHandshake (M.ServerHello parsed_sh)))
      (ensures Seq.equal parsed_sh.M.key_share sh.M.key_share)
=
  let low = canonical_server_hello_low sh in
  let wire = LP.serialize GHS.handshake_serializer (GHS.Body_server_hello low) in
  lemma_canonical_server_hello_low_serializes sh;
  Seq.lemma_eq_elim wire (WS.serialize_handshake (M.ServerHello sh));
  LP.parse_serialize GHS.handshake_serializer (GHS.Body_server_hello low);
  assert (LP.parse GHS.handshake_parser wire ==
    Some (GHS.Body_server_hello low, B.length wire));
  match low.GSH.body with
  | GSHB.HelloRetryRequest shb ->
    WSR.lemma_handshake_synth_server_hello_hrr low shb;
    WSR.lemma_ptm_handshake_some wire (GHS.Body_server_hello low) M.HelloRetryRequest;
    assert (M.TlsHandshake M.HelloRetryRequest ==
      M.TlsHandshake (M.ServerHello parsed_sh));
    assert False
  | GSHB.ServerHello_body_false sf ->
    assert (sf.GSHB.value == canonical_server_hello_body sh);
    lemma_canonical_server_hello_key_scan sh.M.key_share;
    WSR.lemma_handshake_synth_server_hello_sh low sf;
    assert (WSR.handshake_synth (GHS.Body_server_hello low) ==
      Some (M.ServerHello ({
        M.random = (sf.GSHB.tag <: B.bytes_of_len 32);
        M.key_share = sh.M.key_share;
        M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
        M.body = wire
      })));
    WSR.lemma_ptm_handshake_some
      wire
      (GHS.Body_server_hello low)
      (M.ServerHello ({
        M.random = (sf.GSHB.tag <: B.bytes_of_len 32);
        M.key_share = sh.M.key_share;
        M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
        M.body = wire
      }));
    assert (M.TlsHandshake (M.ServerHello parsed_sh) ==
      M.TlsHandshake (M.ServerHello ({
        M.random = (sf.GSHB.tag <: B.bytes_of_len 32);
        M.key_share = sh.M.key_share;
        M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
        M.body = wire
      })));
    assert (parsed_sh.M.key_share == sh.M.key_share);
    Seq.lemma_eq_refl parsed_sh.M.key_share sh.M.key_share
#pop-options
