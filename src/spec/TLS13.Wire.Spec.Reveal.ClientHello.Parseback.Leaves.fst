module TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Leaves
friend TLS13.Wire.Generated.ProtocolVersion
friend TLS13.Wire.Generated.Random
friend TLS13.Wire.Generated.CipherSuite
friend TLS13.Wire.Generated.ClientHello_legacy_session_id
friend TLS13.Wire.Generated.ClientHello_cipher_suites
friend TLS13.Wire.Generated.ClientHello_legacy_compression_methods

module B = TLS13.Bytes
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.Spec
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GRandom = TLS13.Wire.Generated.Random
module GSID = TLS13.Wire.Generated.ClientHello_legacy_session_id
module GComp = TLS13.Wire.Generated.ClientHello_legacy_compression_methods
module GCS = TLS13.Wire.Generated.CipherSuite
module GCCS = TLS13.Wire.Generated.ClientHello_cipher_suites
module U = TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Util

let lemma_u16_parts_fit_raw = U.lemma_u16_parts_fit_raw
let lemma_u8_uint_to_t_eq_raw = U.lemma_u8_uint_to_t_eq_raw
let lemma_serialize_u16_bytes_raw = U.lemma_serialize_u16_bytes_raw
let lemma_of_list_append_raw = U.lemma_of_list_append_raw
let lemma_bounded_int_1_raw = U.lemma_bounded_int_1_raw
let lemma_bounded_int_2_fits_raw = U.lemma_bounded_int_2_fits_raw
let lemma_bounded_int_2_raw = U.lemma_bounded_int_2_raw
let lemma_vldata_strong_unfold_raw = U.lemma_vldata_strong_unfold_raw

/// Leaf field serializers

let lemma_lp_pv_tls12 ()
  : Lemma (Seq.equal (LP.serialize GPV.protocolVersion_serializer GPV.TLS_1p2)
                     (B.of_list [0x03uy; 0x03uy]))
=
  GPV.lemma_synth_protocolVersion_inj ();
  GPV.lemma_synth_protocolVersion_inv ();
  LP.serialize_synth_eq _ GPV.synth_protocolVersion GPV.serialize_protocolVersion_key GPV.synth_protocolVersion_inv () GPV.TLS_1p2;
  LP.serialize_enum_key_eq GPV.protocolVersion_repr_serializer GPV.protocolVersion_enum GPV.TLS_1p2;
  assert_norm (LP.enum_repr_of_key GPV.protocolVersion_enum GPV.TLS_1p2 == 771us);
  lemma_u16_parts_fit_raw 771us;
  lemma_serialize_u16_bytes_raw 771us

let lemma_lp_random (r:B.bytes{B.length r == 32})
  : Lemma (LP.serialize GRandom.random_serializer r == r)
= ()

let lemma_lp_session_id ()
  : Lemma (Seq.equal (LP.serialize GSID.clientHello_legacy_session_id_serializer B.empty)
                     (B.of_list [0uy]))
=
  assert_norm (LP.log256' 32 == 1);
  LP.serialize_bounded_seq_vlbytes_bytes_eq 0 32 B.empty;
  lemma_bounded_int_1_raw 0

let lemma_lp_cipher_suites ()
  : Lemma (Seq.equal (LP.serialize GCCS.clientHello_cipher_suites_serializer
                                   [GCS.TLS_CHACHA20_POLY1305_SHA256])
                     (B.of_list [0uy; 2uy; 0x13uy; 0x03uy]))
=
  let l : GCCS.clientHello_cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256] in
  LP.vldata_to_vlarray_inj 2 65534 GCS.cipherSuite_serializer 1 32767 ();
  LP.vlarray_to_vldata_to_vlarray 2 65534 GCS.cipherSuite_serializer 1 32767 ();
  LP.serialize_synth_eq _
    (LP.vldata_to_vlarray 2 65534 GCS.cipherSuite_serializer 1 32767 ())
    (LP.serialize_bounded_vldata_strong 2 65534 (LP.serialize_list _ GCS.cipherSuite_serializer))
    (LP.vlarray_to_vldata 2 65534 GCS.cipherSuite_serializer 1 32767 ())
    () l;
  LP.serialize_list_nil GCS.cipherSuite_parser GCS.cipherSuite_serializer;
  LP.serialize_list_cons GCS.cipherSuite_parser GCS.cipherSuite_serializer GCS.TLS_CHACHA20_POLY1305_SHA256 [];
  GCS.lemma_synth_cipherSuite_inj ();
  GCS.lemma_synth_cipherSuite_inv ();
  LP.serialize_synth_eq _ GCS.synth_cipherSuite GCS.serialize_maybe_cipherSuite_key GCS.synth_cipherSuite_inv () GCS.TLS_CHACHA20_POLY1305_SHA256;
  let chacha_key : LP.enum_key GCS.cipherSuite_enum = GCS.TLS_CHACHA20_POLY1305_SHA256 in
  let chacha_mkey : LP.maybe_enum_key GCS.cipherSuite_enum = LP.Known chacha_key in
  assert (GCS.synth_cipherSuite_inv GCS.TLS_CHACHA20_POLY1305_SHA256 == chacha_mkey);
  LP.serialize_maybe_enum_key_eq GCS.cipherSuite_repr_serializer GCS.cipherSuite_enum chacha_mkey;
  assert_norm (LP.enum_repr_of_key GCS.cipherSuite_enum GCS.TLS_CHACHA20_POLY1305_SHA256 == 4867us);
  assert (LP.repr_of_maybe_enum_key GCS.cipherSuite_enum chacha_mkey == 4867us);
  lemma_u16_parts_fit_raw 4867us;
  lemma_serialize_u16_bytes_raw 4867us;
  assert_norm (U16.v 4867us / 256 == 19);
  assert_norm (U16.v 4867us % 256 == 3);
  assert_norm (U8.v 0x13uy == 19);
  assert_norm (U8.v 0x03uy == 3);
  lemma_u8_uint_to_t_eq_raw 19 0x13uy;
  lemma_u8_uint_to_t_eq_raw 3 0x03uy;
  let vd = LP.vlarray_to_vldata 2 65534 GCS.cipherSuite_serializer 1 32767 () l in
  assert (vd == l);
  Seq.append_empty_r (B.of_list [0x13uy; 0x03uy]);
  assert (Seq.equal
    (LP.serialize (LP.serialize_list _ GCS.cipherSuite_serializer) vd)
    (B.of_list [0x13uy; 0x03uy]));
  Seq.lemma_eq_elim
    (LP.serialize (LP.serialize_list _ GCS.cipherSuite_serializer) vd)
    (B.of_list [0x13uy; 0x03uy]);
  lemma_vldata_strong_unfold_raw 2 65534 (LP.serialize_list _ GCS.cipherSuite_serializer) vd;
  assert_norm (LP.log256' 65534 == 2);
  lemma_bounded_int_2_fits_raw 2;
  assert_norm (2 / 256 == 0);
  assert_norm (2 % 256 == 2);
  assert_norm (U8.v 0uy == 0);
  assert_norm (U8.v 2uy == 2);
  assert (U32.fits 2);
  lemma_bounded_int_2_raw 2 0uy 2uy;
  Seq.lemma_eq_elim
    (LP.serialize (LP.serialize_bounded_integer (LP.log256' 65534)) (U32.uint_to_t 2))
    (B.of_list [0uy; 2uy]);
  assert (Seq.equal
    (LP.serialize (LP.serialize_bounded_vldata_strong 2 65534 (LP.serialize_list _ GCS.cipherSuite_serializer)) vd)
    (Seq.append (B.of_list [0uy; 2uy]) (B.of_list [0x13uy; 0x03uy])));
  assert (Seq.equal
    (LP.serialize GCCS.clientHello_cipher_suites_serializer l)
    (LP.serialize (LP.serialize_bounded_vldata_strong 2 65534 (LP.serialize_list _ GCS.cipherSuite_serializer)) vd));
  assert (Seq.equal
    (LP.serialize GCCS.clientHello_cipher_suites_serializer l)
    (Seq.append (B.of_list [0uy; 2uy]) (B.of_list [0x13uy; 0x03uy])));
  lemma_of_list_append_raw [0uy; 2uy] [0x13uy; 0x03uy]

let lemma_lp_compression ()
  : Lemma (Seq.equal (LP.serialize GComp.clientHello_legacy_compression_methods_serializer
                                   (B.of_list [0uy]))
                     (B.of_list [1uy; 0uy]))
=
  let y : GComp.clientHello_legacy_compression_methods = Seq.create 1 0uy in
  Seq.lemma_create_len 1 0uy;
  Seq.lemma_index_create 1 0uy 0;
  Seq.lemma_seq_of_list_induction [0uy];
  SeqP.lemma_seq_of_list_index [0uy] 0;
  assert_norm (FStar.List.Tot.index [0uy] 0 == 0uy);
  assert (Seq.length y == Seq.length (B.of_list [0uy]));
  assert (Seq.index y 0 == Seq.index (B.of_list [0uy]) 0);
  Seq.lemma_eq_intro y (B.of_list [0uy]);
  Seq.lemma_eq_elim y (B.of_list [0uy]);
  assert_norm (LP.log256' 255 == 1);
  assert (Seq.length y == 1);
  LP.serialize_bounded_seq_vlbytes_bytes_eq 1 255 y;
  assert (U8.fits 1);
  assert_norm (pow2 32 == 4294967296);
  assert (1 < 4294967296);
  assert (U32.fits 1);
  assert_norm (U8.v 1uy == 1);
  lemma_u8_uint_to_t_eq_raw 1 1uy;
  lemma_bounded_int_1_raw 1;
  Seq.lemma_eq_elim
    (LP.serialize (LP.serialize_bounded_integer (LP.log256' 255)) (U32.uint_to_t 1))
    (B.of_list [1uy]);
  lemma_of_list_append_raw [1uy] [0uy]
