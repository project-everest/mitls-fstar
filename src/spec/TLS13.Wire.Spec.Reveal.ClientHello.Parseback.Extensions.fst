module TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Extensions
friend TLS13.Wire.Generated.ProtocolVersion
friend TLS13.Wire.Generated.ExtensionType
friend TLS13.Wire.Generated.NameType
friend TLS13.Wire.Generated.HostName
friend TLS13.Wire.Generated.ServerName
friend TLS13.Wire.Generated.ServerNameList
friend TLS13.Wire.Generated.NamedGroup
friend TLS13.Wire.Generated.NamedGroupList
friend TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_groups
friend TLS13.Wire.Generated.SignatureScheme
friend TLS13.Wire.Generated.SignatureSchemeList
friend TLS13.Wire.Generated.ExtensionClientHello_extension_data_signature_algorithms
friend TLS13.Wire.Generated.KeyShareEntry_key_exchange
friend TLS13.Wire.Generated.KeyShareEntry
friend TLS13.Wire.Generated.KeyShareClientHello
friend TLS13.Wire.Generated.ExtensionClientHello_extension_data_key_share
friend TLS13.Wire.Generated.SupportedVersionsClientHello
friend TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_versions
friend TLS13.Wire.Generated.ExtensionClientHello_extension_data_default
friend TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
friend TLS13.Wire.Generated.ExtensionClientHello

module B = TLS13.Bytes
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.Spec
module RCH = TLS13.Wire.Spec.Reveal.ClientHello
module GET = TLS13.Wire.Generated.ExtensionType
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GSG = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_groups
module GNGL = TLS13.Wire.Generated.NamedGroupList
module GNG = TLS13.Wire.Generated.NamedGroup
module GSS = TLS13.Wire.Generated.SignatureScheme
module GSSL = TLS13.Wire.Generated.SignatureSchemeList
module GSA = TLS13.Wire.Generated.ExtensionClientHello_extension_data_signature_algorithms
module GSV = TLS13.Wire.Generated.SupportedVersionsClientHello
module GSVE = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_versions
module GKSEKE = TLS13.Wire.Generated.KeyShareEntry_key_exchange
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GKSCH = TLS13.Wire.Generated.KeyShareClientHello
module GKS = TLS13.Wire.Generated.ExtensionClientHello_extension_data_key_share
module GNT = TLS13.Wire.Generated.NameType
module GHN = TLS13.Wire.Generated.HostName
module GSNM = TLS13.Wire.Generated.ServerName
module GSNL = TLS13.Wire.Generated.ServerNameList
module GSNE = TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
module GPV = TLS13.Wire.Generated.ProtocolVersion
module U = TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Util

let client_hello_byte n = RCH.client_hello_byte n
let client_hello_server_name_extension_bytes hostname = RCH.client_hello_server_name_extension_bytes hostname
let lemma_u16_parts_fit_raw = U.lemma_u16_parts_fit_raw
let lemma_u8_uint_to_t_eq_raw = U.lemma_u8_uint_to_t_eq_raw
let lemma_u16_uint_to_t_eq_raw = U.lemma_u16_uint_to_t_eq_raw
let lemma_serialize_u16_bytes_raw = U.lemma_serialize_u16_bytes_raw
let lemma_of_list_append_raw = U.lemma_of_list_append_raw
let lemma_bounded_int_1_raw = U.lemma_bounded_int_1_raw
let lemma_bounded_int_2_fits_raw = U.lemma_bounded_int_2_fits_raw
let lemma_bounded_int_2_raw = U.lemma_bounded_int_2_raw
let lemma_vldata_strong_unfold_raw = U.lemma_vldata_strong_unfold_raw
let lemma_vlarray_unfold_raw = U.lemma_vlarray_unfold_raw
let lemma_vldata_unfold_raw = U.lemma_vldata_unfold_raw
let lemma_olcons_raw = U.lemma_olcons_raw

/// Concrete extension bytes

#push-options "--fuel 8 --ifuel 8 --z3rlimit 100"
private let lemma_lp_extension_bytes_raw
  (x: GECH.extensionClientHello)
  (k: LP.dsum_known_key GECH.extensionClientHello_sum)
  (tag_bytes payload: Seq.seq U8.t)
  : Lemma
    (requires
      LP.dsum_tag_of_data GECH.extensionClientHello_sum x == LP.Known k /\
      Seq.equal
        (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                        (LP.dsum_enum GECH.extensionClientHello_sum)) (LP.Known k))
        tag_bytes /\
      Seq.equal
        (LP.serialize (GECH.serialize_extensionClientHello_cases k)
                      (LP.synth_dsum_case_recip GECH.extensionClientHello_sum (LP.Known k) x))
        payload)
    (ensures Seq.equal (LP.serialize GECH.extensionClientHello_serializer x)
                       (Seq.append tag_bytes payload))
=
  LP.serialize_dsum_eq
    GECH.extensionClientHello_sum
    GET.extensionType_repr_serializer
    GECH.parse_extensionClientHello_cases
    GECH.serialize_extensionClientHello_cases
    GECH.extensionClientHello_extension_data_default_parser
    GECH.extensionClientHello_extension_data_default_serializer
    x
#pop-options

private let lemma_lp_ext_tag_raw (k: LP.dsum_known_key GECH.extensionClientHello_sum) (repr:U16.t)
  : Lemma
      (requires
        LP.repr_of_maybe_enum_key (LP.dsum_enum GECH.extensionClientHello_sum) (LP.Known k) == repr /\
        U8.fits (U16.v repr / 256) /\
        U8.fits (U16.v repr % 256))
      (ensures Seq.equal
        (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                        (LP.dsum_enum GECH.extensionClientHello_sum)) (LP.Known k))
        (B.of_list [U8.uint_to_t (U16.v repr / 256); U8.uint_to_t (U16.v repr % 256)]))
=
  LP.serialize_maybe_enum_key_eq GET.extensionType_repr_serializer (LP.dsum_enum GECH.extensionClientHello_sum) (LP.Known k);
  lemma_u16_parts_fit_raw repr;
  lemma_serialize_u16_bytes_raw repr

#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_lp_sg_extension ()
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer (GECH.Extension_data_supported_groups [GNG.X25519]))
                     (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]))
=
  let x : GECH.extensionClientHello = GECH.Extension_data_supported_groups [GNG.X25519] in
  let sum = GECH.extensionClientHello_sum in
  assert_norm (LP.dsum_tag_of_data sum x == LP.Known GET.Supported_groups);
  assert_norm (LP.repr_of_maybe_enum_key (LP.dsum_enum sum) (LP.Known GET.Supported_groups) == 10us);
  lemma_u16_parts_fit_raw 10us;
  lemma_lp_ext_tag_raw GET.Supported_groups 10us;
  assert_norm (U16.v 10us / 256 == 0);
  assert_norm (U16.v 10us % 256 == 10);
  assert_norm (U8.v 0uy == 0);
  assert_norm (U8.v 0x0auy == 10);
  lemma_u8_uint_to_t_eq_raw 0 0uy;
  lemma_u8_uint_to_t_eq_raw 10 0x0auy;
  assert (Seq.equal
    (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                    (LP.dsum_enum GECH.extensionClientHello_sum)) (LP.Known GET.Supported_groups))
    (B.of_list [0uy; 0x0auy]));
  assert_norm (LP.synth_dsum_case_recip sum (LP.Known GET.Supported_groups) x == [GNG.X25519]);
  // payload
  GNG.lemma_synth_namedGroup_inj ();
  GNG.lemma_synth_namedGroup_inv ();
  LP.serialize_synth_eq _ GNG.synth_namedGroup GNG.serialize_maybe_namedGroup_key GNG.synth_namedGroup_inv () GNG.X25519;
  assert_norm (GNG.synth_namedGroup_inv GNG.X25519 == LP.Known GNG.X25519);
  LP.serialize_maybe_enum_key_eq GNG.namedGroup_repr_serializer GNG.namedGroup_enum (LP.Known GNG.X25519);
  assert_norm (LP.repr_of_maybe_enum_key GNG.namedGroup_enum (LP.Known GNG.X25519) == 29us);
  lemma_u16_parts_fit_raw 29us;
  lemma_serialize_u16_bytes_raw 29us;
  assert_norm (U16.v 29us / 256 == 0);
  assert_norm (U16.v 29us % 256 == 29);
  assert_norm (U8.v 0x1duy == 29);
  lemma_u8_uint_to_t_eq_raw 29 0x1duy;
  assert (Seq.equal (LP.serialize GNG.namedGroup_serializer GNG.X25519)
                    (B.of_list [0uy; 0x1duy]));
  Seq.lemma_eq_elim (LP.serialize GNG.namedGroup_serializer GNG.X25519)
                    (B.of_list [0uy; 0x1duy]);
  // namedGroupList [X25519]
  let l : GNGL.namedGroupList = [GNG.X25519] in
  lemma_vlarray_unfold_raw 2 65535 GNG.namedGroup_serializer 1 32767 () l;
  let vd = LP.vlarray_to_vldata 2 65535 GNG.namedGroup_serializer 1 32767 () l in
  assert (vd == l);
  LP.serialize_list_nil GNG.namedGroup_parser GNG.namedGroup_serializer;
  LP.serialize_list_cons GNG.namedGroup_parser GNG.namedGroup_serializer GNG.X25519 [];
  assert_norm (LP.log256' 65535 == 2);
  lemma_bounded_int_2_fits_raw 2;
  lemma_bounded_int_2_raw 2 0uy 2uy;
  assert (Seq.equal
    (LP.serialize GNGL.namedGroupList_serializer l)
    (Seq.append (B.of_list [0uy; 2uy]) (B.of_list [0uy; 0x1duy])));
  lemma_of_list_append_raw [0uy; 2uy] [0uy; 0x1duy];
  assert (Seq.equal (LP.serialize GNGL.namedGroupList_serializer l)
                    (B.of_list [0uy; 2uy; 0uy; 0x1duy]));
  Seq.lemma_eq_elim (LP.serialize GNGL.namedGroupList_serializer l)
                    (B.of_list [0uy; 2uy; 0uy; 0x1duy]);
  // extensionClientHello_extension_data_supported_groups
  let v : GSG.extensionClientHello_extension_data_supported_groups = [GNG.X25519] in
  LP.serialize_synth_eq _
    GSG.synth_extensionClientHello_extension_data_supported_groups
    GSG.extensionClientHello_extension_data_supported_groups'_serializer
    GSG.synth_extensionClientHello_extension_data_supported_groups_recip
    () v;
  assert (GSG.synth_extensionClientHello_extension_data_supported_groups_recip v == v);
  lemma_vldata_strong_unfold_raw 0 65535 GNGL.namedGroupList_serializer v;
  lemma_bounded_int_2_fits_raw 4;
  lemma_bounded_int_2_raw 4 0uy 4uy;
  assert (Seq.equal
    (LP.serialize GSG.extensionClientHello_extension_data_supported_groups_serializer v)
    (Seq.append (B.of_list [0uy; 4uy]) (B.of_list [0uy; 2uy; 0uy; 0x1duy])));
  lemma_of_list_append_raw [0uy; 4uy] [0uy; 2uy; 0uy; 0x1duy];
  assert (Seq.equal
    (LP.serialize GSG.extensionClientHello_extension_data_supported_groups_serializer v)
    (B.of_list [0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]));
  // final
  assert (GECH.serialize_extensionClientHello_cases GET.Supported_groups
          == GSG.extensionClientHello_extension_data_supported_groups_serializer);
  lemma_lp_extension_bytes_raw x GET.Supported_groups
    (B.of_list [0uy; 0x0auy])
    (B.of_list [0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]);
  assert_norm (FStar.List.Tot.append [0uy; 0x0auy] [0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]
               == [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]);
  lemma_of_list_append_raw [0uy; 0x0auy] [0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]
#pop-options

#restart-solver

#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_lp_sa_extension ()
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer (GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256]))
                     (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]))
=
  let x : GECH.extensionClientHello = GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256] in
  let sum = GECH.extensionClientHello_sum in
  assert_norm (LP.dsum_tag_of_data sum x == LP.Known GET.Signature_algorithms);
  assert_norm (LP.repr_of_maybe_enum_key (LP.dsum_enum sum) (LP.Known GET.Signature_algorithms) == 13us);
  lemma_u16_parts_fit_raw 13us;
  lemma_lp_ext_tag_raw GET.Signature_algorithms 13us;
  assert_norm (U16.v 13us / 256 == 0);
  assert_norm (U16.v 13us % 256 == 13);
  assert_norm (U8.v 0x0duy == 13);
  lemma_u8_uint_to_t_eq_raw 13 0x0duy;
  assert (Seq.equal
    (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                    (LP.dsum_enum GECH.extensionClientHello_sum)) (LP.Known GET.Signature_algorithms))
    (B.of_list [0uy; 0x0duy]));
  assert_norm (LP.synth_dsum_case_recip sum (LP.Known GET.Signature_algorithms) x == [GSS.Rsa_pss_rsae_sha256]);
  // signatureScheme
  GSS.lemma_synth_signatureScheme_inj ();
  GSS.lemma_synth_signatureScheme_inv ();
  LP.serialize_synth_eq _ GSS.synth_signatureScheme GSS.serialize_maybe_signatureScheme_key GSS.synth_signatureScheme_inv () GSS.Rsa_pss_rsae_sha256;
  assert_norm (GSS.synth_signatureScheme_inv GSS.Rsa_pss_rsae_sha256 == LP.Known GSS.Rsa_pss_rsae_sha256);
  LP.serialize_maybe_enum_key_eq GSS.signatureScheme_repr_serializer GSS.signatureScheme_enum (LP.Known GSS.Rsa_pss_rsae_sha256);
  assert_norm (LP.repr_of_maybe_enum_key GSS.signatureScheme_enum (LP.Known GSS.Rsa_pss_rsae_sha256) == 2052us);
  lemma_u16_parts_fit_raw 2052us;
  lemma_serialize_u16_bytes_raw 2052us;
  assert_norm (U16.v 2052us / 256 == 8);
  assert_norm (U16.v 2052us % 256 == 4);
  assert_norm (U8.v 0x08uy == 8);
  assert_norm (U8.v 0x04uy == 4);
  lemma_u8_uint_to_t_eq_raw 8 0x08uy;
  lemma_u8_uint_to_t_eq_raw 4 0x04uy;
  assert (Seq.equal (LP.serialize GSS.signatureScheme_serializer GSS.Rsa_pss_rsae_sha256)
                    (B.of_list [0x08uy; 0x04uy]));
  Seq.lemma_eq_elim (LP.serialize GSS.signatureScheme_serializer GSS.Rsa_pss_rsae_sha256)
                    (B.of_list [0x08uy; 0x04uy]);
  // signatureSchemeList [Rsa_pss_rsae_sha256]
  let l : GSSL.signatureSchemeList = [GSS.Rsa_pss_rsae_sha256] in
  lemma_vlarray_unfold_raw 2 65534 GSS.signatureScheme_serializer 1 32767 () l;
  let vd = LP.vlarray_to_vldata 2 65534 GSS.signatureScheme_serializer 1 32767 () l in
  assert (vd == l);
  LP.serialize_list_nil GSS.signatureScheme_parser GSS.signatureScheme_serializer;
  LP.serialize_list_cons GSS.signatureScheme_parser GSS.signatureScheme_serializer GSS.Rsa_pss_rsae_sha256 [];
  assert_norm (LP.log256' 65534 == 2);
  lemma_bounded_int_2_fits_raw 2;
  lemma_bounded_int_2_raw 2 0uy 2uy;
  assert (Seq.equal
    (LP.serialize GSSL.signatureSchemeList_serializer l)
    (Seq.append (B.of_list [0uy; 2uy]) (B.of_list [0x08uy; 0x04uy])));
  lemma_of_list_append_raw [0uy; 2uy] [0x08uy; 0x04uy];
  assert (Seq.equal (LP.serialize GSSL.signatureSchemeList_serializer l)
                    (B.of_list [0uy; 2uy; 0x08uy; 0x04uy]));
  Seq.lemma_eq_elim (LP.serialize GSSL.signatureSchemeList_serializer l)
                    (B.of_list [0uy; 2uy; 0x08uy; 0x04uy]);
  // ext payload
  let v : GSA.extensionClientHello_extension_data_signature_algorithms = [GSS.Rsa_pss_rsae_sha256] in
  LP.serialize_synth_eq _
    GSA.synth_extensionClientHello_extension_data_signature_algorithms
    GSA.extensionClientHello_extension_data_signature_algorithms'_serializer
    GSA.synth_extensionClientHello_extension_data_signature_algorithms_recip
    () v;
  assert (GSA.synth_extensionClientHello_extension_data_signature_algorithms_recip v == v);
  lemma_vldata_strong_unfold_raw 0 65535 GSSL.signatureSchemeList_serializer v;
  lemma_bounded_int_2_fits_raw 4;
  lemma_bounded_int_2_raw 4 0uy 4uy;
  assert (Seq.equal
    (LP.serialize GSA.extensionClientHello_extension_data_signature_algorithms_serializer v)
    (Seq.append (B.of_list [0uy; 4uy]) (B.of_list [0uy; 2uy; 0x08uy; 0x04uy])));
  lemma_of_list_append_raw [0uy; 4uy] [0uy; 2uy; 0x08uy; 0x04uy];
  assert (Seq.equal
    (LP.serialize GSA.extensionClientHello_extension_data_signature_algorithms_serializer v)
    (B.of_list [0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]));
  // final
  assert (GECH.serialize_extensionClientHello_cases GET.Signature_algorithms
          == GSA.extensionClientHello_extension_data_signature_algorithms_serializer);
  lemma_lp_extension_bytes_raw x GET.Signature_algorithms
    (B.of_list [0uy; 0x0duy])
    (B.of_list [0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]);
  assert_norm (FStar.List.Tot.append [0uy; 0x0duy] [0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]
               == [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]);
  lemma_of_list_append_raw [0uy; 0x0duy] [0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]
#pop-options

#restart-solver

#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_lp_sv_extension ()
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer
                        (GECH.Extension_data_supported_versions [GPV.TLS_1p3]))
                     (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]))
=
  let x : GECH.extensionClientHello = GECH.Extension_data_supported_versions [GPV.TLS_1p3] in
  let sum = GECH.extensionClientHello_sum in
  assert_norm (LP.dsum_tag_of_data sum x == LP.Known GET.Supported_versions);
  let sv_tag = LP.repr_of_maybe_enum_key (LP.dsum_enum sum) (LP.Known GET.Supported_versions) in
  LP.enum_key_of_repr_of_key (LP.dsum_enum sum) GET.Supported_versions;
  assert_norm (LP.enum_repr_of_key (LP.dsum_enum sum) GET.Supported_versions == 43us);
  assert (sv_tag == LP.enum_repr_of_key (LP.dsum_enum sum) GET.Supported_versions);
  assert_norm (U16.v sv_tag == 43);
  assert (U16.v sv_tag == 43);
  assert (U16.fits 43);
  assert_norm (U16.v 43us == 43);
  lemma_u16_uint_to_t_eq_raw 43 43us;
  U16.uv_inv sv_tag;
  assert (sv_tag == 43us);
  lemma_u16_parts_fit_raw 43us;
  lemma_lp_ext_tag_raw GET.Supported_versions 43us;
  assert_norm (U16.v 43us / 256 == 0);
  assert_norm (U16.v 43us % 256 == 43);
  assert (U8.fits 43);
  assert_norm (U8.v 0uy == 0);
  assert_norm (U8.v 0x2buy == 43);
  lemma_u8_uint_to_t_eq_raw 0 0uy;
  lemma_u8_uint_to_t_eq_raw 43 0x2buy;
  Seq.lemma_eq_elim
    (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                    (LP.dsum_enum GECH.extensionClientHello_sum)) (LP.Known GET.Supported_versions))
    (B.of_list [U8.uint_to_t (U16.v 43us / 256); U8.uint_to_t (U16.v 43us % 256)]);
  assert (Seq.equal
    (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                    (LP.dsum_enum GECH.extensionClientHello_sum)) (LP.Known GET.Supported_versions))
    (B.of_list [0uy; 0x2buy]));
  assert_norm (LP.synth_dsum_case_recip sum (LP.Known GET.Supported_versions) x == [GPV.TLS_1p3]);
  // protocolVersion TLS_1p3
  GPV.lemma_synth_protocolVersion_inj ();
  GPV.lemma_synth_protocolVersion_inv ();
  LP.serialize_synth_eq _ GPV.synth_protocolVersion GPV.serialize_protocolVersion_key GPV.synth_protocolVersion_inv () GPV.TLS_1p3;
  LP.serialize_enum_key_eq GPV.protocolVersion_repr_serializer GPV.protocolVersion_enum GPV.TLS_1p3;
  assert_norm (LP.enum_repr_of_key GPV.protocolVersion_enum GPV.TLS_1p3 == 772us);
  lemma_u16_parts_fit_raw 772us;
  lemma_serialize_u16_bytes_raw 772us;
  assert_norm (U16.v 772us / 256 == 3);
  assert_norm (U16.v 772us % 256 == 4);
  assert_norm (U8.v 0x03uy == 3);
  assert_norm (U8.v 0x04uy == 4);
  lemma_u8_uint_to_t_eq_raw 3 0x03uy;
  lemma_u8_uint_to_t_eq_raw 4 0x04uy;
  assert (Seq.equal (LP.serialize GPV.protocolVersion_serializer GPV.TLS_1p3)
                    (B.of_list [0x03uy; 0x04uy]));
  Seq.lemma_eq_elim (LP.serialize GPV.protocolVersion_serializer GPV.TLS_1p3)
                    (B.of_list [0x03uy; 0x04uy]);
  // supportedVersionsClientHello [TLS_1p3]
  let l : GSV.supportedVersionsClientHello = [GPV.TLS_1p3] in
  lemma_vlarray_unfold_raw 2 254 GPV.protocolVersion_serializer 1 127 () l;
  let vd = LP.vlarray_to_vldata 2 254 GPV.protocolVersion_serializer 1 127 () l in
  assert (vd == l);
  LP.serialize_list_nil GPV.protocolVersion_parser GPV.protocolVersion_serializer;
  LP.serialize_list_cons GPV.protocolVersion_parser GPV.protocolVersion_serializer GPV.TLS_1p3 [];
  assert_norm (LP.log256' 254 == 1);
  assert (U8.fits 2);
  assert_norm (pow2 32 == 4294967296);
  assert (2 < 4294967296);
  assert (U32.fits 2);
  let two : nat = 2 in
  lemma_bounded_int_1_raw two;
  assert_norm (U8.v 2uy == 2);
  lemma_u8_uint_to_t_eq_raw 2 2uy;
  assert (Seq.equal
    (LP.serialize GSV.supportedVersionsClientHello_serializer l)
    (Seq.append (B.of_list [2uy]) (B.of_list [0x03uy; 0x04uy])));
  lemma_of_list_append_raw [2uy] [0x03uy; 0x04uy];
  assert (Seq.equal (LP.serialize GSV.supportedVersionsClientHello_serializer l)
                    (B.of_list [2uy; 0x03uy; 0x04uy]));
  Seq.lemma_eq_elim (LP.serialize GSV.supportedVersionsClientHello_serializer l)
                    (B.of_list [2uy; 0x03uy; 0x04uy]);
  // ext payload
  let v : GSVE.extensionClientHello_extension_data_supported_versions = [GPV.TLS_1p3] in
  lemma_vldata_unfold_raw 0 65535 GSV.supportedVersionsClientHello_serializer v;
  assert_norm (LP.log256' 65535 == 2);
  lemma_bounded_int_2_fits_raw 3;
  lemma_bounded_int_2_raw 3 0uy 3uy;
  assert (Seq.equal
    (LP.serialize GSVE.extensionClientHello_extension_data_supported_versions_serializer v)
    (Seq.append (B.of_list [0uy; 3uy]) (B.of_list [2uy; 0x03uy; 0x04uy])));
  lemma_of_list_append_raw [0uy; 3uy] [2uy; 0x03uy; 0x04uy];
  assert (Seq.equal
    (LP.serialize GSVE.extensionClientHello_extension_data_supported_versions_serializer v)
    (B.of_list [0uy; 3uy; 2uy; 0x03uy; 0x04uy]));
  // final
  assert (GECH.serialize_extensionClientHello_cases GET.Supported_versions
          == GSVE.extensionClientHello_extension_data_supported_versions_serializer);
  lemma_lp_extension_bytes_raw x GET.Supported_versions
    (B.of_list [0uy; 0x2buy])
    (B.of_list [0uy; 3uy; 2uy; 0x03uy; 0x04uy]);
  assert_norm (FStar.List.Tot.append [0uy; 0x2buy] [0uy; 3uy; 2uy; 0x03uy; 0x04uy]
               == [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]);
  lemma_of_list_append_raw [0uy; 0x2buy] [0uy; 3uy; 2uy; 0x03uy; 0x04uy]
#pop-options

#restart-solver

#push-options "--fuel 8 --ifuel 8 --z3rlimit 100"
let lemma_lp_ks_extension (key: GKSEKE.keyShareEntry_key_exchange{Seq.length key == 32})
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer
                        (GECH.Extension_data_key_share ([ { GKSE.group = GNG.X25519; GKSE.key_exchange = key } ])))
                     (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key))
=
  let e : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key } in
  let x : GECH.extensionClientHello = GECH.Extension_data_key_share [e] in
  let sum = GECH.extensionClientHello_sum in
  assert_norm (LP.dsum_tag_of_data sum x == LP.Known GET.Key_share);
  assert_norm (LP.repr_of_maybe_enum_key (LP.dsum_enum sum) (LP.Known GET.Key_share) == 51us);
  lemma_u16_parts_fit_raw 51us;
  lemma_lp_ext_tag_raw GET.Key_share 51us;
  assert_norm (U16.v 51us / 256 == 0);
  assert_norm (U16.v 51us % 256 == 51);
  assert_norm (U8.v 0uy == 0);
  assert_norm (U8.v 0x33uy == 51);
  lemma_u8_uint_to_t_eq_raw 0 0uy;
  lemma_u8_uint_to_t_eq_raw 51 0x33uy;
  assert (Seq.equal
    (LP.serialize (LP.serialize_maybe_enum_key _ GET.extensionType_repr_serializer
                    (LP.dsum_enum GECH.extensionClientHello_sum)) (LP.Known GET.Key_share))
    (B.of_list [0uy; 0x33uy]));
  assert_norm (LP.synth_dsum_case_recip sum (LP.Known GET.Key_share) x == [e]);
  // keyShareEntry bytes
  GNG.lemma_synth_namedGroup_inj ();
  GNG.lemma_synth_namedGroup_inv ();
  LP.serialize_synth_eq _ GNG.synth_namedGroup GNG.serialize_maybe_namedGroup_key GNG.synth_namedGroup_inv () GNG.X25519;
  assert_norm (GNG.synth_namedGroup_inv GNG.X25519 == LP.Known GNG.X25519);
  LP.serialize_maybe_enum_key_eq GNG.namedGroup_repr_serializer GNG.namedGroup_enum (LP.Known GNG.X25519);
  assert_norm (LP.repr_of_maybe_enum_key GNG.namedGroup_enum (LP.Known GNG.X25519) == 29us);
  lemma_u16_parts_fit_raw 29us;
  lemma_serialize_u16_bytes_raw 29us;
  // key_exchange bytes: u16(32) ++ key
  assert_norm (LP.log256' 65535 == 2);
  LP.serialize_bounded_seq_vlbytes_bytes_eq 1 65535 key;
  lemma_bounded_int_2_fits_raw 32;
  lemma_bounded_int_2_raw 32 0uy 32uy;
  // keyShareEntry = namedGroup ++ key_exchange
  GKSE.synth_keyShareEntry_injective ();
  GKSE.synth_keyShareEntry_inverse ();
  LP.serialize_synth_eq _ GKSE.synth_keyShareEntry GKSE.keyShareEntry'_serializer GKSE.synth_keyShareEntry_recip () e;
  assert (GKSE.synth_keyShareEntry_recip e == (GNG.X25519, key));
  LP.serialize_nondep_then_eq GNG.namedGroup_serializer GKSE.keyShareEntry_key_exchange_serializer (GNG.X25519, key);
  lemma_of_list_append_raw [0uy; 0x1duy] [0uy; 32uy];
  Seq.append_assoc (B.of_list [0uy; 0x1duy]) (B.of_list [0uy; 32uy]) key;
  // keyShareClientHello [e]
  let l : GKSCH.keyShareClientHello = [e] in
  assert_norm (LP.synth_injective GKSCH.synth_keyShareClientHello);
  assert_norm (LP.synth_inverse GKSCH.synth_keyShareClientHello GKSCH.synth_keyShareClientHello_recip);
  LP.serialize_synth_eq _ GKSCH.synth_keyShareClientHello GKSCH.keyShareClientHello'_serializer GKSCH.synth_keyShareClientHello_recip () l;
  assert (GKSCH.synth_keyShareClientHello_recip l == l);
  LP.serialize_list_nil GKSE.keyShareEntry_parser GKSE.keyShareEntry_serializer;
  LP.serialize_list_cons GKSE.keyShareEntry_parser GKSE.keyShareEntry_serializer e [];
  lemma_vldata_strong_unfold_raw 0 65535 (LP.serialize_list _ GKSE.keyShareEntry_serializer) l;
  lemma_bounded_int_2_fits_raw 36;
  lemma_bounded_int_2_raw 36 0uy 36uy;
  lemma_of_list_append_raw [0uy; 36uy] [0uy; 0x1duy; 0uy; 32uy];
  Seq.append_assoc (B.of_list [0uy; 36uy]) (B.of_list [0uy; 0x1duy; 0uy; 32uy]) key;
  // ext payload = u16(38) ++ ksch_bytes
  let v : GKS.extensionClientHello_extension_data_key_share = [e] in
  GKS.extensionClientHello_extension_data_key_share_copyful_synth_injective ();
  GKS.extensionClientHello_extension_data_key_share_copyful_synth_inverse ();
  LP.serialize_synth_eq _
    GKS.synth_extensionClientHello_extension_data_key_share
    GKS.extensionClientHello_extension_data_key_share'_serializer
    GKS.synth_extensionClientHello_extension_data_key_share_recip
    () v;
  assert (GKS.synth_extensionClientHello_extension_data_key_share_recip v == v);
  lemma_vldata_strong_unfold_raw 0 65535 GKSCH.keyShareClientHello_serializer v;
  lemma_bounded_int_2_fits_raw 38;
  lemma_bounded_int_2_raw 38 0uy 38uy;
  lemma_of_list_append_raw [0uy; 38uy] [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy];
  Seq.append_assoc (B.of_list [0uy; 38uy]) (B.of_list [0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key;
  // full extension
  assert (GECH.serialize_extensionClientHello_cases GET.Key_share
          == GKS.extensionClientHello_extension_data_key_share_serializer);
  lemma_lp_extension_bytes_raw x GET.Key_share
    (B.of_list [0uy; 0x33uy])
    (Seq.append (B.of_list [0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key);
  lemma_of_list_append_raw [0uy; 0x33uy] [0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy];
  Seq.append_assoc (B.of_list [0uy; 0x33uy]) (B.of_list [0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key
#pop-options

#restart-solver

(* Smart constructors that discharge the bytesize refinements for ServerName *)
let mk_snl (hn: GHN.hostName{Seq.length hn <= 255}) : GSNL.serverNameList =
  let _ = GSNL.serverNameList_list_bytesize_nil in
  [ GSNM.Name_host_name hn ]

let mk_sne (hn: GHN.hostName{Seq.length hn <= 255})
  : GSNE.extensionClientHello_extension_data_server_name =
  let _ = GSNL.serverNameList_list_bytesize_nil in
  mk_snl hn

#push-options "--fuel 4 --ifuel 4 --z3rlimit 100 --split_queries always"
let lemma_lp_sn_extension (hn: GHN.hostName{Seq.length hn <= 255 /\ Seq.length hn > 0})
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer
                        (GECH.Extension_data_server_name (mk_sne hn)))
                     (client_hello_server_name_extension_bytes hn))
=
  // tag bytes: [0;0]
  let x : GECH.extensionClientHello = GECH.Extension_data_server_name (mk_sne hn) in
  let sum = GECH.extensionClientHello_sum in
  assert_norm (LP.dsum_tag_of_data sum x == LP.Known GET.Server_name);
  assert_norm (LP.repr_of_maybe_enum_key (LP.dsum_enum sum) (LP.Known GET.Server_name) == 0us);
  lemma_u16_parts_fit_raw 0us;
  lemma_lp_ext_tag_raw GET.Server_name 0us;
  // payload:
  assert (LP.synth_dsum_case_recip sum (LP.Known GET.Server_name) x == mk_sne hn);
  assert (GECH.serialize_extensionClientHello_cases GET.Server_name
          == GSNE.extensionClientHello_extension_data_server_name_serializer);
  // hostName bytes
  assert_norm (LP.log256' 65535 == 2);
  LP.serialize_bounded_seq_vlbytes_bytes_eq 1 65535 hn;
  // serverName bytes: u8(0) ++ u16(len) ++ hn
  let sn : GSNM.serverName = GSNM.Name_host_name hn in
  LP.serialize_sum_eq GSNM.serverName_sum GNT.nameType_repr_serializer GSNM.serialize_serverName_cases sn;
  assert_norm (LP.sum_tag_of_data GSNM.serverName_sum sn == GNT.Host_name);
  LP.serialize_enum_key_eq GNT.nameType_repr_serializer GNT.nameType_enum GNT.Host_name;
  assert_norm (LP.enum_repr_of_key GNT.nameType_enum GNT.Host_name == 0uy);
  LP.serialize_u8_spec 0uy;
  assert (GSNM.serialize_serverName_cases GNT.Host_name == GHN.hostName_serializer);
  assert_norm (LP.synth_sum_case_recip GSNM.serverName_sum GNT.Host_name sn == hn);
  // serverNameList bytes
  let l : GSNL.serverNameList = mk_snl hn in
  GSNL.serverNameList_copyful_synth_injective ();
  GSNL.serverNameList_copyful_synth_inverse ();
  LP.serialize_synth_eq _ GSNL.synth_serverNameList GSNL.serverNameList'_serializer GSNL.synth_serverNameList_recip () l;
  assert (GSNL.synth_serverNameList_recip l == l);
  LP.serialize_list_nil GSNM.serverName_parser GSNM.serverName_serializer;
  LP.serialize_list_cons GSNM.serverName_parser GSNM.serverName_serializer sn [];
  lemma_vldata_strong_unfold_raw 1 65535 (LP.serialize_list _ GSNM.serverName_serializer) l;
  // server_name payload
  let sne : GSNE.extensionClientHello_extension_data_server_name = mk_sne hn in
  GSNE.extensionClientHello_extension_data_server_name_copyful_synth_injective ();
  GSNE.extensionClientHello_extension_data_server_name_copyful_synth_inverse ();
  LP.serialize_synth_eq _
    GSNE.synth_extensionClientHello_extension_data_server_name
    GSNE.extensionClientHello_extension_data_server_name'_serializer
    GSNE.synth_extensionClientHello_extension_data_server_name_recip
    () sne;
  assert (GSNE.synth_extensionClientHello_extension_data_server_name_recip sne == sne);
  lemma_vldata_strong_unfold_raw 0 65535 GSNL.serverNameList_serializer sne;
  // byte lengths
  let len = Seq.length hn in
  lemma_bounded_int_2_fits_raw (5 + len);
  let c1 = U8.uint_to_t ((5+len)/256) in let c2 = U8.uint_to_t ((5+len)%256) in
  lemma_bounded_int_2_raw (5 + len) c1 c2;
  lemma_bounded_int_2_fits_raw (3 + len);
  let c3 = U8.uint_to_t ((3+len)/256) in let c4 = U8.uint_to_t ((3+len)%256) in
  lemma_bounded_int_2_raw (3 + len) c3 c4;
  lemma_bounded_int_2_fits_raw len;
  let c5 = U8.uint_to_t (len/256) in let c6 = U8.uint_to_t (len%256) in
  lemma_bounded_int_2_raw len c5 c6;
  // reconcile with real-file bytes form
  RCH.lemma_client_hello_byte_v ((5+len)/256);
  assert ((5 + len) / 256 < 256);
  FStar.Math.Lemmas.small_mod ((5 + len) / 256) 256;
  assert (U8.v (client_hello_byte ((5+len)/256)) == (5+len)/256);
  lemma_u8_uint_to_t_eq_raw ((5+len)/256) (client_hello_byte ((5+len)/256));
  assert (client_hello_byte ((5+len)/256) == c1);
  RCH.lemma_client_hello_byte_v (5+len);
  lemma_u8_uint_to_t_eq_raw ((5+len)%256) (client_hello_byte (5+len));
  assert (client_hello_byte (5+len) == c2);
  RCH.lemma_client_hello_byte_v ((3+len)/256);
  assert ((3 + len) / 256 < 256);
  FStar.Math.Lemmas.small_mod ((3 + len) / 256) 256;
  assert (U8.v (client_hello_byte ((3+len)/256)) == (3+len)/256);
  lemma_u8_uint_to_t_eq_raw ((3+len)/256) (client_hello_byte ((3+len)/256));
  assert (client_hello_byte ((3+len)/256) == c3);
  RCH.lemma_client_hello_byte_v (3+len);
  lemma_u8_uint_to_t_eq_raw ((3+len)%256) (client_hello_byte (3+len));
  assert (client_hello_byte (3+len) == c4);
  RCH.lemma_client_hello_byte_v (len/256);
  assert (len / 256 < 256);
  FStar.Math.Lemmas.small_mod (len / 256) 256;
  assert (U8.v (client_hello_byte (len/256)) == len/256);
  lemma_u8_uint_to_t_eq_raw (len/256) (client_hello_byte (len/256));
  assert (client_hello_byte (len/256) == c5);
  RCH.lemma_client_hello_byte_v len;
  lemma_u8_uint_to_t_eq_raw (len%256) (client_hello_byte len);
  assert (client_hello_byte len == c6);
  // fold nested appends
  lemma_olcons_raw [0uy] [c5; c6] hn;
  lemma_olcons_raw [c3; c4] [0uy; c5; c6] hn;
  lemma_olcons_raw [c1; c2] [c3; c4; 0uy; c5; c6] hn;
  lemma_olcons_raw [0uy; 0uy] [c1; c2; c3; c4; 0uy; c5; c6] hn;
  // complete extension
  lemma_lp_extension_bytes_raw x GET.Server_name (B.of_list [0uy; 0uy])
    (Seq.append (LP.serialize (LP.serialize_bounded_integer 2) (U32.uint_to_t (5 + len)))
                (LP.serialize GSNL.serverNameList_serializer (mk_snl hn)));
  assert_norm (B.length hn == Seq.length hn);
  assert (Seq.length hn > 0);
  assert (B.length hn > 0);
  RCH.lemma_client_hello_server_name_extension_bytes_reveal hn
#pop-options
