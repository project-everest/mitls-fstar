module TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Low
friend TLS13.Wire.Generated.ProtocolVersion
friend TLS13.Wire.Generated.Random
friend TLS13.Wire.Generated.CipherSuite
friend TLS13.Wire.Generated.ClientHello_legacy_session_id
friend TLS13.Wire.Generated.ClientHello_cipher_suites
friend TLS13.Wire.Generated.ClientHello_legacy_compression_methods
friend TLS13.Wire.Generated.ExtensionType
friend TLS13.Wire.Generated.HostName
friend TLS13.Wire.Generated.ServerName
friend TLS13.Wire.Generated.ServerNameList
friend TLS13.Wire.Generated.NamedGroup
friend TLS13.Wire.Generated.SignatureScheme
friend TLS13.Wire.Generated.KeyShareEntry_key_exchange
friend TLS13.Wire.Generated.KeyShareEntry
friend TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
friend TLS13.Wire.Generated.ExtensionClientHello
friend TLS13.Wire.Generated.ClientHello_extensions
friend TLS13.Wire.Generated.ClientHello
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.Spec
module RCH = TLS13.Wire.Spec.Reveal.ClientHello
module WS = TLS13.Wire.Spec
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GRandom = TLS13.Wire.Generated.Random
module GSID = TLS13.Wire.Generated.ClientHello_legacy_session_id
module GComp = TLS13.Wire.Generated.ClientHello_legacy_compression_methods
module GCS = TLS13.Wire.Generated.CipherSuite
module GCCS = TLS13.Wire.Generated.ClientHello_cipher_suites
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GSNM = TLS13.Wire.Generated.ServerName
module GNG = TLS13.Wire.Generated.NamedGroup
module GSS = TLS13.Wire.Generated.SignatureScheme
module GHN = TLS13.Wire.Generated.HostName
module GKSEKE = TLS13.Wire.Generated.KeyShareEntry_key_exchange
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GCHEXT = TLS13.Wire.Generated.ClientHello_extensions
module GCH = TLS13.Wire.Generated.ClientHello
module U = TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Util
module L = TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Leaves
module E = TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Extensions

let client_hello_byte n = RCH.client_hello_byte n
let client_hello_common_extensions_bytes key_share = RCH.client_hello_common_extensions_bytes key_share
let client_hello_server_name_extension_bytes hostname = RCH.client_hello_server_name_extension_bytes hostname
let client_hello_extensions_bytes hostname key_share = RCH.client_hello_extensions_bytes hostname key_share
let client_hello_body_bytes random hostname key_share = RCH.client_hello_body_bytes random hostname key_share
let lemma_client_hello_common_extensions_len key_share = RCH.lemma_client_hello_common_extensions_len key_share
let lemma_client_hello_server_name_extension_len hostname = RCH.lemma_client_hello_server_name_extension_len hostname
let lemma_client_hello_extensions_len hostname key_share = RCH.lemma_client_hello_extensions_len hostname key_share
let lemma_lp_pv_tls12 = L.lemma_lp_pv_tls12
let lemma_lp_random = L.lemma_lp_random
let lemma_lp_session_id = L.lemma_lp_session_id
let lemma_lp_cipher_suites = L.lemma_lp_cipher_suites
let lemma_lp_compression = L.lemma_lp_compression
let mk_sne = E.mk_sne
let lemma_lp_sg_extension = E.lemma_lp_sg_extension
let lemma_lp_sa_extension = E.lemma_lp_sa_extension
let lemma_lp_sv_extension = E.lemma_lp_sv_extension
let lemma_lp_ks_extension = E.lemma_lp_ks_extension
let lemma_lp_sn_extension = E.lemma_lp_sn_extension
let lemma_of_list_append_raw = U.lemma_of_list_append_raw
let lemma_bounded_int_2_fits_raw = U.lemma_bounded_int_2_fits_raw
let lemma_bounded_int_2_raw = U.lemma_bounded_int_2_raw
let lemma_vldata_strong_unfold_raw = U.lemma_vldata_strong_unfold_raw

let as_key_exchange
  (key: B.bytes{B.length key == 32})
  : (key_x: GKSEKE.keyShareEntry_key_exchange{key_x == key /\ Seq.length key_x == 32})
=
  assert (LP.parse_bounded_seq_vlbytes_pred 1 65535 key);
  key

let as_host_name
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  : (hn: GHN.hostName{hn == hostname /\ Seq.length hn <= 255 /\ Seq.length hn > 0})
=
  assert (LP.parse_bounded_seq_vlbytes_pred 1 65535 hostname);
  hostname

let empty_session_id ()
  : (sid: GSID.clientHello_legacy_session_id{sid == B.empty})
=
  assert (LP.parse_bounded_seq_vlbytes_pred 0 32 B.empty);
  B.empty

let singleton_cipher_suites ()
  : (suites: GCCS.clientHello_cipher_suites{suites == [GCS.TLS_CHACHA20_POLY1305_SHA256]})
=
  [GCS.TLS_CHACHA20_POLY1305_SHA256]

let null_compression_methods ()
  : (comp: GComp.clientHello_legacy_compression_methods{comp == B.of_list [0uy]})
=
  assert_norm (B.length (B.of_list [0uy]) == 1);
  assert (LP.parse_bounded_seq_vlbytes_pred 1 255 (B.of_list [0uy]));
  B.of_list [0uy]

let lemma_ext_list_some_bounds
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  (e_sn e_sg e_sa e_ks e_sv: GECH.extensionClientHello)
  : Lemma
      (requires
        GECH.extensionClientHello_bytesize e_sn == 9 + B.length hostname /\
        GECH.extensionClientHello_bytesize e_sg == 8 /\
        GECH.extensionClientHello_bytesize e_sa == 8 /\
        GECH.extensionClientHello_bytesize e_ks == 42 /\
        GECH.extensionClientHello_bytesize e_sv == 7)
      (ensures (
        let l = [e_sn; e_sg; e_sa; e_ks; e_sv] in
        let x = GCHEXT.clientHello_extensions_list_bytesize l in
        8 <= x /\ x <= 65535))
=
  let l : list GECH.extensionClientHello = [e_sn; e_sg; e_sa; e_ks; e_sv] in
  let _ = GCHEXT.clientHello_extensions_list_bytesize_nil in
  GCHEXT.clientHello_extensions_list_bytesize_cons e_sv [];
  GCHEXT.clientHello_extensions_list_bytesize_cons e_ks [e_sv];
  GCHEXT.clientHello_extensions_list_bytesize_cons e_sa [e_ks; e_sv];
  GCHEXT.clientHello_extensions_list_bytesize_cons e_sg [e_sa; e_ks; e_sv];
  GCHEXT.clientHello_extensions_list_bytesize_cons e_sn [e_sg; e_sa; e_ks; e_sv];
  assert (GCHEXT.clientHello_extensions_list_bytesize l == 74 + B.length hostname);
  assert (8 <= 74 + B.length hostname);
  assert (B.length hostname <= 255);
  assert (74 + B.length hostname <= 329);
  assert (329 <= 65535);
  assert (74 + B.length hostname <= 65535)

let lemma_sni_extension_len_nonempty
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  : Lemma (B.length (client_hello_server_name_extension_bytes hostname) ==
           9 + B.length hostname)
=
  assert (not (B.length hostname = 0));
  RCH.lemma_client_hello_server_name_extension_bytes_reveal hostname;
  let sni_prefix = B.of_list [
    0uy; 0uy;
    client_hello_byte ((5 + B.length hostname) / 256);
    client_hello_byte (5 + B.length hostname);
    client_hello_byte ((3 + B.length hostname) / 256);
    client_hello_byte (3 + B.length hostname);
    0uy;
    client_hello_byte (B.length hostname / 256);
    client_hello_byte (B.length hostname)] in
  assert_norm (B.length sni_prefix == 9);
  Seq.lemma_len_append sni_prefix hostname;
  Seq.lemma_eq_elim (client_hello_server_name_extension_bytes hostname)
    (B.append sni_prefix hostname)

#push-options "--z3rlimit 200 --fuel 4 --ifuel 4"
let mk_ext_list_some_raw
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  (key: B.bytes{B.length key == 32})
  : list GECH.extensionClientHello
=
  let hn = as_host_name hostname in
  let key_x = as_key_exchange key in
  let ks : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key_x } in
  lemma_lp_sn_extension hn;
  lemma_lp_sg_extension ();
  lemma_lp_sa_extension ();
  lemma_lp_ks_extension key_x;
  lemma_lp_sv_extension ();
  [ GECH.Extension_data_server_name (mk_sne hn);
    GECH.Extension_data_supported_groups [GNG.X25519];
    GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256];
    GECH.Extension_data_key_share [ks];
    GECH.Extension_data_supported_versions [GPV.TLS_1p3] ]

let mk_ext_list_none_raw
  (key: B.bytes{B.length key == 32})
  : list GECH.extensionClientHello
=
  let key_x = as_key_exchange key in
  let ks : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key_x } in
  lemma_lp_sg_extension ();
  lemma_lp_sa_extension ();
  lemma_lp_ks_extension key_x;
  lemma_lp_sv_extension ();
  [ GECH.Extension_data_supported_groups [GNG.X25519];
    GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256];
    GECH.Extension_data_key_share [ks];
    GECH.Extension_data_supported_versions [GPV.TLS_1p3] ]

/// LP extensions serializer == extension list bytes
let lemma_ext_list_some_raw_wf
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  (key: B.bytes{B.length key == 32})
  : Lemma (
      let l = mk_ext_list_some_raw hostname key in
      let x = GCHEXT.clientHello_extensions_list_bytesize l in
      8 <= x /\ x <= 65535)
=
  let hn = as_host_name hostname in
  let key_x = as_key_exchange key in
  let ks : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key_x } in
  lemma_lp_sn_extension hn;
  lemma_lp_sg_extension ();
  lemma_lp_sa_extension ();
  lemma_lp_ks_extension key_x;
  lemma_lp_sv_extension ();
  let e_sn = GECH.Extension_data_server_name (mk_sne hn) in
  let e_sg = GECH.Extension_data_supported_groups [GNG.X25519] in
  let e_sa = GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256] in
  let e_ks = GECH.Extension_data_key_share [ks] in
  let e_sv = GECH.Extension_data_supported_versions [GPV.TLS_1p3] in
  GECH.extensionClientHello_bytesize_eq e_sn;
  GECH.extensionClientHello_bytesize_eq e_sg;
  GECH.extensionClientHello_bytesize_eq e_sa;
  GECH.extensionClientHello_bytesize_eq e_ks;
  GECH.extensionClientHello_bytesize_eq e_sv;
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_sn)
    (client_hello_server_name_extension_bytes hostname);
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_sg)
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]);
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_sa)
    (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]);
  assert (key_x == key);
  assert (Seq.length key_x == 32);
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_ks)
    (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key);
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_sv)
    (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]);
  lemma_client_hello_server_name_extension_len hostname;
  Seq.lemma_len_append (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key;
  assert_norm (Seq.length (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]) == 8);
  assert_norm (Seq.length (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]) == 8);
  assert_norm (Seq.length (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) == 10);
  assert_norm (Seq.length (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]) == 7);
  assert (B.length hostname > 0);
  assert (not (B.length hostname = 0));
  assert ((if B.length hostname == 0 then 0 else 9 + B.length hostname) ==
          9 + B.length hostname);
  lemma_sni_extension_len_nonempty hostname;
  assert (B.length (client_hello_server_name_extension_bytes hostname) == 9 + B.length hostname);
  assert (GECH.extensionClientHello_bytesize e_sn == Seq.length (LP.serialize GECH.extensionClientHello_serializer e_sn));
  assert (Seq.length (LP.serialize GECH.extensionClientHello_serializer e_sn) ==
          B.length (client_hello_server_name_extension_bytes hostname));
  assert (GECH.extensionClientHello_bytesize e_sn == 9 + B.length hostname);
  assert (GECH.extensionClientHello_bytesize e_sg == 8);
  assert (GECH.extensionClientHello_bytesize e_sa == 8);
  assert (GECH.extensionClientHello_bytesize e_ks == 42);
  assert (GECH.extensionClientHello_bytesize e_sv == 7);
  lemma_ext_list_some_bounds hostname e_sn e_sg e_sa e_ks e_sv;
  assert_norm (mk_ext_list_some_raw hostname key == [e_sn; e_sg; e_sa; e_ks; e_sv])

let mk_ext_list_some
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  (key: B.bytes{B.length key == 32})
  : GCHEXT.clientHello_extensions
=
  lemma_ext_list_some_raw_wf hostname key;
  mk_ext_list_some_raw hostname key

let lemma_ext_list_none_raw_wf
  (key: B.bytes{B.length key == 32})
  : Lemma (
      let l = mk_ext_list_none_raw key in
      let x = GCHEXT.clientHello_extensions_list_bytesize l in
      8 <= x /\ x <= 65535)
=
  let key_x = as_key_exchange key in
  let ks : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key_x } in
  lemma_lp_sg_extension ();
  lemma_lp_sa_extension ();
  lemma_lp_ks_extension key_x;
  lemma_lp_sv_extension ();
  let e_sg = GECH.Extension_data_supported_groups [GNG.X25519] in
  let e_sa = GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256] in
  let e_ks = GECH.Extension_data_key_share [ks] in
  let e_sv = GECH.Extension_data_supported_versions [GPV.TLS_1p3] in
  GECH.extensionClientHello_bytesize_eq e_sg;
  GECH.extensionClientHello_bytesize_eq e_sa;
  GECH.extensionClientHello_bytesize_eq e_ks;
  GECH.extensionClientHello_bytesize_eq e_sv;
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_sg)
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]);
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_sa)
    (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]);
  assert (key_x == key);
  assert (Seq.length key_x == 32);
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_ks)
    (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key);
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_sv)
    (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]);
  Seq.lemma_len_append (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key;
  assert_norm (Seq.length (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]) == 8);
  assert_norm (Seq.length (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]) == 8);
  assert_norm (Seq.length (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) == 10);
  assert_norm (Seq.length (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]) == 7);
  assert (GECH.extensionClientHello_bytesize e_sg == 8);
  assert (GECH.extensionClientHello_bytesize e_sa == 8);
  assert (GECH.extensionClientHello_bytesize e_ks == 42);
  assert (GECH.extensionClientHello_bytesize e_sv == 7);
  let l : list GECH.extensionClientHello = [e_sg; e_sa; e_ks; e_sv] in
  let _ = GCHEXT.clientHello_extensions_list_bytesize_nil in
  GCHEXT.clientHello_extensions_list_bytesize_cons e_sv [];
  GCHEXT.clientHello_extensions_list_bytesize_cons e_ks [e_sv];
  GCHEXT.clientHello_extensions_list_bytesize_cons e_sa [e_ks; e_sv];
  GCHEXT.clientHello_extensions_list_bytesize_cons e_sg [e_sa; e_ks; e_sv];
  assert (GCHEXT.clientHello_extensions_list_bytesize l == 65);
  assert (8 <= GCHEXT.clientHello_extensions_list_bytesize l);
  assert (GCHEXT.clientHello_extensions_list_bytesize l <= 65535);
  assert_spinoff (let x = GCHEXT.clientHello_extensions_list_bytesize l in 8 <= x /\ x <= 65535);
  assert_norm (mk_ext_list_none_raw key == l)

let mk_ext_list_none
  (key: B.bytes{B.length key == 32})
  : GCHEXT.clientHello_extensions
=
  lemma_ext_list_none_raw_wf key;
  mk_ext_list_none_raw key

let mk_ch_low_some
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32})
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  : GCH.clientHello
=
  { GCH.legacy_version = GPV.TLS_1p2;
    GCH.random = ch.M.random;
    GCH.legacy_session_id = B.empty;
    GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
    GCH.legacy_compression_methods = B.of_list [0uy];
    GCH.extensions = mk_ext_list_some hostname ch.M.key_share }

let mk_ch_low_none
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32})
  : GCH.clientHello
=
  { GCH.legacy_version = GPV.TLS_1p2;
    GCH.random = ch.M.random;
    GCH.legacy_session_id = B.empty;
    GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
    GCH.legacy_compression_methods = B.of_list [0uy];
    GCH.extensions = mk_ext_list_none ch.M.key_share }
#pop-options

#push-options "--z3rlimit 10 --fuel 4 --ifuel 4"
let lemma_ch_extensions_some_raw
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  (key: B.bytes{B.length key == 32})
  : Lemma (
      WS.ch_extensions (mk_ext_list_some_raw hostname key) None None false [] ==
      Some (Some hostname, Some key, true, [T.RsaPssRsaeSha256]))
=
  let hn = as_host_name hostname in
  let key_x = as_key_exchange key in
  let ks : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key_x } in
  let tail_sv = [GECH.Extension_data_supported_versions [GPV.TLS_1p3]] in
  let tail_ks = GECH.Extension_data_key_share [ks] :: tail_sv in
  let tail_sa = GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256] :: tail_ks in
  let tail_sg = GECH.Extension_data_supported_groups [GNG.X25519] :: tail_sa in
  let exts = GECH.Extension_data_server_name (E.mk_sne hn) :: tail_sg in
  E.lemma_mk_sne_shape hn;
  assert (hn == hostname);
  assert (E.mk_sne hn == [GSNM.Name_host_name hn]);
  assert (WS.ch_server_name (E.mk_sne hn) == Some hostname);
  WS.lemma_key_exchange_to_key32 key_x;
  assert (WS.key_exchange_to_key32 key_x == Some key);
  assert (WS.ch_find_key_share [ks] == Some key);
  assert_norm (WS.synth_sig_schemes [GSS.Rsa_pss_rsae_sha256] == [T.RsaPssRsaeSha256]);
  assert_norm (List.Tot.mem GPV.TLS_1p3 [GPV.TLS_1p3]);
  assert_norm (WS.ch_extensions [] (Some hostname) (Some key) true [T.RsaPssRsaeSha256] ==
    Some (Some hostname, Some key, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions tail_sv (Some hostname) (Some key) false [T.RsaPssRsaeSha256] ==
    Some (Some hostname, Some key, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions tail_ks (Some hostname) None false [T.RsaPssRsaeSha256] ==
    Some (Some hostname, Some key, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions tail_sa (Some hostname) None false [] ==
    Some (Some hostname, Some key, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions tail_sg (Some hostname) None false [] ==
    Some (Some hostname, Some key, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions exts None None false [] ==
    Some (Some hostname, Some key, true, [T.RsaPssRsaeSha256]));
  assert_norm (mk_ext_list_some_raw hostname key == exts)

let lemma_ch_extensions_none_raw
  (key: B.bytes{B.length key == 32})
  : Lemma (
      WS.ch_extensions (mk_ext_list_none_raw key) None None false [] ==
      Some (None, Some key, true, [T.RsaPssRsaeSha256]))
=
  let key_x = as_key_exchange key in
  let ks : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key_x } in
  let tail_sv = [GECH.Extension_data_supported_versions [GPV.TLS_1p3]] in
  let tail_ks = GECH.Extension_data_key_share [ks] :: tail_sv in
  let tail_sa = GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256] :: tail_ks in
  let exts = GECH.Extension_data_supported_groups [GNG.X25519] :: tail_sa in
  WS.lemma_key_exchange_to_key32 key_x;
  assert (WS.key_exchange_to_key32 key_x == Some key);
  assert (WS.ch_find_key_share [ks] == Some key);
  assert_norm (WS.synth_sig_schemes [GSS.Rsa_pss_rsae_sha256] == [T.RsaPssRsaeSha256]);
  assert_norm (List.Tot.mem GPV.TLS_1p3 [GPV.TLS_1p3]);
  assert_norm (WS.ch_extensions [] None (Some key) true [T.RsaPssRsaeSha256] ==
    Some (None, Some key, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions tail_sv None (Some key) false [T.RsaPssRsaeSha256] ==
    Some (None, Some key, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions tail_ks None None false [T.RsaPssRsaeSha256] ==
    Some (None, Some key, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions tail_sa None None false [] ==
    Some (None, Some key, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions exts None None false [] ==
    Some (None, Some key, true, [T.RsaPssRsaeSha256]));
  assert_norm (mk_ext_list_none_raw key == exts)
#pop-options

let lemma_synth_client_hello_some
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256]})
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0 /\ ch.M.server_name == Some hostname})
  : Lemma (
      let low : GCH.clientHello =
        { GCH.legacy_version = GPV.TLS_1p2;
          GCH.random = ch.M.random;
          GCH.legacy_session_id = B.empty;
          GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
          GCH.legacy_compression_methods = B.of_list [0uy];
          GCH.extensions = mk_ext_list_some hostname ch.M.key_share } in
      WS.synth_client_hello low == Some ch)
=
  let ext_raw = mk_ext_list_some_raw hostname ch.M.key_share in
  let low : GCH.clientHello =
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = ch.M.random;
      GCH.legacy_session_id = B.empty;
      GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
      GCH.legacy_compression_methods = B.of_list [0uy];
      GCH.extensions = mk_ext_list_some hostname ch.M.key_share } in
  let hn = as_host_name hostname in
  E.lemma_mk_sne_shape hn;
  assert (hn == hostname);
  assert (E.mk_sne hn == [GSNM.Name_host_name hn]);
  assert (mk_ext_list_some hostname ch.M.key_share == ext_raw);
  assert (low.GCH.extensions == ext_raw);
  lemma_ch_extensions_some_raw hostname ch.M.key_share;
  assert (WS.ch_extensions ext_raw None None false [] ==
    Some (Some hostname, Some ch.M.key_share, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions low.GCH.extensions None None false [] ==
    Some (Some hostname, Some ch.M.key_share, true, [T.RsaPssRsaeSha256]));
  assert_norm (WS.synth_cipher_suites low.GCH.cipher_suites ==
    [T.TLS_CHACHA20_POLY1305_SHA256]);
  assert (WS.synth_client_hello low == Some ch)

let lemma_synth_client_hello_none
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                       ch.M.server_name == None})
  : Lemma (
      let low : GCH.clientHello =
        { GCH.legacy_version = GPV.TLS_1p2;
          GCH.random = ch.M.random;
          GCH.legacy_session_id = B.empty;
          GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
          GCH.legacy_compression_methods = B.of_list [0uy];
          GCH.extensions = mk_ext_list_none ch.M.key_share } in
      WS.synth_client_hello low == Some ch)
=
  let ext_raw = mk_ext_list_none_raw ch.M.key_share in
  let low : GCH.clientHello =
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = ch.M.random;
      GCH.legacy_session_id = B.empty;
      GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
      GCH.legacy_compression_methods = B.of_list [0uy];
      GCH.extensions = mk_ext_list_none ch.M.key_share } in
  assert (mk_ext_list_none ch.M.key_share == ext_raw);
  assert (low.GCH.extensions == ext_raw);
  lemma_ch_extensions_none_raw ch.M.key_share;
  assert (WS.ch_extensions ext_raw None None false [] ==
    Some (None, Some ch.M.key_share, true, [T.RsaPssRsaeSha256]));
  assert (WS.ch_extensions low.GCH.extensions None None false [] ==
    Some (None, Some ch.M.key_share, true, [T.RsaPssRsaeSha256]));
  assert_norm (WS.synth_cipher_suites low.GCH.cipher_suites ==
    [T.TLS_CHACHA20_POLY1305_SHA256]);
  assert (WS.synth_client_hello low == Some ch)

/// Prove that LP extensions list bytes == client_hello_extensions_bytes (common part)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
private let lemma_lp_ext_list_bytes_common
  (key: B.bytes{B.length key == 32})
  : Lemma (Seq.equal
      (LP.serialize (LP.serialize_list _ GECH.extensionClientHello_serializer)
                    (mk_ext_list_none key))
      (client_hello_common_extensions_bytes key))
=
  let key_x = as_key_exchange key in
  let ks : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key_x } in
  let l = mk_ext_list_none key in
  let e_sg = GECH.Extension_data_supported_groups [GNG.X25519] in
  let e_sa = GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256] in
  let e_ks = GECH.Extension_data_key_share [ks] in
  let e_sv = GECH.Extension_data_supported_versions [GPV.TLS_1p3] in
  assert_norm (mk_ext_list_none key == [e_sg; e_sa; e_ks; e_sv]);
  LP.serialize_list_nil GECH.extensionClientHello_parser GECH.extensionClientHello_serializer;
  LP.serialize_list_cons GECH.extensionClientHello_parser GECH.extensionClientHello_serializer e_sv [];
  LP.serialize_list_cons GECH.extensionClientHello_parser GECH.extensionClientHello_serializer e_ks [e_sv];
  LP.serialize_list_cons GECH.extensionClientHello_parser GECH.extensionClientHello_serializer e_sa [e_ks; e_sv];
  LP.serialize_list_cons GECH.extensionClientHello_parser GECH.extensionClientHello_serializer e_sg [e_sa; e_ks; e_sv];
  lemma_lp_sg_extension ();
  lemma_lp_sa_extension ();
  lemma_lp_ks_extension key_x;
  lemma_lp_sv_extension ();
  let sg_bytes = B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy] in
  let sa_bytes = B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy] in
  let ks_prefix = B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] in
  let sv_bytes = B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy] in
  Seq.lemma_eq_elim (LP.serialize GECH.extensionClientHello_serializer e_sg) sg_bytes;
  Seq.lemma_eq_elim (LP.serialize GECH.extensionClientHello_serializer e_sa) sa_bytes;
  assert (key_x == key);
  Seq.lemma_eq_elim
    (Seq.append ks_prefix key_x)
    (Seq.append ks_prefix key);
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_ks)
    (Seq.append ks_prefix key);
  Seq.lemma_eq_elim (LP.serialize GECH.extensionClientHello_serializer e_sv) sv_bytes;
  Seq.append_empty_r sv_bytes;
  RCH.lemma_client_hello_common_extensions_bytes_reveal key;
  Seq.lemma_eq_elim
    (client_hello_common_extensions_bytes key)
    (B.append
      sg_bytes
      (B.append
        sa_bytes
        (B.append
          (B.append ks_prefix key)
          sv_bytes)));
  assert (Seq.equal
    (LP.serialize (LP.serialize_list _ GECH.extensionClientHello_serializer)
                  (mk_ext_list_none key))
    (client_hello_common_extensions_bytes key))
#pop-options

#restart-solver

#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
private let lemma_lp_ext_list_bytes_some
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  (key: B.bytes{B.length key == 32})
  : Lemma (Seq.equal
      (LP.serialize (LP.serialize_list _ GECH.extensionClientHello_serializer)
                    (mk_ext_list_some hostname key))
      (client_hello_extensions_bytes hostname key))
=
  let hn = as_host_name hostname in
  let key_x = as_key_exchange key in
  let ks : GKSE.keyShareEntry = { GKSE.group = GNG.X25519; GKSE.key_exchange = key_x } in
  let e_sn = GECH.Extension_data_server_name (mk_sne hn) in
  let e_sg = GECH.Extension_data_supported_groups [GNG.X25519] in
  let e_sa = GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256] in
  let e_ks = GECH.Extension_data_key_share [ks] in
  let e_sv = GECH.Extension_data_supported_versions [GPV.TLS_1p3] in
  assert_norm (mk_ext_list_some hostname key == [e_sn; e_sg; e_sa; e_ks; e_sv]);
  LP.serialize_list_nil GECH.extensionClientHello_parser GECH.extensionClientHello_serializer;
  LP.serialize_list_cons GECH.extensionClientHello_parser GECH.extensionClientHello_serializer e_sv [];
  LP.serialize_list_cons GECH.extensionClientHello_parser GECH.extensionClientHello_serializer e_ks [e_sv];
  LP.serialize_list_cons GECH.extensionClientHello_parser GECH.extensionClientHello_serializer e_sa [e_ks; e_sv];
  LP.serialize_list_cons GECH.extensionClientHello_parser GECH.extensionClientHello_serializer e_sg [e_sa; e_ks; e_sv];
  LP.serialize_list_cons GECH.extensionClientHello_parser GECH.extensionClientHello_serializer e_sn
    [e_sg; e_sa; e_ks; e_sv];
  lemma_lp_sn_extension hn;
  lemma_lp_sg_extension ();
  lemma_lp_sa_extension ();
  lemma_lp_ks_extension key_x;
  lemma_lp_sv_extension ();
  let sn_bytes = client_hello_server_name_extension_bytes hostname in
  let sg_bytes = B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy] in
  let sa_bytes = B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy] in
  let ks_prefix = B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] in
  let sv_bytes = B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy] in
  assert (hn == hostname);
  Seq.lemma_eq_elim
    (client_hello_server_name_extension_bytes hn)
    sn_bytes;
  Seq.lemma_eq_elim (LP.serialize GECH.extensionClientHello_serializer e_sn) sn_bytes;
  Seq.lemma_eq_elim (LP.serialize GECH.extensionClientHello_serializer e_sg) sg_bytes;
  Seq.lemma_eq_elim (LP.serialize GECH.extensionClientHello_serializer e_sa) sa_bytes;
  assert (key_x == key);
  Seq.lemma_eq_elim
    (Seq.append ks_prefix key_x)
    (Seq.append ks_prefix key);
  Seq.lemma_eq_elim
    (LP.serialize GECH.extensionClientHello_serializer e_ks)
    (Seq.append ks_prefix key);
  Seq.lemma_eq_elim (LP.serialize GECH.extensionClientHello_serializer e_sv) sv_bytes;
  Seq.append_empty_r sv_bytes;
  RCH.lemma_client_hello_common_extensions_bytes_reveal key;
  Seq.lemma_eq_elim
    (client_hello_common_extensions_bytes key)
    (B.append
      sg_bytes
      (B.append
        sa_bytes
        (B.append
          (B.append ks_prefix key)
          sv_bytes)));
  RCH.lemma_client_hello_extensions_bytes_shape hostname key;
  Seq.lemma_eq_elim
    (client_hello_extensions_bytes hostname key)
    (B.append sn_bytes (client_hello_common_extensions_bytes key));
  assert (Seq.equal
    (LP.serialize (LP.serialize_list _ GECH.extensionClientHello_serializer)
                  (mk_ext_list_some hostname key))
    (client_hello_extensions_bytes hostname key))
#pop-options

#restart-solver

/// LP clientHello_extensions_serializer bytes

#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_lp_ch_ext_ser_some
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0})
  (key: B.bytes{B.length key == 32})
  : Lemma (Seq.equal
      (LP.serialize GCHEXT.clientHello_extensions_serializer (mk_ext_list_some hostname key))
      (Seq.append
        (B.of_list [client_hello_byte (B.length (client_hello_extensions_bytes hostname key) / 256);
                    client_hello_byte (B.length (client_hello_extensions_bytes hostname key))])
        (client_hello_extensions_bytes hostname key)))
=
  let ext_list = mk_ext_list_some hostname key in
  GCHEXT.clientHello_extensions_copyful_synth_injective ();
  GCHEXT.clientHello_extensions_copyful_synth_inverse ();
  LP.serialize_synth_eq _
    GCHEXT.synth_clientHello_extensions
    GCHEXT.clientHello_extensions'_serializer
    GCHEXT.synth_clientHello_extensions_recip
    () ext_list;
  assert (GCHEXT.synth_clientHello_extensions_recip ext_list == ext_list);
  lemma_vldata_strong_unfold_raw 8 65535
    (LP.serialize_list _ GECH.extensionClientHello_serializer) ext_list;
  assert_norm (LP.log256' 65535 == 2);
  lemma_lp_ext_list_bytes_some hostname key;
  let ext_bytes = client_hello_extensions_bytes hostname key in
  let ext_len = B.length ext_bytes in
  lemma_client_hello_extensions_len hostname key;
  lemma_bounded_int_2_fits_raw ext_len;
  let ext_hi = client_hello_byte (ext_len / 256) in
  let ext_lo = client_hello_byte ext_len in
  RCH.lemma_client_hello_byte_v (ext_len / 256);
  RCH.lemma_client_hello_byte_v ext_len;
  FStar.Math.Lemmas.small_mod (ext_len / 256) 256;
  assert (U8.v ext_hi == ext_len / 256);
  assert (U8.v ext_lo == ext_len % 256);
  lemma_bounded_int_2_raw ext_len ext_hi ext_lo
#pop-options

#restart-solver

#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_lp_ch_ext_ser_none
  (key: B.bytes{B.length key == 32})
  : Lemma (Seq.equal
      (LP.serialize GCHEXT.clientHello_extensions_serializer (mk_ext_list_none key))
      (Seq.append
        (B.of_list [client_hello_byte (B.length (client_hello_common_extensions_bytes key) / 256);
                    client_hello_byte (B.length (client_hello_common_extensions_bytes key))])
        (client_hello_common_extensions_bytes key)))
=
  let ext_list = mk_ext_list_none key in
  GCHEXT.clientHello_extensions_copyful_synth_injective ();
  GCHEXT.clientHello_extensions_copyful_synth_inverse ();
  LP.serialize_synth_eq _
    GCHEXT.synth_clientHello_extensions
    GCHEXT.clientHello_extensions'_serializer
    GCHEXT.synth_clientHello_extensions_recip
    () ext_list;
  assert (GCHEXT.synth_clientHello_extensions_recip ext_list == ext_list);
  lemma_vldata_strong_unfold_raw 8 65535
    (LP.serialize_list _ GECH.extensionClientHello_serializer) ext_list;
  assert_norm (LP.log256' 65535 == 2);
  lemma_lp_ext_list_bytes_common key;
  let ext_bytes = client_hello_common_extensions_bytes key in
  let ext_len = B.length ext_bytes in
  lemma_client_hello_common_extensions_len key;
  lemma_bounded_int_2_fits_raw ext_len;
  let ext_hi = client_hello_byte (ext_len / 256) in
  let ext_lo = client_hello_byte ext_len in
  RCH.lemma_client_hello_byte_v (ext_len / 256);
  RCH.lemma_client_hello_byte_v ext_len;
  FStar.Math.Lemmas.small_mod (ext_len / 256) 256;
  assert (U8.v ext_hi == ext_len / 256);
  assert (U8.v ext_lo == ext_len % 256);
  lemma_bounded_int_2_raw ext_len ext_hi ext_lo
#pop-options

#restart-solver

/// LP clientHello_serializer == client_hello_body_bytes

#push-options "--fuel 4 --ifuel 4 --z3rlimit 200 --split_queries always"
let lemma_lp_ch_low_bytes_some
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256]})
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0 /\ ch.M.server_name == Some hostname})
  : Lemma
      (let low : GCH.clientHello =
         { GCH.legacy_version = GPV.TLS_1p2;
           GCH.random = ch.M.random;
           GCH.legacy_session_id = B.empty;
           GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
           GCH.legacy_compression_methods = B.of_list [0uy];
           GCH.extensions = mk_ext_list_some hostname ch.M.key_share } in
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (client_hello_body_bytes ch.M.random hostname ch.M.key_share) /\
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (client_hello_body_bytes
                   ch.M.random
                   (match ch.M.server_name with
                    | Some h -> h
                    | None -> B.empty)
                   ch.M.key_share) /\
       WS.synth_client_hello low == Some ch)
=
  let sid = empty_session_id () in
  let suites = singleton_cipher_suites () in
  let comp = null_compression_methods () in
  let low : GCH.clientHello =
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = ch.M.random;
      GCH.legacy_session_id = sid;
      GCH.cipher_suites = suites;
      GCH.legacy_compression_methods = comp;
      GCH.extensions = mk_ext_list_some hostname ch.M.key_share } in
  // Step 1: expand clientHello_serializer via serialize_synth_eq
  GCH.synth_clientHello_injective ();
  GCH.synth_clientHello_inverse ();
  LP.serialize_synth_eq GCH.clientHello'_parser GCH.synth_clientHello
    GCH.clientHello'_serializer GCH.synth_clientHello_recip () low;
  assert (GCH.synth_clientHello_recip low ==
    (((GPV.TLS_1p2, ch.M.random), (sid, suites)),
     (comp, mk_ext_list_some hostname ch.M.key_share)));
  // Step 2: expand clientHello'_serializer via nondep_then_eq
  let s1 = GPV.protocolVersion_serializer in
  let s2 = GRandom.random_serializer in
  let s3 = GSID.clientHello_legacy_session_id_serializer in
  let s4 = GCCS.clientHello_cipher_suites_serializer in
  let s5 = GComp.clientHello_legacy_compression_methods_serializer in
  let s6 = GCHEXT.clientHello_extensions_serializer in
  let s12 = LP.serialize_nondep_then s1 s2 in
  let s34 = LP.serialize_nondep_then s3 s4 in
  let s56 = LP.serialize_nondep_then s5 s6 in
  let s1234 = LP.serialize_nondep_then s12 s34 in
  LP.serialize_nondep_then_eq s1234 s56
    (((GPV.TLS_1p2, ch.M.random), (sid, suites)),
     (comp, mk_ext_list_some hostname ch.M.key_share));
  LP.serialize_nondep_then_eq s12 s34
    ((GPV.TLS_1p2, ch.M.random), (sid, suites));
  LP.serialize_nondep_then_eq s5 s6
    (comp, mk_ext_list_some hostname ch.M.key_share);
  LP.serialize_nondep_then_eq s1 s2 (GPV.TLS_1p2, ch.M.random);
  LP.serialize_nondep_then_eq s3 s4 (sid, suites);
  // Step 3: leaf fields
  lemma_lp_pv_tls12 ();
  lemma_lp_random ch.M.random;
  lemma_lp_session_id ();
  lemma_lp_cipher_suites ();
  lemma_lp_compression ();
  // Step 4: extensions
  lemma_lp_ch_ext_ser_some hostname ch.M.key_share;
  // Step 5: convert Seq.equal to == for each component
  let ext_bytes = client_hello_extensions_bytes hostname ch.M.key_share in
  let ext_len = B.length ext_bytes in
  lemma_client_hello_extensions_len hostname ch.M.key_share;
  let ext_len_bytes = B.of_list [client_hello_byte (ext_len / 256); client_hello_byte ext_len] in
  Seq.lemma_eq_elim (LP.serialize s1 GPV.TLS_1p2) (B.of_list [0x03uy; 0x03uy]);
  Seq.lemma_eq_elim (LP.serialize s3 sid) (B.of_list [0uy]);
  Seq.lemma_eq_elim (LP.serialize s4 suites) (B.of_list [0uy; 2uy; 0x13uy; 0x03uy]);
  Seq.lemma_eq_elim (LP.serialize s5 comp) (B.of_list [1uy; 0uy]);
  Seq.lemma_eq_elim
    (LP.serialize s6 (mk_ext_list_some hostname ch.M.key_share))
    (Seq.append ext_len_bytes ext_bytes);
  // Step 6: reassociate to match client_hello_body_bytes tree structure
  // LP tree: ((([0x03;0x03] ++ r) ++ ([0uy] ++ [0uy;2uy;0x13uy;0x03uy])) ++ ([1uy;0uy] ++ (ext_len ++ ext)))
  // body tree: [0x03;0x03] ++ r ++ [0uy] ++ [0uy;2uy;0x13uy;0x03uy;1uy] ++ [0uy] ++ ext_len ++ ext
  let pv = B.of_list [0x03uy; 0x03uy] in
  let r = ch.M.random in
  let sid = B.of_list [0uy] in
  let cs = B.of_list [0uy; 2uy; 0x13uy; 0x03uy] in
  let comp = B.of_list [1uy; 0uy] in
  // Show cs ++ comp == B.of_list [0;2;0x13;3;1;0]
  lemma_of_list_append_raw [0uy; 2uy; 0x13uy; 0x03uy] [1uy; 0uy];
  assert_norm (FStar.List.Tot.append [0uy; 2uy; 0x13uy; 0x03uy] [1uy; 0uy] == [0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy]);
  assert (Seq.equal (Seq.append cs comp) (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy]));
  lemma_of_list_append_raw [0uy; 2uy; 0x13uy; 0x03uy; 1uy] [0uy];
  assert_norm (FStar.List.Tot.append [0uy; 2uy; 0x13uy; 0x03uy; 1uy] [0uy] == [0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy]);
  assert (Seq.equal (Seq.append (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]) (B.of_list [0uy])) (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy]));
  Seq.lemma_eq_elim (Seq.append cs comp) (Seq.append (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]) (B.of_list [0uy]));
  // Reassociate: show LP_tree == body_tree using append_assoc
  let f56 = (B.of_list [0uy], mk_ext_list_some hostname ch.M.key_share) in
  let ext_with_len = Seq.append ext_len_bytes ext_bytes in
  // LP: Seq.append (Seq.append (Seq.append pv r) (Seq.append sid cs)) (Seq.append comp ext_with_len)
  // Step: Seq.append comp ext_with_len == Seq.append comp (ext_with_len)
  // Reassoc outer: (A ++ B) ++ C == A ++ (B ++ C)
  Seq.append_assoc (Seq.append pv r) (Seq.append sid cs) (Seq.append comp ext_with_len);
  // outer left: A=pv++r, B=sid++cs, C=comp++ext_with_len
  // → pv++r ++ (sid++cs ++ comp++ext_with_len)
  Seq.append_assoc pv r (Seq.append (Seq.append sid cs) (Seq.append comp ext_with_len));
  // → pv ++ (r ++ (sid++cs ++ comp++ext_with_len))
  Seq.append_assoc (Seq.append sid cs) (Seq.append comp ext_with_len) (Seq.create 0 0uy);
  Seq.append_assoc sid cs (Seq.append comp ext_with_len);
  // → ... ++ (sid ++ (cs ++ comp ++ ext_with_len))
  Seq.append_assoc cs comp ext_with_len;
  // → ... ++ (sid ++ ((cs ++ comp) ++ ext_with_len))
  // And cs ++ comp = [0;2;0x13;3;1;0] = [0;2;0x13;3;1] ++ [0]
  Seq.append_assoc (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]) (B.of_list [0uy]) ext_with_len;
  // Now: (cs ++ comp) ++ ext_with_len == [cs';0uy] ++ ext_with_len == cs' ++ (0uy ++ ext_with_len)
  Seq.append_assoc (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]) (B.of_list [0uy]) (Seq.append ext_len_bytes ext_bytes);
  // ext_with_len = ext_len_bytes ++ ext_bytes
  Seq.append_assoc (B.of_list [0uy]) ext_len_bytes ext_bytes;
  RCH.lemma_client_hello_body_bytes_shape ch.M.random hostname ch.M.key_share;
  Seq.lemma_eq_elim
    (client_hello_body_bytes ch.M.random hostname ch.M.key_share)
    (B.append
      pv
      (B.append
        r
        (B.append
          sid
          (B.append
            (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
            (B.append
              (B.of_list [0uy])
              (B.append ext_len_bytes ext_bytes))))));
  assert (Seq.equal
    (LP.serialize GCH.clientHello_serializer low)
    (client_hello_body_bytes ch.M.random hostname ch.M.key_share));
  assert ((match ch.M.server_name with | Some h -> h | None -> B.empty) == hostname);
  assert (Seq.equal
    (LP.serialize GCH.clientHello_serializer low)
    (client_hello_body_bytes
      ch.M.random
      (match ch.M.server_name with | Some h -> h | None -> B.empty)
      ch.M.key_share));
  lemma_synth_client_hello_some ch hostname;
  assert (WS.synth_client_hello low == Some ch)
#pop-options

#push-options "--fuel 4 --ifuel 4 --z3rlimit 200 --split_queries always"
let lemma_lp_ch_low_bytes_none
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                       ch.M.server_name == None})
  : Lemma
      (let low : GCH.clientHello =
         { GCH.legacy_version = GPV.TLS_1p2;
           GCH.random = ch.M.random;
           GCH.legacy_session_id = B.empty;
           GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
           GCH.legacy_compression_methods = B.of_list [0uy];
           GCH.extensions = mk_ext_list_none ch.M.key_share } in
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (client_hello_body_bytes ch.M.random B.empty ch.M.key_share) /\
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (client_hello_body_bytes
                   ch.M.random
                   (match ch.M.server_name with
                    | Some h -> h
                    | None -> B.empty)
                   ch.M.key_share) /\
       WS.synth_client_hello low == Some ch)
=
  let sid = empty_session_id () in
  let suites = singleton_cipher_suites () in
  let comp = null_compression_methods () in
  let low : GCH.clientHello =
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = ch.M.random;
      GCH.legacy_session_id = sid;
      GCH.cipher_suites = suites;
      GCH.legacy_compression_methods = comp;
      GCH.extensions = mk_ext_list_none ch.M.key_share } in
  GCH.synth_clientHello_injective ();
  GCH.synth_clientHello_inverse ();
  LP.serialize_synth_eq GCH.clientHello'_parser GCH.synth_clientHello
    GCH.clientHello'_serializer GCH.synth_clientHello_recip () low;
  assert (GCH.synth_clientHello_recip low ==
    (((GPV.TLS_1p2, ch.M.random), (sid, suites)),
     (comp, mk_ext_list_none ch.M.key_share)));
  let s1 = GPV.protocolVersion_serializer in
  let s2 = GRandom.random_serializer in
  let s3 = GSID.clientHello_legacy_session_id_serializer in
  let s4 = GCCS.clientHello_cipher_suites_serializer in
  let s5 = GComp.clientHello_legacy_compression_methods_serializer in
  let s6 = GCHEXT.clientHello_extensions_serializer in
  let s12 = LP.serialize_nondep_then s1 s2 in
  let s34 = LP.serialize_nondep_then s3 s4 in
  let s56 = LP.serialize_nondep_then s5 s6 in
  let s1234 = LP.serialize_nondep_then s12 s34 in
  LP.serialize_nondep_then_eq s1234 s56
    (((GPV.TLS_1p2, ch.M.random), (sid, suites)),
     (comp, mk_ext_list_none ch.M.key_share));
  LP.serialize_nondep_then_eq s12 s34
    ((GPV.TLS_1p2, ch.M.random), (sid, suites));
  LP.serialize_nondep_then_eq s5 s6
    (comp, mk_ext_list_none ch.M.key_share);
  LP.serialize_nondep_then_eq s1 s2 (GPV.TLS_1p2, ch.M.random);
  LP.serialize_nondep_then_eq s3 s4 (sid, suites);
  lemma_lp_pv_tls12 ();
  lemma_lp_random ch.M.random;
  lemma_lp_session_id ();
  lemma_lp_cipher_suites ();
  lemma_lp_compression ();
  lemma_lp_ch_ext_ser_none ch.M.key_share;
  let ext_bytes = client_hello_common_extensions_bytes ch.M.key_share in
  let ext_len = B.length ext_bytes in
  lemma_client_hello_common_extensions_len ch.M.key_share;
  let ext_len_bytes = B.of_list [client_hello_byte (ext_len / 256); client_hello_byte ext_len] in
  Seq.lemma_eq_elim (LP.serialize s1 GPV.TLS_1p2) (B.of_list [0x03uy; 0x03uy]);
  Seq.lemma_eq_elim (LP.serialize s3 sid) (B.of_list [0uy]);
  Seq.lemma_eq_elim (LP.serialize s4 suites) (B.of_list [0uy; 2uy; 0x13uy; 0x03uy]);
  Seq.lemma_eq_elim (LP.serialize s5 comp) (B.of_list [1uy; 0uy]);
  Seq.lemma_eq_elim
    (LP.serialize s6 (mk_ext_list_none ch.M.key_share))
    (Seq.append ext_len_bytes ext_bytes);
  let pv = B.of_list [0x03uy; 0x03uy] in
  let r = ch.M.random in
  let sid = B.of_list [0uy] in
  let cs = B.of_list [0uy; 2uy; 0x13uy; 0x03uy] in
  let comp = B.of_list [1uy; 0uy] in
  let ext_with_len = Seq.append ext_len_bytes ext_bytes in
  lemma_of_list_append_raw [0uy; 2uy; 0x13uy; 0x03uy] [1uy; 0uy];
  assert_norm (FStar.List.Tot.append [0uy; 2uy; 0x13uy; 0x03uy] [1uy; 0uy] == [0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy]);
  assert (Seq.equal (Seq.append cs comp) (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy]));
  lemma_of_list_append_raw [0uy; 2uy; 0x13uy; 0x03uy; 1uy] [0uy];
  assert_norm (FStar.List.Tot.append [0uy; 2uy; 0x13uy; 0x03uy; 1uy] [0uy] == [0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy]);
  assert (Seq.equal (Seq.append (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]) (B.of_list [0uy])) (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy]));
  Seq.lemma_eq_elim (Seq.append cs comp) (Seq.append (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]) (B.of_list [0uy]));
  Seq.append_assoc (Seq.append pv r) (Seq.append sid cs) (Seq.append comp ext_with_len);
  Seq.append_assoc pv r (Seq.append (Seq.append sid cs) (Seq.append comp ext_with_len));
  Seq.append_assoc sid cs (Seq.append comp ext_with_len);
  Seq.append_assoc cs comp ext_with_len;
  Seq.append_assoc (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]) (B.of_list [0uy]) ext_with_len;
  Seq.append_assoc (B.of_list [0uy]) ext_len_bytes ext_bytes;
  RCH.lemma_client_hello_extensions_bytes_shape B.empty ch.M.key_share;
  RCH.lemma_client_hello_server_name_extension_bytes_empty B.empty;
  Seq.lemma_eq_elim (client_hello_server_name_extension_bytes B.empty) B.empty;
  Seq.append_empty_l ext_bytes;
  Seq.lemma_eq_elim
    (client_hello_extensions_bytes B.empty ch.M.key_share)
    ext_bytes;
  RCH.lemma_client_hello_body_bytes_shape ch.M.random B.empty ch.M.key_share;
  Seq.lemma_eq_elim
    (client_hello_body_bytes ch.M.random B.empty ch.M.key_share)
    (B.append
      pv
      (B.append
        r
        (B.append
          sid
          (B.append
            (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
            (B.append
              (B.of_list [0uy])
              (B.append ext_len_bytes ext_bytes))))));
  assert (Seq.equal
    (LP.serialize GCH.clientHello_serializer low)
    (client_hello_body_bytes ch.M.random B.empty ch.M.key_share));
  assert ((match ch.M.server_name with | Some h -> h | None -> B.empty) == B.empty);
  assert (Seq.equal
    (LP.serialize GCH.clientHello_serializer low)
    (client_hello_body_bytes
      ch.M.random
      (match ch.M.server_name with | Some h -> h | None -> B.empty)
      ch.M.key_share));
  lemma_synth_client_hello_none ch;
  assert (WS.synth_client_hello low == Some ch)
#pop-options

let lemma_lp_ch_low_body_some
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256]})
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0 /\ ch.M.server_name == Some hostname})
  : Lemma
      (let low = mk_ch_low_some ch hostname in
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (client_hello_body_bytes
                   ch.M.random
                   (match ch.M.server_name with
                    | Some h -> h
                    | None -> B.empty)
                   ch.M.key_share))
=
  assert_norm (mk_ch_low_some ch hostname ==
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = ch.M.random;
      GCH.legacy_session_id = B.empty;
      GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
      GCH.legacy_compression_methods = B.of_list [0uy];
      GCH.extensions = mk_ext_list_some hostname ch.M.key_share });
  lemma_lp_ch_low_bytes_some ch hostname

let lemma_lp_ch_low_body_none
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                       ch.M.server_name == None})
  : Lemma
      (let low = mk_ch_low_none ch in
       Seq.equal (LP.serialize GCH.clientHello_serializer low)
                 (client_hello_body_bytes
                   ch.M.random
                   (match ch.M.server_name with
                    | Some h -> h
                    | None -> B.empty)
                   ch.M.key_share))
=
  assert_norm (mk_ch_low_none ch ==
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = ch.M.random;
      GCH.legacy_session_id = B.empty;
      GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
      GCH.legacy_compression_methods = B.of_list [0uy];
      GCH.extensions = mk_ext_list_none ch.M.key_share });
  lemma_lp_ch_low_bytes_none ch

let lemma_lp_ch_low_synth_some
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256]})
  (hostname: B.bytes{B.length hostname <= 255 /\ B.length hostname > 0 /\ ch.M.server_name == Some hostname})
  : Lemma
      (let low = mk_ch_low_some ch hostname in
       WS.synth_client_hello low == Some ch)
=
  assert_norm (mk_ch_low_some ch hostname ==
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = ch.M.random;
      GCH.legacy_session_id = B.empty;
      GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
      GCH.legacy_compression_methods = B.of_list [0uy];
      GCH.extensions = mk_ext_list_some hostname ch.M.key_share });
  lemma_lp_ch_low_bytes_some ch hostname

let lemma_lp_ch_low_synth_none
  (ch: M.client_hello{B.length ch.M.random == 32 /\ B.length ch.M.key_share == 32 /\
                       ch.M.cipher_suites == [T.TLS_CHACHA20_POLY1305_SHA256] /\
                       ch.M.signature_schemes == [T.RsaPssRsaeSha256] /\
                       ch.M.server_name == None})
  : Lemma
      (let low = mk_ch_low_none ch in
       WS.synth_client_hello low == Some ch)
=
  assert_norm (mk_ch_low_none ch ==
    { GCH.legacy_version = GPV.TLS_1p2;
      GCH.random = ch.M.random;
      GCH.legacy_session_id = B.empty;
      GCH.cipher_suites = [GCS.TLS_CHACHA20_POLY1305_SHA256];
      GCH.legacy_compression_methods = B.of_list [0uy];
      GCH.extensions = mk_ext_list_none ch.M.key_share });
  lemma_lp_ch_low_bytes_none ch
