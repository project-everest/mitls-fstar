module TLS13.Wire.Spec.Reveal
// Generated module friends BEFORE TLS13.Wire.Spec (which imports them).
// Ordering matters: body_finished.fsti opens Finished, so Finished must be
// friended first; GHS.fsti includes body_finished, so body_finished must
// come before GHS; then WS (which imports GHS etc.) can be friended last.
friend TLS13.Wire.Generated.Finished
friend TLS13.Wire.Generated.Handshake_body_finished
friend TLS13.Wire.Generated.HandshakeType
friend TLS13.Wire.Generated.ProtocolVersion
friend TLS13.Wire.Generated.Random
friend TLS13.Wire.Generated.CipherSuite
friend TLS13.Wire.Generated.ClientHello_legacy_session_id
friend TLS13.Wire.Generated.ClientHello_cipher_suites
friend TLS13.Wire.Generated.ClientHello_legacy_compression_methods
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
friend TLS13.Wire.Generated.ClientHello_extensions
friend TLS13.Wire.Generated.ClientHello
friend TLS13.Wire.Generated.Handshake
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module CS = TLS13.Spec.ConnectionState
module M = TLS13.Messages
module T = TLS13.Types
module H = TLS13.Handshake.Spec
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
open FStar.Classical.Sugar
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module WS = TLS13.Wire.Spec
module GHS = TLS13.Wire.Generated.Handshake
module GFinished = TLS13.Wire.Generated.Finished
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
module GCH = TLS13.Wire.Generated.ClientHello
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GSN = TLS13.Wire.Generated.ServerName
module HT = TLS13.Wire.Generated.HandshakeType
module LP = LowParse.Spec
// Additional aliases needed for LP serializer expansion proofs
module E = FStar.Endianness
module GRandom = TLS13.Wire.Generated.Random
module GSID = TLS13.Wire.Generated.ClientHello_legacy_session_id
module GComp = TLS13.Wire.Generated.ClientHello_legacy_compression_methods
module GCCS = TLS13.Wire.Generated.ClientHello_cipher_suites
module GET = TLS13.Wire.Generated.ExtensionType
module GSG = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_groups
module GNGL = TLS13.Wire.Generated.NamedGroupList
module GSSL = TLS13.Wire.Generated.SignatureSchemeList
module GSA = TLS13.Wire.Generated.ExtensionClientHello_extension_data_signature_algorithms
module GSV = TLS13.Wire.Generated.SupportedVersionsClientHello
module GSVE = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_versions
module GKSEKE = TLS13.Wire.Generated.KeyShareEntry_key_exchange
module GKSCH = TLS13.Wire.Generated.KeyShareClientHello
module GKS = TLS13.Wire.Generated.ExtensionClientHello_extension_data_key_share
module GNT = TLS13.Wire.Generated.NameType
module GHN = TLS13.Wire.Generated.HostName
module GSNL = TLS13.Wire.Generated.ServerNameList
module GSNE = TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
module GCHEXT = TLS13.Wire.Generated.ClientHello_extensions
module GSNM = TLS13.Wire.Generated.ServerName

module RU = TLS13.Wire.Spec.Reveal.Util
module RR = TLS13.Wire.Spec.Reveal.Record
module RF = TLS13.Wire.Spec.Reveal.Finished
module RCV = TLS13.Wire.Spec.Reveal.CertificateVerify
module RA = TLS13.Wire.Spec.Reveal.Alert
module RCH = TLS13.Wire.Spec.Reveal.ClientHello

let byte = RR.byte

let lemma_byte_value n =
  RR.lemma_byte_value n

let lemma_ptm_change_cipher_spec = RR.lemma_ptm_change_cipher_spec

let lemma_ptm_application_data = RR.lemma_ptm_application_data

let lemma_parse_plaintext_fragment_len = RR.lemma_parse_plaintext_fragment_len

let u8 n = WS.u8 n

let u16 n = WS.u16 n

let u24 n = WS.u24 n

let lemma_u24_reveal n =
  let w0 = WS.byte (n / 65536) in
  let w1 = WS.byte (n / 256) in
  let w2 = WS.byte n in
  let r0 = RR.byte (n / 65536) in
  let r1 = RR.byte (n / 256) in
  let r2 = RR.byte n in
  WS.lemma_byte_v (n / 65536);
  WS.lemma_byte_v (n / 256);
  WS.lemma_byte_v n;
  RR.lemma_byte_value (n / 65536);
  RR.lemma_byte_value (n / 256);
  RR.lemma_byte_value n;
  U8.v_inj w0 r0;
  U8.v_inj w1 r1;
  U8.v_inj w2 r2

let lemma_serialize_tls_message_handshake hs = ()

let content_type_byte = RR.content_type_byte

let lemma_content_type_byte_value = RR.lemma_content_type_byte_value

let serialize_record_header = RR.serialize_record_header

let lemma_serialize_record_reveal = RR.lemma_serialize_record_reveal

let lemma_serialize_application_data_header_reveal = RR.lemma_serialize_application_data_header_reveal

let lemma_serialize_handshake_record_header_reveal = RR.lemma_serialize_handshake_record_header_reveal

let lemma_application_data_record_aad = RR.lemma_application_data_record_aad

let lemma_serialize_application_data_record_reveal = RR.lemma_serialize_application_data_record_reveal

let lemma_application_data_record_header = RR.lemma_application_data_record_header

let application_data_record_header_bytes = RR.application_data_record_header_bytes
let lemma_application_data_record_header_bytes = RR.lemma_application_data_record_header_bytes
let lemma_application_data_record_header_bytes_reveal = RR.lemma_application_data_record_header_bytes_reveal
let lemma_parse_application_data_record_header_bytes = RR.lemma_parse_application_data_record_header_bytes
let lemma_serialize_plaintext_reveal = RR.lemma_serialize_plaintext_reveal

let lemma_plaintext_roundtrip_reveal = RR.lemma_plaintext_roundtrip_reveal

let lemma_serialize_finished_reveal = RF.lemma_serialize_finished_reveal

let lemma_parse_finished_handshake = RF.lemma_parse_finished_handshake
let lemma_serialize_server_certificate_verify_input_reveal = RCV.lemma_serialize_server_certificate_verify_input_reveal

let certificate_verify_context_with_zero = RCV.certificate_verify_context_with_zero

let lemma_certificate_verify_context_with_zero_literal = RCV.lemma_certificate_verify_context_with_zero_literal

let certificate_verify_context_byte = RCV.certificate_verify_context_byte

let lemma_certificate_verify_context_byte = RCV.lemma_certificate_verify_context_byte

let lemma_certificate_verify_context_index_0 = RCV.lemma_certificate_verify_context_index_0
let lemma_certificate_verify_context_index_1 = RCV.lemma_certificate_verify_context_index_1
let lemma_certificate_verify_context_index_2 = RCV.lemma_certificate_verify_context_index_2
let lemma_certificate_verify_context_index_3 = RCV.lemma_certificate_verify_context_index_3
let lemma_certificate_verify_context_index_4 = RCV.lemma_certificate_verify_context_index_4
let lemma_certificate_verify_context_index_5 = RCV.lemma_certificate_verify_context_index_5
let lemma_certificate_verify_context_index_6 = RCV.lemma_certificate_verify_context_index_6
let lemma_certificate_verify_context_index_7 = RCV.lemma_certificate_verify_context_index_7
let lemma_certificate_verify_context_index_8 = RCV.lemma_certificate_verify_context_index_8
let lemma_certificate_verify_context_index_9 = RCV.lemma_certificate_verify_context_index_9
let lemma_certificate_verify_context_index_10 = RCV.lemma_certificate_verify_context_index_10
let lemma_certificate_verify_context_index_11 = RCV.lemma_certificate_verify_context_index_11
let lemma_certificate_verify_context_index_12 = RCV.lemma_certificate_verify_context_index_12
let lemma_certificate_verify_context_index_13 = RCV.lemma_certificate_verify_context_index_13
let lemma_certificate_verify_context_index_14 = RCV.lemma_certificate_verify_context_index_14
let lemma_certificate_verify_context_index_15 = RCV.lemma_certificate_verify_context_index_15
let lemma_certificate_verify_context_index_16 = RCV.lemma_certificate_verify_context_index_16
let lemma_certificate_verify_context_index_17 = RCV.lemma_certificate_verify_context_index_17
let lemma_certificate_verify_context_index_18 = RCV.lemma_certificate_verify_context_index_18
let lemma_certificate_verify_context_index_19 = RCV.lemma_certificate_verify_context_index_19
let lemma_certificate_verify_context_index_20 = RCV.lemma_certificate_verify_context_index_20
let lemma_certificate_verify_context_index_21 = RCV.lemma_certificate_verify_context_index_21
let lemma_certificate_verify_context_index_22 = RCV.lemma_certificate_verify_context_index_22
let lemma_certificate_verify_context_index_23 = RCV.lemma_certificate_verify_context_index_23
let lemma_certificate_verify_context_index_24 = RCV.lemma_certificate_verify_context_index_24
let lemma_certificate_verify_context_index_25 = RCV.lemma_certificate_verify_context_index_25
let lemma_certificate_verify_context_index_26 = RCV.lemma_certificate_verify_context_index_26
let lemma_certificate_verify_context_index_27 = RCV.lemma_certificate_verify_context_index_27
let lemma_certificate_verify_context_index_28 = RCV.lemma_certificate_verify_context_index_28
let lemma_certificate_verify_context_index_29 = RCV.lemma_certificate_verify_context_index_29
let lemma_certificate_verify_context_index_30 = RCV.lemma_certificate_verify_context_index_30
let lemma_certificate_verify_context_index_31 = RCV.lemma_certificate_verify_context_index_31
let lemma_certificate_verify_context_index_32 = RCV.lemma_certificate_verify_context_index_32
let lemma_certificate_verify_context_index_33 = RCV.lemma_certificate_verify_context_index_33

let lemma_serialize_server_certificate_verify_input_bytes = RCV.lemma_serialize_server_certificate_verify_input_bytes

#push-options "--z3rlimit 20"
let lemma_serialize_client_hello_reveal (hello:M.client_hello{B.length hello.M.body == 0}) =
  let body = WS.serialize_client_hello hello in
  WS.lemma_byte_v 1;
  assert_norm (U8.v 1uy == 1);
  assert (U8.v (WS.byte 1) == U8.v 1uy);
  U8.v_inj (WS.byte 1) 1uy;
  RU.lemma_u8_reveal 1;
  assert (WS.byte 1 == 1uy);
  assert (B.singleton (WS.byte 1) == B.singleton 1uy);
  RU.lemma_singleton_of_list 1uy;
  assert (Seq.equal (B.singleton 1uy) (B.of_list [1uy]));
  Seq.lemma_eq_elim (B.singleton 1uy) (B.of_list [1uy])
#pop-options

let client_hello_byte n = RCH.client_hello_byte n

let lemma_client_hello_byte_v n = RCH.lemma_client_hello_byte_v n

let client_hello_common_extensions_bytes key_share =
  RCH.client_hello_common_extensions_bytes key_share

let client_hello_server_name_extension_bytes hostname =
  RCH.client_hello_server_name_extension_bytes hostname

let client_hello_extensions_bytes hostname key_share =
  RCH.client_hello_extensions_bytes hostname key_share

let client_hello_prefix_bytes body_len extensions_len random =
  RCH.client_hello_prefix_bytes body_len extensions_len random

let client_hello_body_bytes random hostname key_share =
  RCH.client_hello_body_bytes random hostname key_share

let client_hello_handshake_bytes random hostname key_share =
  RCH.client_hello_handshake_bytes random hostname key_share

let lemma_client_hello_common_extensions_bytes_reveal key_share =
  RCH.lemma_client_hello_common_extensions_bytes_reveal key_share

let lemma_client_hello_extensions_bytes_shape hostname key_share =
  RCH.lemma_client_hello_extensions_bytes_shape hostname key_share

let lemma_client_hello_server_name_extension_bytes_reveal hostname =
  RCH.lemma_client_hello_server_name_extension_bytes_reveal hostname

let lemma_client_hello_server_name_extension_bytes_empty hostname =
  RCH.lemma_client_hello_server_name_extension_bytes_empty hostname

let lemma_client_hello_prefix_bytes_reveal body_len extensions_len random =
  RCH.lemma_client_hello_prefix_bytes_reveal body_len extensions_len random

let lemma_client_hello_common_extensions_len key_share =
  RCH.lemma_client_hello_common_extensions_len key_share

let lemma_client_hello_server_name_extension_len hostname =
  RCH.lemma_client_hello_server_name_extension_len hostname

let lemma_client_hello_extensions_len hostname key_share =
  RCH.lemma_client_hello_extensions_len hostname key_share

let lemma_client_hello_handshake_bytes_prefix random hostname key_share =
  RCH.lemma_client_hello_handshake_bytes_prefix random hostname key_share

let lemma_client_hello_handshake_bytes_reveal hello =
  RCH.lemma_client_hello_handshake_bytes_reveal hello

let lemma_ptm_alert = RA.lemma_ptm_alert

let lemma_synth_signature_scheme s = ()

let lemma_ptm_handshake_some fragment v m =
  assert (WS.parse_handshake fragment == Some (m, B.length fragment))

let lemma_handshake_synth_finished b =
  WS.lemma_synth_handshake_msg_finished b

let lemma_handshake_synth_certificate_verify b =
  WS.lemma_synth_handshake_msg_certificate_verify b

let lemma_handshake_synth_key_update b =
  WS.lemma_synth_handshake_msg_key_update b

let lemma_handshake_synth_client_hello b =
  WS.lemma_synth_handshake_msg_client_hello b

(* a*65536 + b*256 + c == 1 with 0 <= a,b,c <= 255 forces a=b=0, c=1.
   (multiplication by literal constants is linear, so SMT handles this.) *)
let lemma_u24_one (input:B.bytes{B.length input >= 4})
  : Lemma (WS.read_u24 input 1 == 1 <==>
           (U8.v (Seq.index input 1) == 0 /\
            U8.v (Seq.index input 2) == 0 /\
            U8.v (Seq.index input 3) == 1))
= WS.lemma_read_u24_one input

let lemma_parse_key_update_def input =
  WS.lemma_parse_key_update_def input

let lemma_parse_ignored_post_handshake_def input =
  WS.lemma_parse_ignored_post_handshake_def input

let lemma_parse_handshake_none_of_lp_none fragment =
  WS.lemma_parse_handshake_none_of_lp_none fragment

let lemma_parse_handshake_none_of_synth_none fragment v consumed =
  WS.lemma_parse_handshake_none_of_synth_none fragment v consumed

let lemma_ptm_handshake_fallback fragment =
  WS.lemma_ptm_handshake_fallback fragment


let lemma_handshake_synth_encrypted_extensions b =
  WS.lemma_synth_handshake_msg_encrypted_extensions b

let lemma_synth_ee_nil () =
  WS.lemma_synth_encrypted_extensions_nil ()

let lemma_synth_ee_cons_non_alpn e tl =
  WS.lemma_synth_encrypted_extensions_cons_non_alpn e tl

let lemma_synth_ee_cons_alpn pnl tl =
  WS.lemma_synth_encrypted_extensions_cons_alpn pnl tl
let rec list_drop (#a:Type) (n:nat) (l:list a) : Tot (list a) (decreases n) =
  if n <= 0 then l
  else (
    assert (n > 0);
    assert (0 <= n - 1);
    match l with
    | [] -> []
    | _ :: tl -> list_drop (n - 1) tl
  )

let lemma_list_drop_zero (#a:Type) (l:list a)
  : Lemma (ensures list_drop 0 l == l)
  = ()

let lemma_list_drop_cons_succ (#a:Type) (hd:a) (tl:list a) (n:nat)
  : Lemma (ensures list_drop (n + 1) (hd :: tl) == list_drop n tl)
  =
  assert (n + 1 > 0);
  assert (0 <= (n + 1) - 1);
  assert ((n + 1) - 1 == n)

let lemma_list_index_tail (#a:Type) (l:list a) (i:nat)
  : Lemma (requires i > 0 /\ i < FStar.List.Tot.length l)
          (ensures FStar.List.Tot.index l i == FStar.List.Tot.index (FStar.List.Tot.tl l) (i - 1))
  =
  match i with
  | 0 -> ()
  | _ -> ()

let lemma_list_index_cons_succ (#a:Type) (hd:a) (tl:list a) (i:nat)
  : Lemma (requires i < FStar.List.Tot.length tl)
          (ensures FStar.List.Tot.index (hd :: tl) (i + 1) == FStar.List.Tot.index tl i)
  =
  lemma_list_index_tail (hd :: tl) (i + 1);
  assert (FStar.List.Tot.tl (hd :: tl) == tl);
  assert ((i + 1) - 1 == i)

let rec lemma_list_drop_index (#a:Type) (l:list a) (i:nat)
  : Lemma (requires i < FStar.List.Tot.length l)
          (ensures list_drop i l == FStar.List.Tot.index l i :: list_drop (i + 1) l)
          (decreases i)
  =
  if i <= 0 then (
    assert (i == 0);
    match l with
    | [] -> assert False
    | hd :: tl ->
      assert (list_drop i l == hd :: tl);
      assert (FStar.List.Tot.index l i == hd);
      lemma_list_drop_cons_succ hd tl 0;
      assert (list_drop (i + 1) l == tl)
  )
  else (
    assert (i > 0);
    assert (0 <= i - 1);
    match l with
    | [] -> assert False
    | hd :: tl ->
      assert (i - 1 < FStar.List.Tot.length tl);
      lemma_list_drop_index tl (i - 1);
      assert ((i - 1) + 1 == i);
      lemma_list_drop_cons_succ hd tl (i - 1);
      lemma_list_index_cons_succ hd tl (i - 1);
      lemma_list_drop_cons_succ hd tl i
  )

let rec lemma_list_drop_length (#a:Type) (l:list a)
  : Lemma (ensures list_drop (FStar.List.Tot.length l) l == [])
          (decreases l)
  =
  match l with
  | [] -> ()
  | _ :: tl -> lemma_list_drop_length tl

let lemma_alpn_first_name_index0 pnl = ()

(* --- ServerHello reveal interface --------------------------------------- *)

let reveal_key_exchange_to_key32 ke = WS.key_exchange_to_key32 ke

let lemma_reveal_key_exchange_to_key32 ke = WS.lemma_key_exchange_to_key32 ke

let reveal_sh_key_share l saw key_share = WS.sh_key_share l saw key_share

let lemma_sh_key_share_nil saw key_share = WS.lemma_sh_key_share_nil saw key_share

let lemma_sh_key_share_cons e tl saw key_share =
  WS.lemma_sh_key_share_cons e tl saw key_share;
  match e with
  | GESH.Extension_data_supported_versions sv ->
    assert (reveal_sh_key_share tl true key_share == WS.sh_key_share tl true key_share)
  | GESH.Extension_data_key_share kse ->
    assert (reveal_key_exchange_to_key32 kse.GKSE.key_exchange ==
            WS.key_exchange_to_key32 kse.GKSE.key_exchange);
    (match reveal_key_exchange_to_key32 kse.GKSE.key_exchange with
     | Some k ->
       assert (reveal_sh_key_share tl saw (Some k) == WS.sh_key_share tl saw (Some k))
     | None -> ())
  | _ ->
    assert (reveal_sh_key_share tl saw key_share == WS.sh_key_share tl saw key_share)

let lemma_handshake_synth_server_hello_bad_version b =
  WS.lemma_synth_handshake_msg_server_hello_bad_version b

let lemma_handshake_synth_server_hello_hrr b shb =
  WS.lemma_synth_handshake_msg_server_hello_hrr b shb

let lemma_handshake_synth_server_hello_sh b sf =
  WS.lemma_synth_handshake_msg_server_hello_sh b sf;
  assert (reveal_sh_key_share sf.GSHB.value.GSHBody.extensions false None ==
          WS.sh_key_share sf.GSHB.value.GSHBody.extensions false None);
  if U8.v sf.GSHB.value.GSHBody.legacy_compression_method <> 0 then ()
  else
    match reveal_sh_key_share sf.GSHB.value.GSHBody.extensions false None with
    | Some _ ->
      (match sf.GSHB.value.GSHBody.cipher_suite with
       | GCS.TLS_CHACHA20_POLY1305_SHA256 -> ()
       | GCS.Unknown_cipherSuite _ -> ())
    | None -> ()

(* --- Certificate reveal interface --------------------------------------- *)

let reveal_synth_cert_chain l = WS.synth_cert_chain l

let reveal_cert_chain_total_bytes chain = WS.cert_chain_total_bytes chain

let lemma_synth_cert_chain_nil () = WS.lemma_synth_cert_chain_nil ()

let lemma_synth_cert_chain_cons e tl = WS.lemma_synth_cert_chain_cons e tl

let lemma_synth_cert_chain_length l = WS.lemma_synth_cert_chain_length l

let lemma_cert_chain_total_bytes_nil () = WS.lemma_cert_chain_total_bytes_nil ()

let lemma_cert_chain_total_bytes_snoc chain x =
  WS.lemma_cert_chain_total_bytes_snoc chain x

let lemma_cert_chain_total_bytes_prefix_le prefix x rest =
  WS.lemma_cert_chain_total_bytes_prefix_le prefix x rest

let lemma_handshake_synth_certificate b =
  WS.lemma_synth_handshake_msg_certificate b;
  assert (reveal_synth_cert_chain (b.GCert.certificate_list <: list GCE.certificateEntry) ==
          WS.synth_cert_chain (b.GCert.certificate_list <: list GCE.certificateEntry));
  let chain = reveal_synth_cert_chain (b.GCert.certificate_list <: list GCE.certificateEntry) in
  assert (reveal_cert_chain_total_bytes chain == WS.cert_chain_total_bytes chain)

(* ---- ClientHello parsing reveals ---------------------------------------- *)

let reveal_synth_cipher_suites l = WS.synth_cipher_suites l

let lemma_reveal_synth_cipher_suites_nil () = WS.lemma_synth_cipher_suites_nil ()

let lemma_reveal_synth_cipher_suites_cons c tl = WS.lemma_synth_cipher_suites_cons c tl

let reveal_synth_sig_schemes l = WS.synth_sig_schemes l

let lemma_reveal_synth_sig_schemes_nil () = WS.lemma_synth_sig_schemes_nil ()

let lemma_reveal_synth_sig_schemes_cons s tl = WS.lemma_synth_sig_schemes_cons s tl

let reveal_ch_server_name snl = WS.ch_server_name snl

let lemma_reveal_ch_server_name_nil () = WS.lemma_ch_server_name_nil ()

let lemma_reveal_ch_server_name_host h tl = WS.lemma_ch_server_name_host h tl

let reveal_ch_find_key_share l = WS.ch_find_key_share l

let lemma_reveal_ch_find_key_share_nil () = WS.lemma_ch_find_key_share_nil ()

let lemma_reveal_ch_find_key_share_cons e tl =
  WS.lemma_ch_find_key_share_cons e tl;
  assert (reveal_key_exchange_to_key32 e.GKSE.key_exchange ==
          WS.key_exchange_to_key32 e.GKSE.key_exchange);
  (match WS.key_exchange_to_key32 e.GKSE.key_exchange with
   | Some k -> assert (reveal_ch_find_key_share tl == WS.ch_find_key_share tl)
   | None -> assert (reveal_ch_find_key_share tl == WS.ch_find_key_share tl))

let reveal_ch_extensions l sn ks sv ss = WS.ch_extensions l sn ks sv ss

let lemma_reveal_ch_extensions_nil sn ks sv ss = WS.lemma_ch_extensions_nil sn ks sv ss

let lemma_reveal_ch_extensions_cons_sn snl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_sn snl tl sn ks sv ss;
  assert (reveal_ch_server_name snl == WS.ch_server_name snl);
  (match WS.ch_server_name snl with
   | Some name ->
     assert (reveal_ch_extensions tl (Some name) ks sv ss ==
             WS.ch_extensions tl (Some name) ks sv ss)
   | None -> ())

let lemma_reveal_ch_extensions_cons_sg sgl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_sg sgl tl sn ks sv ss;
  assert (reveal_ch_extensions tl sn ks sv ss == WS.ch_extensions tl sn ks sv ss)

let lemma_reveal_ch_extensions_cons_sa ssl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_sa ssl tl sn ks sv ss;
  assert (reveal_synth_sig_schemes ssl == WS.synth_sig_schemes ssl);
  assert (reveal_ch_extensions tl sn ks sv (WS.synth_sig_schemes ssl) ==
          WS.ch_extensions tl sn ks sv (WS.synth_sig_schemes ssl))

let lemma_reveal_ch_extensions_cons_ks kscl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_ks kscl tl sn ks sv ss;
  assert (reveal_ch_find_key_share kscl == WS.ch_find_key_share kscl);
  (match WS.ch_find_key_share kscl with
   | Some k ->
     assert (reveal_ch_extensions tl sn (Some k) sv ss ==
             WS.ch_extensions tl sn (Some k) sv ss)
   | None -> ())

let lemma_reveal_ch_extensions_cons_sv svl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_sv svl tl sn ks sv ss;
  assert (reveal_ch_extensions tl sn ks true ss == WS.ch_extensions tl sn ks true ss)

let lemma_reveal_ch_extensions_cons_other e tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_other e tl sn ks sv ss;
  assert (reveal_ch_extensions tl sn ks sv ss == WS.ch_extensions tl sn ks sv ss)

let lemma_synth_client_hello_reveal c =
  WS.lemma_synth_client_hello c;
  let cs : list GCS.cipherSuite = c.GCH.cipher_suites in
  let ext : list GECH.extensionClientHello = c.GCH.extensions in
  assert (reveal_ch_extensions ext None None false [] == WS.ch_extensions ext None None false []);
  assert (reveal_synth_cipher_suites cs == WS.synth_cipher_suites cs)
