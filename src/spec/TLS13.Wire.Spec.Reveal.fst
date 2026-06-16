module TLS13.Wire.Spec.Reveal
// Generated module friends BEFORE TLS13.Wire.Spec (which imports them).
// Ordering matters: body_finished.fsti opens Finished, so Finished must be
// friended first; GHS.fsti includes body_finished, so body_finished must
// come before GHS; then WS (which imports GHS etc.) can be friended last.
friend TLS13.Wire.Generated.Finished
friend TLS13.Wire.Generated.Handshake_body_finished
friend TLS13.Wire.Generated.HandshakeType
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
module HT = TLS13.Wire.Generated.HandshakeType
module LP = LowParse.Spec

let lemma_ptm_change_cipher_spec fragment =
  if B.length fragment = 1 && U8.v (Seq.index fragment 0) = 1
  then assert (WS.nat_of_byte (Seq.index fragment 0) == 1)
  else ()

let lemma_ptm_application_data fragment = ()

let lemma_parse_plaintext_fragment_len input =
  match WS.parse_plaintext input with
  | Some pt -> Seq.lemma_len_slice input 0 (B.length input - 1)
  | None -> ()

let u8 n = WS.u8 n

let u16 n = WS.u16 n

let u24 n = WS.u24 n

let content_type_byte ct = WS.byte (WS.content_type_to_byte ct)

let lemma_content_type_byte_value ct =
  match ct with
  | T.ChangeCipherSpec -> ()
  | T.Alert -> ()
  | T.Handshake -> ()
  | T.ApplicationData -> ()

let serialize_record_header content_type fragment_len =
  B.append
    (u8 (WS.content_type_to_byte content_type))
    (B.append (u16 0x0303) (u16 fragment_len))

let lemma_serialize_record_reveal content_type fragment = ()

let lemma_serialize_application_data_header_reveal fragment_len = ()

let lemma_serialize_handshake_record_header_reveal fragment_len =
  lemma_content_type_byte_value T.Handshake;
  assert_norm (U8.v 0x16uy == 0x16);
  U8.v_inj (content_type_byte T.Handshake) 0x16uy

private let lemma_slice_append_left (#a:eqtype) (prefix:Seq.seq a) (suffix:Seq.seq a)
  : Lemma (ensures Seq.equal (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) prefix)
=
  Seq.lemma_len_append prefix suffix;
  Seq.lemma_len_slice (Seq.append prefix suffix) 0 (Seq.length prefix);
  assert (forall (i:nat{i < Seq.length prefix}).
    Seq.index (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) i ==
    Seq.index prefix i);
  Seq.lemma_eq_intro (Seq.slice (Seq.append prefix suffix) 0 (Seq.length prefix)) prefix

let lemma_application_data_record_aad fragment =
  let header = serialize_record_header T.ApplicationData (B.length fragment) in
  lemma_serialize_record_reveal T.ApplicationData fragment;
  Seq.lemma_eq_elim
    (WS.serialize_record T.ApplicationData fragment)
    (B.append header fragment);
  lemma_slice_append_left header fragment;
  lemma_serialize_application_data_header_reveal (B.length fragment);
  Seq.lemma_eq_elim
    header
    (CS.application_data_record_header (B.length fragment))

let lemma_serialize_application_data_record_reveal fragment =
  let header = serialize_record_header T.ApplicationData (B.length fragment) in
  lemma_serialize_record_reveal T.ApplicationData fragment;
  lemma_serialize_application_data_header_reveal (B.length fragment);
  Seq.lemma_eq_elim
    header
    (CS.application_data_record_header (B.length fragment))

let lemma_application_data_record_header fragment_len =
  lemma_serialize_application_data_header_reveal fragment_len;
  Seq.lemma_eq_elim
    (serialize_record_header T.ApplicationData fragment_len)
    (CS.application_data_record_header fragment_len);
  WS.lemma_read_u16_u16 0x0303;
  WS.lemma_read_u16_u16 fragment_len

let application_data_record_header_bytes fragment_len =
  B.of_list [
    0x17uy;
    0x03uy;
    0x03uy;
    U8.uint_to_t ((fragment_len / 256) % 256);
    U8.uint_to_t (fragment_len % 256)
  ]

let lemma_application_data_record_header_bytes fragment_len =
  lemma_application_data_record_header fragment_len;
  WS.lemma_read_u16_u16 0x0303;
  WS.lemma_read_u16_u16 fragment_len

let lemma_application_data_record_header_bytes_reveal fragment_len = ()

let lemma_serialize_plaintext_reveal pt = ()

private let lemma_slice_append_single (#a:eqtype) (s:Seq.seq a) (x:a)
  : Lemma (ensures Seq.equal (Seq.slice (Seq.append s (Seq.create 1 x)) 0 (Seq.length s)) s)
=
  Seq.lemma_len_append s (Seq.create 1 x);
  Seq.lemma_len_slice (Seq.append s (Seq.create 1 x)) 0 (Seq.length s);
  assert (forall (i:nat{i < Seq.length s}).
    Seq.index (Seq.slice (Seq.append s (Seq.create 1 x)) 0 (Seq.length s)) i ==
    Seq.index s i);
  Seq.lemma_eq_intro (Seq.slice (Seq.append s (Seq.create 1 x)) 0 (Seq.length s)) s

let lemma_plaintext_roundtrip_reveal ct fragment =
  lemma_serialize_plaintext_reveal { M.content_type = ct; M.fragment = fragment };
  lemma_slice_append_single fragment (content_type_byte ct);
  lemma_content_type_byte_value ct;
  match ct with
  | T.ChangeCipherSpec -> ()
  | T.Alert -> ()
  | T.Handshake -> ()
  | T.ApplicationData -> ()

let lemma_serialize_finished_reveal fin = ()

(* Prove that WS.serialize_handshake (M.Finished fin) parses back to
   (Body_finished vd, 36) under GHS.handshake_parser, by decomposing each
   layer of the LP sum/vldata parsers with concrete LP spec lemmas. *)
module E = FStar.Endianness

#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 200"

(* Sub-lemma: the vldata body for Finished serializes to [0;0;32] ++ vd *)
private let lemma_vldata_bytes (vd: GHS.handshake_body_finished) :
  Lemma (LP.serialize GHS.handshake_body_finished_serializer vd ==
         Seq.append (B.of_list [0uy; 0uy; 32uy]) vd) =
  LP.serialize_bounded_integer_spec 3 (U32.uint_to_t 32);
  E.n_to_be_be_to_n 3 (B.of_list [0uy; 0uy; 32uy]);
  E.reveal_be_to_n (B.of_list [0uy; 0uy; 32uy]);
  E.reveal_be_to_n (Seq.slice (B.of_list [0uy; 0uy; 32uy]) 0 2);
  E.reveal_be_to_n (Seq.slice (B.of_list [0uy; 0uy; 32uy]) 0 1);
  assert_norm (Seq.length (B.of_list [0uy; 0uy; 32uy]) = 3);
  assert_norm (Seq.index (B.of_list [0uy; 0uy; 32uy]) 2 = 32uy);
  assert_norm (Seq.index (B.of_list [0uy; 0uy; 32uy]) 1 = 0uy);
  assert_norm (Seq.index (B.of_list [0uy; 0uy; 32uy]) 0 = 0uy)

(* Sub-lemma: the handshake serializer produces the same bytes as WS.
   Chain of == equalities ends with Seq.lemma_eq_refl SMTPat closing the goal. *)
private let lemma_ghs_serialize_eq_ws (vd: GHS.handshake_body_finished) :
  Lemma (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_finished vd))
    (WS.serialize_handshake (M.Finished ({ M.verify_data = vd })))) =
  // Unfold sum serializer: S == tag_bytes ++ body_bytes
  LP.serialize_sum_eq
    GHS.handshake_sum HT.handshakeType_repr_serializer GHS.serialize_handshake_cases
    (GHS.Body_finished vd);
  // tag_bytes == LP.serialize HT.handshakeType_repr_serializer 20z
  LP.serialize_enum_key_eq
    HT.handshakeType_repr_serializer HT.handshakeType_enum HT.Finished;
  assert_norm (LP.enum_repr_of_key HT.handshakeType_enum HT.Finished == 20z);
  // With friend HT the normalizer reduces HT.handshakeType_repr_serializer to LP.serialize_u8.
  // serialize_u8_spec adds: Seq.equal (LP.serialize LP.serialize_u8 20z) (Seq.create 1 20uy)
  // -> via Seq.lemma_eq_elim SMTPat: LP.serialize LP.serialize_u8 20z == Seq.create 1 20uy
  LP.serialize_u8_spec 20z;
  // body_bytes == B.of_list [0;0;32] ++ vd
  lemma_vldata_bytes vd;
  // WS bytes Seq.equal [20;0;0;32] ++ vd -> via SMTPat: WS.serialize_handshake ... == [20;0;0;32] ++ vd
  lemma_serialize_finished_reveal ({ M.verify_data = vd });
  // Unfold B.of_list [20;0;0;32] = cons 20uy (B.of_list [0;0;32])
  //                                = Seq.create 1 20uy ++ B.of_list [0;0;32]
  Seq.lemma_seq_of_list_induction [20uy; 0uy; 0uy; 32uy];
  // append_assoc: (Seq.create 1 20uy ++ B.of_list [0;0;32]) ++ vd ==
  //                Seq.create 1 20uy ++ (B.of_list [0;0;32] ++ vd)
  Seq.append_assoc (Seq.create 1 20uy) (B.of_list [0uy; 0uy; 32uy]) vd
  // Now Z3 has S == F via transitivity.
  // Seq.lemma_eq_refl SMTPat (equal s1 s2 when s1 == s2) closes the Seq.equal goal.

#pop-options

#push-options "--z3rlimit 50"
let lemma_parse_finished_handshake fin =
  let vd : GHS.handshake_body_finished = fin.M.verify_data in
  LP.parse_serialize GHS.handshake_serializer (GHS.Body_finished vd);
  lemma_ghs_serialize_eq_ws vd;
  WS.lemma_serialize_finished_len fin
#pop-options

let lemma_serialize_server_certificate_verify_input_reveal transcript_hash = ()

/// The concrete list of 33 bytes for the TLS 1.3 server certificate verify context.
/// (Same bytes as H.certificate_verify_server_context.)
let cv_server_list : list U8.t = [
  0x54uy; 0x4cuy; 0x53uy; 0x20uy; 0x31uy; 0x2euy; 0x33uy; 0x2cuy;
  0x20uy; 0x73uy; 0x65uy; 0x72uy; 0x76uy; 0x65uy; 0x72uy; 0x20uy;
  0x43uy; 0x65uy; 0x72uy; 0x74uy; 0x69uy; 0x66uy; 0x69uy; 0x63uy;
  0x61uy; 0x74uy; 0x65uy; 0x56uy; 0x65uy; 0x72uy; 0x69uy; 0x66uy;
  0x79uy]

/// The 34-byte list as a FLAT list (no append) so List.Tot.index k needs only k+1
/// normalizer steps (max 34 for k=33), well within fuel 50.
let cv_context_list : list FStar.UInt8.t = [
  0x54uy; 0x4cuy; 0x53uy; 0x20uy; 0x31uy; 0x2euy; 0x33uy; 0x2cuy;
  0x20uy; 0x73uy; 0x65uy; 0x72uy; 0x76uy; 0x65uy; 0x72uy; 0x20uy;
  0x43uy; 0x65uy; 0x72uy; 0x74uy; 0x69uy; 0x66uy; 0x69uy; 0x63uy;
  0x61uy; 0x74uy; 0x65uy; 0x56uy; 0x65uy; 0x72uy; 0x69uy; 0x66uy;
  0x79uy; 0uy]

/// Helper: FStar.List.Tot.index of left part of append.
/// Preconditions include j < length (append l1 l2) to avoid subtyping issues
/// without requiring open FStar.List.Tot.Properties globally.
/// Marked opaque_to_smt so the fuel-based unrolling axioms don't appear in
/// Z3's background for every subsequent proof in this module.
#push-options "--initial_fuel 50 --max_fuel 50"
[@@"opaque_to_smt"]
let rec lemma_list_index_append_left
  (#a:Type) (l1 l2: list a) (j:nat)
  : Lemma
    (requires j < FStar.List.Tot.length l1 /\ j < FStar.List.Tot.length (FStar.List.Tot.append l1 l2))
    (ensures FStar.List.Tot.index (FStar.List.Tot.append l1 l2) j == FStar.List.Tot.index l1 j)
    (decreases j)
= match l1 with
  | hd :: tl ->
    if j = 0 then ()
    else lemma_list_index_append_left tl l2 (j-1)
#pop-options

/// certificate_verify_context_with_zero = B.of_list cv_context_list (34 bytes).
#push-options "--initial_fuel 50 --max_fuel 50"
let certificate_verify_context_with_zero = B.of_list cv_context_list
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 20"
let lemma_certificate_verify_context_with_zero_literal () = ()
#pop-options

/// Implement via List.Tot.index on the concrete list.
#push-options "--initial_fuel 50 --max_fuel 50"
let certificate_verify_context_byte i =
  FStar.List.Tot.index cv_context_list i
#pop-options

/// Proof: cv[i] == List.Tot.index cv_context_list i
/// via Seq.Properties.lemma_seq_of_list_index.
#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 100"
let lemma_certificate_verify_context_byte i =
  assert (FStar.List.Tot.length cv_context_list == 34);
  FStar.Seq.Properties.lemma_seq_of_list_index cv_context_list i
#pop-options

/// For each concrete i, Seq.index cv i == concrete byte.
#push-options "--initial_fuel 50 --max_fuel 50 --split_queries always --z3rlimit 100"
let lemma_certificate_verify_context_index_eq i =
  lemma_certificate_verify_context_byte i;
  match i with
  | 0  -> assert_norm (FStar.List.Tot.index cv_context_list  0 == 0x54uy)
  | 1  -> assert_norm (FStar.List.Tot.index cv_context_list  1 == 0x4cuy)
  | 2  -> assert_norm (FStar.List.Tot.index cv_context_list  2 == 0x53uy)
  | 3  -> assert_norm (FStar.List.Tot.index cv_context_list  3 == 0x20uy)
  | 4  -> assert_norm (FStar.List.Tot.index cv_context_list  4 == 0x31uy)
  | 5  -> assert_norm (FStar.List.Tot.index cv_context_list  5 == 0x2euy)
  | 6  -> assert_norm (FStar.List.Tot.index cv_context_list  6 == 0x33uy)
  | 7  -> assert_norm (FStar.List.Tot.index cv_context_list  7 == 0x2cuy)
  | 8  -> assert_norm (FStar.List.Tot.index cv_context_list  8 == 0x20uy)
  | 9  -> assert_norm (FStar.List.Tot.index cv_context_list  9 == 0x73uy)
  | 10 -> assert_norm (FStar.List.Tot.index cv_context_list 10 == 0x65uy)
  | 11 -> assert_norm (FStar.List.Tot.index cv_context_list 11 == 0x72uy)
  | 12 -> assert_norm (FStar.List.Tot.index cv_context_list 12 == 0x76uy)
  | 13 -> assert_norm (FStar.List.Tot.index cv_context_list 13 == 0x65uy)
  | 14 -> assert_norm (FStar.List.Tot.index cv_context_list 14 == 0x72uy)
  | 15 -> assert_norm (FStar.List.Tot.index cv_context_list 15 == 0x20uy)
  | 16 -> assert_norm (FStar.List.Tot.index cv_context_list 16 == 0x43uy)
  | 17 -> assert_norm (FStar.List.Tot.index cv_context_list 17 == 0x65uy)
  | 18 -> assert_norm (FStar.List.Tot.index cv_context_list 18 == 0x72uy)
  | 19 -> assert_norm (FStar.List.Tot.index cv_context_list 19 == 0x74uy)
  | 20 -> assert_norm (FStar.List.Tot.index cv_context_list 20 == 0x69uy)
  | 21 -> assert_norm (FStar.List.Tot.index cv_context_list 21 == 0x66uy)
  | 22 -> assert_norm (FStar.List.Tot.index cv_context_list 22 == 0x69uy)
  | 23 -> assert_norm (FStar.List.Tot.index cv_context_list 23 == 0x63uy)
  | 24 -> assert_norm (FStar.List.Tot.index cv_context_list 24 == 0x61uy)
  | 25 -> assert_norm (FStar.List.Tot.index cv_context_list 25 == 0x74uy)
  | 26 -> assert_norm (FStar.List.Tot.index cv_context_list 26 == 0x65uy)
  | 27 -> assert_norm (FStar.List.Tot.index cv_context_list 27 == 0x56uy)
  | 28 -> assert_norm (FStar.List.Tot.index cv_context_list 28 == 0x65uy)
  | 29 -> assert_norm (FStar.List.Tot.index cv_context_list 29 == 0x72uy)
  | 30 -> assert_norm (FStar.List.Tot.index cv_context_list 30 == 0x69uy)
  | 31 -> assert_norm (FStar.List.Tot.index cv_context_list 31 == 0x66uy)
  | 32 -> assert_norm (FStar.List.Tot.index cv_context_list 32 == 0x79uy)
  | _  -> assert_norm (FStar.List.Tot.index cv_context_list 33 == 0uy)
#pop-options

/// Private helper: Seq.equal cv (B.append H.cv_server_context (B.singleton 0uy)).
/// Proved element-by-element via forall_intro + Seq.lemma_eq_intro.
#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 100"
private let lemma_cv_eq_append ()
  : Lemma (Seq.equal certificate_verify_context_with_zero
    (B.append H.certificate_verify_server_context (B.singleton 0uy))) =
  assert_norm (H.certificate_verify_server_context == B.of_list cv_server_list);
  let h_cv = H.certificate_verify_server_context in
  let b_zero = B.singleton 0uy in
  let cv = certificate_verify_context_with_zero in
  let aux (i:nat{i<34}) : Lemma (Seq.index cv i == Seq.index (B.append h_cv b_zero) i) =
    lemma_certificate_verify_context_byte i;
    if i < 33 then (
      // Tell Z3 that cv_context_list = append cv_server_list [0uy] so that
      // lemma_list_index_append_left can connect cv_context_list[i] to cv_server_list[i].
      // Normalizer: append [33 bytes] [0uy] = 33 steps, well within fuel 50.
      assert_norm (cv_context_list == FStar.List.Tot.append cv_server_list [0uy]);
      assert_norm (FStar.List.Tot.length cv_server_list == 33);
      assert (FStar.List.Tot.length cv_context_list == 34);
      lemma_list_index_append_left cv_server_list [0uy] i;
      FStar.Seq.Properties.lemma_seq_of_list_index cv_server_list i;
      assert_norm (B.length h_cv == 33);
      FStar.Seq.Base.lemma_index_app1 h_cv b_zero i
    ) else (
      assert_norm (B.length h_cv == 33);
      FStar.Seq.Base.lemma_index_app2 h_cv b_zero 33;
      FStar.Seq.Base.lemma_index_create 1 0uy 0;
      assert_norm (FStar.List.Tot.index cv_context_list 33 == 0uy)
    )
  in
  FStar.Classical.forall_intro aux;
  Seq.lemma_eq_intro cv (B.append h_cv b_zero)
#pop-options

/// Main serializer lemma: uses lemma_cv_eq_append + Seq.append_assoc.
#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 20"
let lemma_serialize_server_certificate_verify_input_bytes transcript_hash =
  lemma_serialize_server_certificate_verify_input_reveal transcript_hash;
  lemma_cv_eq_append ();
  Seq.lemma_eq_elim certificate_verify_context_with_zero
    (B.append H.certificate_verify_server_context (B.singleton B.zero));
  let a = Seq.create 64 0x20uy in
  let h_cv = H.certificate_verify_server_context in
  let cv = certificate_verify_context_with_zero in
  Seq.append_assoc a h_cv (B.append (B.singleton B.zero) transcript_hash);
  Seq.append_assoc h_cv (B.singleton B.zero) transcript_hash;
  Seq.append_assoc a cv transcript_hash;
  Seq.lemma_eq_elim
    (WS.serialize_server_certificate_verify_input transcript_hash)
    (H.certificate_verify_input transcript_hash);
  Seq.lemma_eq_refl
    (WS.serialize_server_certificate_verify_input transcript_hash)
    (B.append (B.append a cv) transcript_hash)
#pop-options

#push-options "--z3rlimit 20"
let lemma_serialize_client_hello_reveal hello = ()
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 20"
let lemma_client_hello_common_extensions_len key_share =
  let supported_l : l:list B.byte{FStar.List.Tot.length l == 8} =
    [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy] in
  let supported = SeqP.createL supported_l in
  assert (supported == B.of_list supported_l);
  assert (B.length (B.of_list supported_l) == 8);
  let signature_l : l:list B.byte{FStar.List.Tot.length l == 8} =
    [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy] in
  let signature = SeqP.createL signature_l in
  assert (signature == B.of_list signature_l);
  assert (B.length (B.of_list signature_l) == 8);
  let key_header_l : l:list B.byte{FStar.List.Tot.length l == 10} =
    [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] in
  let key_header = SeqP.createL key_header_l in
  assert (key_header == B.of_list key_header_l);
  assert (B.length (B.of_list key_header_l) == 10);
  let common_suffix_l : l:list B.byte{FStar.List.Tot.length l == 7} =
    [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy] in
  let common_suffix = SeqP.createL common_suffix_l in
  assert (common_suffix == B.of_list common_suffix_l);
  assert (B.length (B.of_list common_suffix_l) == 7);
  Seq.lemma_len_append (B.of_list key_header_l) key_share;
  Seq.lemma_len_append
    (B.append (B.of_list key_header_l) key_share)
    (B.of_list common_suffix_l);
  Seq.lemma_len_append
    (B.of_list signature_l)
    (B.append
      (B.append (B.of_list key_header_l) key_share)
      (B.of_list common_suffix_l));
  Seq.lemma_len_append
    (B.of_list supported_l)
    (B.append
      (B.of_list signature_l)
      (B.append
        (B.append (B.of_list key_header_l) key_share)
        (B.of_list common_suffix_l)))

let lemma_client_hello_server_name_extension_len hostname =
  if B.length hostname = 0 then
    assert_norm (B.length B.empty == 0)
  else
    let sni_prefix_l : l:list B.byte{FStar.List.Tot.length l == 9} = [
        0uy; 0uy;
        client_hello_byte ((5 + B.length hostname) / 256);
        client_hello_byte (5 + B.length hostname);
        client_hello_byte ((3 + B.length hostname) / 256);
        client_hello_byte (3 + B.length hostname);
        0uy;
        client_hello_byte (B.length hostname / 256);
        client_hello_byte (B.length hostname)] in
    let sni_prefix = SeqP.createL sni_prefix_l in
    assert (sni_prefix == B.of_list sni_prefix_l);
    assert (B.length (B.of_list sni_prefix_l) == 9);
    Seq.lemma_len_append
      (B.of_list sni_prefix_l)
      hostname

let lemma_client_hello_extensions_len hostname key_share =
  lemma_client_hello_common_extensions_len key_share;
  lemma_client_hello_server_name_extension_len hostname;
  Seq.lemma_len_append
    (client_hello_server_name_extension_bytes hostname)
    (client_hello_common_extensions_bytes key_share)
#pop-options

private let client_hello_body_bytes_with_extensions
  (random:B.bytes)
  (extensions:B.bytes)
  : B.bytes =
  B.append
    (B.of_list [0x03uy; 0x03uy])
    (B.append
      random
      (B.append
        (B.of_list [0uy])
        (B.append
          (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
          (B.append
            (B.of_list [0uy])
            (B.append
              (B.of_list [
                client_hello_byte (B.length extensions / 256);
                client_hello_byte (B.length extensions)])
              extensions)))))

private let client_hello_hostname (hello:M.client_hello) : B.bytes =
  match hello.M.server_name with
  | Some h -> h
  | None -> B.empty

private let client_hello_expected_extensions (hello:M.client_hello) : B.bytes =
  client_hello_extensions_bytes (client_hello_hostname hello) hello.M.key_share

private let client_hello_ws_body_bytes (hello:M.client_hello) : GTot B.bytes =
  let extensions = client_hello_expected_extensions hello in
  WS.append6
    (WS.u16 0x0303)
    hello.M.random
    (WS.u8 0)
    (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
    (WS.u8 0)
    (B.append (WS.u16 (B.length extensions)) extensions)

private let client_hello_impl_body_bytes (hello:M.client_hello) : B.bytes =
  client_hello_body_bytes_with_extensions
    hello.M.random
    (client_hello_expected_extensions hello)

private let client_hello_public_body_bytes (hello:M.client_hello) : B.bytes =
  client_hello_body_bytes
    hello.M.random
    (client_hello_hostname hello)
    hello.M.key_share

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 20"
private let lemma_client_hello_body_bytes_with_extensions_reveal
  (random:B.bytes)
  (extensions:B.bytes)
  : Lemma (Seq.equal
    (WS.append6
      (WS.u16 0x0303)
      random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions))
    (client_hello_body_bytes_with_extensions random extensions))
=
  assert (Seq.equal (WS.u16 0x0303) (B.of_list [0x03uy; 0x03uy]));
  Seq.lemma_eq_elim (WS.u16 0x0303) (B.of_list [0x03uy; 0x03uy]);
  assert (Seq.equal (WS.u8 0) (B.of_list [0uy]));
  Seq.lemma_eq_elim (WS.u8 0) (B.of_list [0uy]);
  assert (Seq.equal
    (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
    (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]));
  Seq.lemma_eq_elim
    (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
    (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]);
  assert (Seq.equal
    (WS.u16 (B.length extensions))
    (B.of_list [
      client_hello_byte (B.length extensions / 256);
      client_hello_byte (B.length extensions)]));
  Seq.lemma_eq_elim
    (WS.u16 (B.length extensions))
    (B.of_list [
      client_hello_byte (B.length extensions / 256);
      client_hello_byte (B.length extensions)]);
  assert_norm (WS.append6
    (B.of_list [0x03uy; 0x03uy])
    random
    (B.of_list [0uy])
    (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
    (B.of_list [0uy])
    (B.append
      (B.of_list [
        client_hello_byte (B.length extensions / 256);
        client_hello_byte (B.length extensions)])
      extensions) ==
    client_hello_body_bytes_with_extensions random extensions);
  Seq.lemma_eq_elim
    (WS.append6
      (WS.u16 0x0303)
      random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions))
    (WS.append6
      (B.of_list [0x03uy; 0x03uy])
      random
      (B.of_list [0uy])
      (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
      (B.of_list [0uy])
      (B.append
        (B.of_list [
          client_hello_byte (B.length extensions / 256);
          client_hello_byte (B.length extensions)])
        extensions));
  Seq.lemma_eq_refl
    (WS.append6
      (WS.u16 0x0303)
      random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions))
    (client_hello_body_bytes_with_extensions random extensions)
#pop-options

private let lemma_seq_equal_trans (#a:Type) (x y z:Seq.seq a)
  : Lemma
      (requires Seq.equal x y /\ Seq.equal y z)
      (ensures Seq.equal x z)
=
  Seq.lemma_eq_elim x y;
  Seq.lemma_eq_elim y z;
  Seq.lemma_eq_refl x z

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 10"
private let lemma_client_hello_public_body_reveal
  (hello:M.client_hello)
  : Lemma (Seq.equal
      (client_hello_impl_body_bytes hello)
      (client_hello_public_body_bytes hello))
=
  assert_norm (client_hello_impl_body_bytes hello ==
    client_hello_public_body_bytes hello);
  Seq.lemma_eq_refl
    (client_hello_impl_body_bytes hello)
    (client_hello_public_body_bytes hello)
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 50"
private let lemma_supported_groups_extension_bytes ()
  : Lemma (Seq.equal
      (WS.supported_groups_extension ())
      (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]))
= ()

private let lemma_signature_algorithms_extension_bytes ()
  : Lemma (Seq.equal
      (WS.signature_algorithms_extension ())
      (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]))
= ()

private let lemma_key_share_extension_bytes (key_share:B.bytes)
  : Lemma (Seq.equal
      (WS.key_share_extension key_share)
      (B.append
        (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        key_share))
= ()

private let lemma_supported_versions_extension_bytes ()
  : Lemma (Seq.equal
      (WS.supported_versions_extension ())
      (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]))
= ()

private let lemma_server_name_extension_bytes (hostname:B.bytes{B.length hostname <= 255})
  : Lemma (Seq.equal
      (WS.server_name_extension hostname)
      (client_hello_server_name_extension_bytes hostname))
=
  lemma_client_hello_server_name_extension_len hostname

private let lemma_client_hello_extensions_bytes_reveal
  (hello:M.client_hello{B.length hello.M.key_share == 32 /\
                        (match hello.M.server_name with
                         | Some h -> B.length h <= 255
                         | None -> True)})
  : Lemma (Seq.equal
    (WS.client_hello_extensions hello)
    (client_hello_extensions_bytes
      (match hello.M.server_name with
       | Some h -> h
       | None -> B.empty)
      hello.M.key_share))
=
  match hello.M.server_name with
  | Some h ->
    assert (B.length h <= 255);
    lemma_server_name_extension_bytes h;
    lemma_supported_groups_extension_bytes ();
    lemma_signature_algorithms_extension_bytes ();
    lemma_key_share_extension_bytes hello.M.key_share;
    lemma_supported_versions_extension_bytes ();
    lemma_client_hello_extensions_len h hello.M.key_share
  | None ->
    lemma_server_name_extension_bytes B.empty;
    lemma_supported_groups_extension_bytes ();
    lemma_signature_algorithms_extension_bytes ();
    lemma_key_share_extension_bytes hello.M.key_share;
    lemma_supported_versions_extension_bytes ();
    lemma_client_hello_extensions_len B.empty hello.M.key_share

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 20"
private let lemma_serialize_client_hello_ws_body_reveal
  (hello:M.client_hello{B.length hello.M.key_share == 32 /\
                        (match hello.M.server_name with
                         | Some h -> B.length h <= 255
                         | None -> True)})
  : Lemma (Seq.equal
      (WS.serialize_client_hello hello)
      (client_hello_ws_body_bytes hello))
=
  lemma_client_hello_extensions_bytes_reveal hello;
  let extensions = client_hello_expected_extensions hello in
  let ws_extensions = WS.client_hello_extensions hello in
  assert (Seq.equal
    ws_extensions
    extensions);
  Seq.lemma_eq_elim
    ws_extensions
    extensions;
  assert (ws_extensions == extensions);
  assert (B.length ws_extensions == B.length extensions);
  assert (B.append (WS.u16 (B.length ws_extensions)) ws_extensions ==
    B.append (WS.u16 (B.length extensions)) extensions);
  assert_norm (WS.serialize_client_hello hello ==
    WS.append6
      (WS.u16 0x0303)
      hello.M.random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append
        (WS.u16 (B.length (WS.client_hello_extensions hello)))
        (WS.client_hello_extensions hello)));
  assert (WS.serialize_client_hello hello ==
    WS.append6
      (WS.u16 0x0303)
      hello.M.random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions));
  assert_norm (client_hello_ws_body_bytes hello ==
    WS.append6
      (WS.u16 0x0303)
      hello.M.random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions));
  assert (WS.serialize_client_hello hello == client_hello_ws_body_bytes hello);
  Seq.lemma_eq_refl
    (WS.serialize_client_hello hello)
    (client_hello_ws_body_bytes hello)
#pop-options

private let lemma_client_hello_body_bytes_reveal
  (hello:M.client_hello{B.length hello.M.random == 32 /\
                        B.length hello.M.key_share == 32 /\
                        (match hello.M.server_name with
                         | Some h -> B.length h <= 255
                         | None -> True)})
  : Lemma (Seq.equal
    (WS.serialize_client_hello hello)
    (client_hello_body_bytes
      hello.M.random
      (match hello.M.server_name with
       | Some h -> h
       | None -> B.empty)
      hello.M.key_share))
=
  let ws_body = client_hello_ws_body_bytes hello in
  let impl_body = client_hello_impl_body_bytes hello in
  let public_body = client_hello_public_body_bytes hello in
  lemma_serialize_client_hello_ws_body_reveal hello;
  lemma_client_hello_body_bytes_with_extensions_reveal
    hello.M.random
    (client_hello_expected_extensions hello);
  assert (Seq.equal ws_body impl_body);
  lemma_client_hello_public_body_reveal hello;
  assert (Seq.equal impl_body public_body);
  lemma_seq_equal_trans
    (WS.serialize_client_hello hello)
    ws_body
    impl_body;
  lemma_seq_equal_trans
    (WS.serialize_client_hello hello)
    impl_body
    public_body
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 50"
let lemma_client_hello_handshake_bytes_reveal hello =
  lemma_client_hello_common_extensions_len hello.M.key_share;
  (match hello.M.server_name with
   | Some h ->
     assert (B.length h <= 255);
     assert (B.length hello.M.key_share == 32);
     lemma_client_hello_server_name_extension_len h;
     lemma_client_hello_extensions_len h hello.M.key_share
   | None ->
     assert (B.length B.empty <= 255);
     assert (B.length hello.M.key_share == 32);
     lemma_client_hello_server_name_extension_len B.empty;
     lemma_client_hello_extensions_len B.empty hello.M.key_share);
  lemma_client_hello_body_bytes_reveal hello;
  lemma_serialize_client_hello_reveal hello
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 50"
let lemma_client_hello_handshake_bytes_prefix random hostname key_share =
  lemma_client_hello_extensions_len hostname key_share
#pop-options

let lemma_ptm_alert fragment =
  if B.length fragment <> 2
  then ()
  else assert (WS.nat_of_byte (Seq.index fragment 1) == U8.v (Seq.index fragment 1))

let handshake_synth h = WS.synth_handshake_msg_of h

let synth_cipher_suite c = WS.synth_cipher_suite c

let synth_signature_scheme s = WS.synth_signature_scheme s

let lemma_synth_signature_scheme s = ()

let lemma_ptm_handshake_some fragment v m =
  assert (WS.parse_handshake fragment == Some (m, B.length fragment))

let lemma_handshake_synth_finished b = ()

let lemma_handshake_synth_certificate_verify b = ()

let lemma_handshake_synth_key_update b = ()

let lemma_handshake_synth_client_hello b = ()

let reveal_parse_ignored_post_handshake input = WS.parse_ignored_post_handshake input

(* a*65536 + b*256 + c == 1 with 0 <= a,b,c <= 255 forces a=b=0, c=1.
   (multiplication by literal constants is linear, so SMT handles this.) *)
let lemma_u24_one (input:B.bytes{B.length input >= 4})
  : Lemma (WS.read_u24 input 1 == 1 <==>
           (U8.v (Seq.index input 1) == 0 /\
            U8.v (Seq.index input 2) == 0 /\
            U8.v (Seq.index input 3) == 1))
= ()

let lemma_parse_key_update_def input =
  if B.length input = 5 then lemma_u24_one input else ()

let lemma_parse_ignored_post_handshake_def input = ()

let lemma_parse_handshake_none_of_lp_none fragment = ()

let lemma_parse_handshake_none_of_synth_none fragment v consumed = ()

let lemma_ptm_handshake_fallback fragment = ()


let reveal_synth_encrypted_extensions l = WS.synth_encrypted_extensions l

let reveal_alpn_first_name pnl = WS.alpn_first_name pnl

let lemma_handshake_synth_encrypted_extensions b = ()

let lemma_synth_ee_nil () = ()

let lemma_synth_ee_cons_non_alpn e tl = ()

let lemma_synth_ee_cons_alpn pnl tl = ()
let rec lemma_list_drop_index #a l i =
  if i = 0 then ()
  else (match l with | _ :: tl -> lemma_list_drop_index tl (i - 1))

let rec lemma_list_drop_length #a l =
  match l with
  | [] -> ()
  | _ :: tl -> lemma_list_drop_length tl

let lemma_alpn_first_name_index0 pnl = ()

(* --- ServerHello reveal interface --------------------------------------- *)

let reveal_key_exchange_to_key32 ke = WS.key_exchange_to_key32 ke

let lemma_reveal_key_exchange_to_key32 ke = ()

let reveal_sh_key_share l saw key_share = WS.sh_key_share l saw key_share

let lemma_sh_key_share_nil saw key_share = ()

let lemma_sh_key_share_cons e tl saw key_share = ()

let lemma_handshake_synth_server_hello_bad_version b = ()

let lemma_handshake_synth_server_hello_hrr b shb = ()

let lemma_handshake_synth_server_hello_sh b sf = ()

(* --- Certificate reveal interface --------------------------------------- *)

let reveal_synth_cert_chain l = WS.synth_cert_chain l

let reveal_cert_chain_total_bytes chain = WS.cert_chain_total_bytes chain

let lemma_synth_cert_chain_nil () = ()

let lemma_synth_cert_chain_cons e tl = ()

let rec lemma_synth_cert_chain_length l =
  match l with
  | [] -> ()
  | _ :: tl -> lemma_synth_cert_chain_length tl

let lemma_cert_chain_total_bytes_nil () = ()

let rec lemma_cert_chain_total_bytes_snoc chain x =
  match chain with
  | [] -> ()
  | _ :: tl -> lemma_cert_chain_total_bytes_snoc tl x

let rec lemma_cert_chain_total_bytes_prefix_le prefix x rest =
  match prefix with
  | [] -> ()
  | _ :: tl -> lemma_cert_chain_total_bytes_prefix_le tl x rest

let lemma_handshake_synth_certificate b = ()
