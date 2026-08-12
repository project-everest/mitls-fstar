module TLS13.Wire.Spec.Reveal.CertificateVerify

friend TLS13.Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module Seq = FStar.Seq
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

let lemma_serialize_server_certificate_verify_input_reveal transcript_hash = ()

let cv_server_list : list U8.t = [
  0x54uy; 0x4cuy; 0x53uy; 0x20uy; 0x31uy; 0x2euy; 0x33uy; 0x2cuy;
  0x20uy; 0x73uy; 0x65uy; 0x72uy; 0x76uy; 0x65uy; 0x72uy; 0x20uy;
  0x43uy; 0x65uy; 0x72uy; 0x74uy; 0x69uy; 0x66uy; 0x69uy; 0x63uy;
  0x61uy; 0x74uy; 0x65uy; 0x56uy; 0x65uy; 0x72uy; 0x69uy; 0x66uy;
  0x79uy]

let cv_context_list : list U8.t = [
  0x54uy; 0x4cuy; 0x53uy; 0x20uy; 0x31uy; 0x2euy; 0x33uy; 0x2cuy;
  0x20uy; 0x73uy; 0x65uy; 0x72uy; 0x76uy; 0x65uy; 0x72uy; 0x20uy;
  0x43uy; 0x65uy; 0x72uy; 0x74uy; 0x69uy; 0x66uy; 0x69uy; 0x63uy;
  0x61uy; 0x74uy; 0x65uy; 0x56uy; 0x65uy; 0x72uy; 0x69uy; 0x66uy;
  0x79uy; 0uy]

#push-options "--fuel 2 --ifuel 1"
let certificate_verify_context_with_zero : (b:B.bytes{B.length b == 34}) =
  assert_norm (FStar.List.Tot.length cv_context_list == 34);
  B.of_list cv_context_list
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let lemma_certificate_verify_context_with_zero_literal () = ()
#pop-options

#push-options "--fuel 2 --ifuel 1"
let certificate_verify_context_byte (i:nat{i < 34}) =
  assert_norm (FStar.List.Tot.length cv_context_list == 34);
  FStar.List.Tot.index cv_context_list i
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let lemma_certificate_verify_context_byte (i:nat{i < 34}) =
  assert_norm (FStar.List.Tot.length cv_context_list == 34);
  FStar.Seq.Properties.lemma_seq_of_list_index cv_context_list i
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let lemma_certificate_verify_context_index_0 () = lemma_certificate_verify_context_byte 0; assert_norm (FStar.List.Tot.index cv_context_list 0 == 0x54uy)
let lemma_certificate_verify_context_index_1 () = lemma_certificate_verify_context_byte 1; assert_norm (FStar.List.Tot.index cv_context_list 1 == 0x4cuy)
let lemma_certificate_verify_context_index_2 () = lemma_certificate_verify_context_byte 2; assert_norm (FStar.List.Tot.index cv_context_list 2 == 0x53uy)
let lemma_certificate_verify_context_index_3 () = lemma_certificate_verify_context_byte 3; assert_norm (FStar.List.Tot.index cv_context_list 3 == 0x20uy)
let lemma_certificate_verify_context_index_4 () = lemma_certificate_verify_context_byte 4; assert_norm (FStar.List.Tot.index cv_context_list 4 == 0x31uy)
let lemma_certificate_verify_context_index_5 () = lemma_certificate_verify_context_byte 5; assert_norm (FStar.List.Tot.index cv_context_list 5 == 0x2euy)
let lemma_certificate_verify_context_index_6 () = lemma_certificate_verify_context_byte 6; assert_norm (FStar.List.Tot.index cv_context_list 6 == 0x33uy)
let lemma_certificate_verify_context_index_7 () = lemma_certificate_verify_context_byte 7; assert_norm (FStar.List.Tot.index cv_context_list 7 == 0x2cuy)
let lemma_certificate_verify_context_index_8 () = lemma_certificate_verify_context_byte 8; assert_norm (FStar.List.Tot.index cv_context_list 8 == 0x20uy)
let lemma_certificate_verify_context_index_9 () = lemma_certificate_verify_context_byte 9; assert_norm (FStar.List.Tot.index cv_context_list 9 == 0x73uy)
let lemma_certificate_verify_context_index_10 () = lemma_certificate_verify_context_byte 10; assert_norm (FStar.List.Tot.index cv_context_list 10 == 0x65uy)
let lemma_certificate_verify_context_index_11 () = lemma_certificate_verify_context_byte 11; assert_norm (FStar.List.Tot.index cv_context_list 11 == 0x72uy)
let lemma_certificate_verify_context_index_12 () = lemma_certificate_verify_context_byte 12; assert_norm (FStar.List.Tot.index cv_context_list 12 == 0x76uy)
let lemma_certificate_verify_context_index_13 () = lemma_certificate_verify_context_byte 13; assert_norm (FStar.List.Tot.index cv_context_list 13 == 0x65uy)
let lemma_certificate_verify_context_index_14 () = lemma_certificate_verify_context_byte 14; assert_norm (FStar.List.Tot.index cv_context_list 14 == 0x72uy)
let lemma_certificate_verify_context_index_15 () = lemma_certificate_verify_context_byte 15; assert_norm (FStar.List.Tot.index cv_context_list 15 == 0x20uy)
let lemma_certificate_verify_context_index_16 () = lemma_certificate_verify_context_byte 16; assert_norm (FStar.List.Tot.index cv_context_list 16 == 0x43uy)
let lemma_certificate_verify_context_index_17 () = lemma_certificate_verify_context_byte 17; assert_norm (FStar.List.Tot.index cv_context_list 17 == 0x65uy)
let lemma_certificate_verify_context_index_18 () = lemma_certificate_verify_context_byte 18; assert_norm (FStar.List.Tot.index cv_context_list 18 == 0x72uy)
let lemma_certificate_verify_context_index_19 () = lemma_certificate_verify_context_byte 19; assert_norm (FStar.List.Tot.index cv_context_list 19 == 0x74uy)
let lemma_certificate_verify_context_index_20 () = lemma_certificate_verify_context_byte 20; assert_norm (FStar.List.Tot.index cv_context_list 20 == 0x69uy)
let lemma_certificate_verify_context_index_21 () = lemma_certificate_verify_context_byte 21; assert_norm (FStar.List.Tot.index cv_context_list 21 == 0x66uy)
let lemma_certificate_verify_context_index_22 () = lemma_certificate_verify_context_byte 22; assert_norm (FStar.List.Tot.index cv_context_list 22 == 0x69uy)
let lemma_certificate_verify_context_index_23 () = lemma_certificate_verify_context_byte 23; assert_norm (FStar.List.Tot.index cv_context_list 23 == 0x63uy)
let lemma_certificate_verify_context_index_24 () = lemma_certificate_verify_context_byte 24; assert_norm (FStar.List.Tot.index cv_context_list 24 == 0x61uy)
let lemma_certificate_verify_context_index_25 () = lemma_certificate_verify_context_byte 25; assert_norm (FStar.List.Tot.index cv_context_list 25 == 0x74uy)
let lemma_certificate_verify_context_index_26 () = lemma_certificate_verify_context_byte 26; assert_norm (FStar.List.Tot.index cv_context_list 26 == 0x65uy)
let lemma_certificate_verify_context_index_27 () = lemma_certificate_verify_context_byte 27; assert_norm (FStar.List.Tot.index cv_context_list 27 == 0x56uy)
let lemma_certificate_verify_context_index_28 () = lemma_certificate_verify_context_byte 28; assert_norm (FStar.List.Tot.index cv_context_list 28 == 0x65uy)
let lemma_certificate_verify_context_index_29 () = lemma_certificate_verify_context_byte 29; assert_norm (FStar.List.Tot.index cv_context_list 29 == 0x72uy)
let lemma_certificate_verify_context_index_30 () = lemma_certificate_verify_context_byte 30; assert_norm (FStar.List.Tot.index cv_context_list 30 == 0x69uy)
let lemma_certificate_verify_context_index_31 () = lemma_certificate_verify_context_byte 31; assert_norm (FStar.List.Tot.index cv_context_list 31 == 0x66uy)
let lemma_certificate_verify_context_index_32 () = lemma_certificate_verify_context_byte 32; assert_norm (FStar.List.Tot.index cv_context_list 32 == 0x79uy)
let lemma_certificate_verify_context_index_33 () = lemma_certificate_verify_context_byte 33; assert_norm (FStar.List.Tot.index cv_context_list 33 == 0uy)
#pop-options

#push-options "--fuel 1 --ifuel 1"
(* seq_of_list distributes over list append.  One induction at fuel 1 replaces
   the 34-case assert_norm enumeration this file used to carry at fuel 50. *)
let rec lemma_seq_of_list_append (#a:Type) (l1 l2: list a)
  : Lemma (ensures Seq.equal (Seq.seq_of_list (FStar.List.Tot.append l1 l2))
                             (Seq.append (Seq.seq_of_list l1) (Seq.seq_of_list l2)))
          (decreases l1)
  = match l1 with
    | [] -> Seq.append_empty_l (Seq.seq_of_list l2)
    | _ :: t -> lemma_seq_of_list_append t l2

let lemma_singleton_eq_of_list (#a:Type) (x:a)
  : Lemma (Seq.equal (Seq.create 1 x) (Seq.seq_of_list [x]))
  = Seq.lemma_seq_of_list_index [x] 0
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let lemma_cv_eq_append ()
  : Lemma (Seq.equal certificate_verify_context_with_zero
    (B.append H.certificate_verify_server_context (B.singleton 0uy))) =
  assert_norm (H.certificate_verify_server_context == B.of_list cv_server_list);
  assert_norm (cv_context_list == FStar.List.Tot.append cv_server_list [0uy]);
  lemma_seq_of_list_append cv_server_list [0uy];
  lemma_singleton_eq_of_list 0uy
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
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
