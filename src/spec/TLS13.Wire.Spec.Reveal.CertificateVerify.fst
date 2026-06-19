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

#push-options "--initial_fuel 50 --max_fuel 50"
let certificate_verify_context_with_zero : (b:B.bytes{B.length b == 34}) =
  assert_norm (FStar.List.Tot.length cv_context_list == 34);
  B.of_list cv_context_list
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 20"
let lemma_certificate_verify_context_with_zero_literal () = ()
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50"
let certificate_verify_context_byte (i:nat{i < 34}) =
  FStar.List.Tot.index cv_context_list i
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 100"
let lemma_certificate_verify_context_byte (i:nat{i < 34}) =
  assert (FStar.List.Tot.length cv_context_list == 34);
  FStar.Seq.Properties.lemma_seq_of_list_index cv_context_list i
#pop-options

#push-options "--initial_fuel 100 --max_fuel 100 --z3rlimit 20"
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

#push-options "--initial_fuel 50 --max_fuel 50 --split_queries always --z3rlimit 100"
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
      assert_norm (FStar.List.Tot.length cv_server_list == 33);
      assert (FStar.List.Tot.length cv_context_list == 34);
      match i with
      | 0  -> assert_norm (FStar.List.Tot.index cv_context_list 0 == FStar.List.Tot.index cv_server_list 0)
      | 1  -> assert_norm (FStar.List.Tot.index cv_context_list 1 == FStar.List.Tot.index cv_server_list 1)
      | 2  -> assert_norm (FStar.List.Tot.index cv_context_list 2 == FStar.List.Tot.index cv_server_list 2)
      | 3  -> assert_norm (FStar.List.Tot.index cv_context_list 3 == FStar.List.Tot.index cv_server_list 3)
      | 4  -> assert_norm (FStar.List.Tot.index cv_context_list 4 == FStar.List.Tot.index cv_server_list 4)
      | 5  -> assert_norm (FStar.List.Tot.index cv_context_list 5 == FStar.List.Tot.index cv_server_list 5)
      | 6  -> assert_norm (FStar.List.Tot.index cv_context_list 6 == FStar.List.Tot.index cv_server_list 6)
      | 7  -> assert_norm (FStar.List.Tot.index cv_context_list 7 == FStar.List.Tot.index cv_server_list 7)
      | 8  -> assert_norm (FStar.List.Tot.index cv_context_list 8 == FStar.List.Tot.index cv_server_list 8)
      | 9  -> assert_norm (FStar.List.Tot.index cv_context_list 9 == FStar.List.Tot.index cv_server_list 9)
      | 10 -> assert_norm (FStar.List.Tot.index cv_context_list 10 == FStar.List.Tot.index cv_server_list 10)
      | 11 -> assert_norm (FStar.List.Tot.index cv_context_list 11 == FStar.List.Tot.index cv_server_list 11)
      | 12 -> assert_norm (FStar.List.Tot.index cv_context_list 12 == FStar.List.Tot.index cv_server_list 12)
      | 13 -> assert_norm (FStar.List.Tot.index cv_context_list 13 == FStar.List.Tot.index cv_server_list 13)
      | 14 -> assert_norm (FStar.List.Tot.index cv_context_list 14 == FStar.List.Tot.index cv_server_list 14)
      | 15 -> assert_norm (FStar.List.Tot.index cv_context_list 15 == FStar.List.Tot.index cv_server_list 15)
      | 16 -> assert_norm (FStar.List.Tot.index cv_context_list 16 == FStar.List.Tot.index cv_server_list 16)
      | 17 -> assert_norm (FStar.List.Tot.index cv_context_list 17 == FStar.List.Tot.index cv_server_list 17)
      | 18 -> assert_norm (FStar.List.Tot.index cv_context_list 18 == FStar.List.Tot.index cv_server_list 18)
      | 19 -> assert_norm (FStar.List.Tot.index cv_context_list 19 == FStar.List.Tot.index cv_server_list 19)
      | 20 -> assert_norm (FStar.List.Tot.index cv_context_list 20 == FStar.List.Tot.index cv_server_list 20)
      | 21 -> assert_norm (FStar.List.Tot.index cv_context_list 21 == FStar.List.Tot.index cv_server_list 21)
      | 22 -> assert_norm (FStar.List.Tot.index cv_context_list 22 == FStar.List.Tot.index cv_server_list 22)
      | 23 -> assert_norm (FStar.List.Tot.index cv_context_list 23 == FStar.List.Tot.index cv_server_list 23)
      | 24 -> assert_norm (FStar.List.Tot.index cv_context_list 24 == FStar.List.Tot.index cv_server_list 24)
      | 25 -> assert_norm (FStar.List.Tot.index cv_context_list 25 == FStar.List.Tot.index cv_server_list 25)
      | 26 -> assert_norm (FStar.List.Tot.index cv_context_list 26 == FStar.List.Tot.index cv_server_list 26)
      | 27 -> assert_norm (FStar.List.Tot.index cv_context_list 27 == FStar.List.Tot.index cv_server_list 27)
      | 28 -> assert_norm (FStar.List.Tot.index cv_context_list 28 == FStar.List.Tot.index cv_server_list 28)
      | 29 -> assert_norm (FStar.List.Tot.index cv_context_list 29 == FStar.List.Tot.index cv_server_list 29)
      | 30 -> assert_norm (FStar.List.Tot.index cv_context_list 30 == FStar.List.Tot.index cv_server_list 30)
      | 31 -> assert_norm (FStar.List.Tot.index cv_context_list 31 == FStar.List.Tot.index cv_server_list 31)
      | _  -> assert_norm (FStar.List.Tot.index cv_context_list 32 == FStar.List.Tot.index cv_server_list 32);
      FStar.Seq.Properties.lemma_seq_of_list_index cv_server_list i;
      assert_norm (B.length h_cv == 33);
      assert (i < B.length h_cv);
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
