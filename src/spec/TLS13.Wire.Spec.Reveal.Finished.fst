module TLS13.Wire.Spec.Reveal.Finished

friend TLS13.Wire.Generated.Finished
friend TLS13.Wire.Generated.Handshake_body_finished
friend TLS13.Wire.Generated.HandshakeType
friend TLS13.Wire.Generated.Handshake
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module E = FStar.Endianness
module GHS = TLS13.Wire.Generated.Handshake
module HT = TLS13.Wire.Generated.HandshakeType
module LP = LowParse.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

let byte n = WS.byte n
let u8 n = WS.u8 n
let u24 n = WS.u24 n

let lemma_byte_0 () =
  WS.lemma_byte_v 0;
  assert_norm (U8.v 0uy == 0);
  assert (U8.v (byte 0) == U8.v 0uy);
  U8.v_inj (byte 0) 0uy

let lemma_byte_20 () =
  WS.lemma_byte_v 20;
  assert_norm (U8.v 20uy == 20);
  assert (U8.v (byte 20) == U8.v 20uy);
  U8.v_inj (byte 20) 20uy

let lemma_byte_32 () =
  WS.lemma_byte_v 32;
  assert_norm (U8.v 32uy == 32);
  assert (U8.v (byte 32) == U8.v 32uy);
  U8.v_inj (byte 32) 32uy

let lemma_u8_reveal (n:nat)
  : Lemma (Seq.equal (u8 n) (B.singleton (byte n)))
= ()

let lemma_u24_reveal (n:nat)
  : Lemma (Seq.equal (u24 n) (B.of_list [byte (n / 65536); byte (n / 256); byte n]))
= ()

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

#push-options "--fuel 8 --ifuel 2 --z3rlimit 80"
let lemma_serialize_finished_reveal fin =
  let vd = fin.M.verify_data in
  let tag = u8 20 in
  let lenb = u24 (B.length vd) in
  let lenb32 = u24 32 in
  let lenb32_bytes = B.of_list [byte (32 / 65536); byte (32 / 256); byte 32] in
  WS.lemma_serialize_finished_len fin;
  assert (B.length vd == 32);
  assert_norm (WS.serialize_finished fin == vd);
  assert (WS.serialize_handshake_body (M.Finished fin) == Some (20, vd));
  assert (WS.serialize_handshake (M.Finished fin) == B.append tag (B.append lenb vd));
  assert (lenb == lenb32);
  lemma_u8_reveal 20;
  Seq.lemma_eq_elim tag (B.singleton (byte 20));
  lemma_byte_20 ();
  assert (B.singleton (byte 20) == B.singleton 20uy);
  TLS13.Wire.Spec.Reveal.Util.lemma_singleton_of_list 20uy;
  Seq.lemma_eq_elim tag (B.of_list [20uy]);
  lemma_u24_reveal 32;
  Seq.lemma_eq_elim lenb32 lenb32_bytes;
  assert_norm (32 / 65536 == 0);
  assert_norm (32 / 256 == 0);
  lemma_byte_0 ();
  lemma_byte_32 ();
  assert (lenb32_bytes == B.of_list [0uy; 0uy; 32uy]);
  Seq.lemma_eq_elim lenb (B.of_list [0uy; 0uy; 32uy]);
  lemma_olcons [20uy] [0uy; 0uy; 32uy] vd;
  Seq.lemma_eq_elim
    (WS.serialize_handshake (M.Finished fin))
    (B.append (B.of_list [20uy; 0uy; 0uy; 32uy]) vd)
#pop-options

#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 100"
let lemma_vldata_bytes (vd: GHS.handshake_body_finished)
  : Lemma (LP.serialize GHS.handshake_body_finished_serializer vd ==
           Seq.append (B.of_list [0uy; 0uy; 32uy]) vd)
=
  LP.serialize_bounded_integer_spec 3 (U32.uint_to_t 32);
  E.n_to_be_be_to_n 3 (B.of_list [0uy; 0uy; 32uy]);
  E.reveal_be_to_n (B.of_list [0uy; 0uy; 32uy]);
  E.reveal_be_to_n (Seq.slice (B.of_list [0uy; 0uy; 32uy]) 0 2);
  E.reveal_be_to_n (Seq.slice (B.of_list [0uy; 0uy; 32uy]) 0 1);
  assert_norm (Seq.length (B.of_list [0uy; 0uy; 32uy]) = 3);
  assert_norm (Seq.index (B.of_list [0uy; 0uy; 32uy]) 2 = 32uy);
  assert_norm (Seq.index (B.of_list [0uy; 0uy; 32uy]) 1 = 0uy);
  assert_norm (Seq.index (B.of_list [0uy; 0uy; 32uy]) 0 = 0uy)

let lemma_ghs_serialize_eq_ws (vd: GHS.handshake_body_finished)
  : Lemma (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_finished vd))
    (WS.serialize_handshake (M.Finished ({ M.verify_data = vd }))))
=
  LP.serialize_sum_eq
    GHS.handshake_sum HT.handshakeType_repr_serializer GHS.serialize_handshake_cases
    (GHS.Body_finished vd);
  LP.serialize_enum_key_eq
    HT.handshakeType_repr_serializer HT.handshakeType_enum HT.Finished;
  assert_norm (LP.enum_repr_of_key HT.handshakeType_enum HT.Finished == 20z);
  LP.serialize_u8_spec 20z;
  lemma_vldata_bytes vd;
  lemma_serialize_finished_reveal ({ M.verify_data = vd });
  Seq.lemma_seq_of_list_induction [20uy; 0uy; 0uy; 32uy];
  Seq.append_assoc (Seq.create 1 20uy) (B.of_list [0uy; 0uy; 32uy]) vd
#pop-options

#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 100"
let lemma_parse_finished_handshake fin =
  let vd : GHS.handshake_body_finished = fin.M.verify_data in
  LP.parse_serialize GHS.handshake_serializer (GHS.Body_finished vd);
  lemma_ghs_serialize_eq_ws vd;
  WS.lemma_serialize_finished_len fin
#pop-options
