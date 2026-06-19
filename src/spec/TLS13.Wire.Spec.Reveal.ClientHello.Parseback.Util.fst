module TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Util

module B = TLS13.Bytes
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.Spec
module E = FStar.Endianness

/// be_to_n / n_to_be helpers

private let lemma_n_to_be_2_raw (n:nat{n < 65536}) (hi lo:U8.t)
  : Lemma (requires U8.v hi == n / 256 /\ U8.v lo == n % 256)
          (ensures E.n_to_be 2 n == B.of_list [hi; lo])
=
  let cand : Seq.seq U8.t = B.of_list [hi; lo] in
  Seq.lemma_seq_of_list_induction [hi; lo];
  SeqP.lemma_seq_of_list_index [hi; lo] 0;
  SeqP.lemma_seq_of_list_index [hi; lo] 1;
  assert_norm (FStar.List.Tot.index [hi; lo] 0 == hi);
  assert_norm (FStar.List.Tot.index [hi; lo] 1 == lo);
  assert (Seq.length (B.of_list [hi; lo]) == 2);
  assert (Seq.index (B.of_list [hi; lo]) 0 == hi);
  assert (Seq.index (B.of_list [hi; lo]) 1 == lo);
  Seq.lemma_len_slice cand 0 0;
  Seq.lemma_eq_intro (Seq.slice cand 0 0) B.empty;
  Seq.lemma_eq_elim (Seq.slice cand 0 0) B.empty;
  Seq.lemma_len_slice cand 0 1;
  Seq.lemma_seq_of_list_induction [hi];
  SeqP.lemma_seq_of_list_index [hi] 0;
  assert_norm (FStar.List.Tot.index [hi] 0 == hi);
  assert (Seq.length (Seq.slice cand 0 1) == 1);
  assert (Seq.index (Seq.slice cand 0 1) 0 == hi);
  assert (Seq.index (B.of_list [hi]) 0 == hi);
  assert (Seq.last (B.of_list [hi]) == hi);
  assert (Seq.last cand == lo);
  Seq.lemma_eq_intro (Seq.slice cand 0 1) (B.of_list [hi]);
  Seq.lemma_eq_elim (Seq.slice cand 0 1) (B.of_list [hi]);
  E.reveal_be_to_n cand;
  E.reveal_be_to_n (Seq.slice cand 0 1);
  E.reveal_be_to_n (B.of_list [hi]);
  E.reveal_be_to_n (Seq.slice cand 0 0);
  assert_norm (pow2 8 == 256);
  assert (E.be_to_n (Seq.slice cand 0 0) == 0);
  assert (Seq.length (B.of_list [hi]) == 1);
  Seq.lemma_len_slice (B.of_list [hi]) 0 0;
  Seq.lemma_eq_intro (Seq.slice (B.of_list [hi]) 0 0) B.empty;
  Seq.lemma_eq_elim (Seq.slice (B.of_list [hi]) 0 0) B.empty;
  assert (Seq.last (B.of_list [hi]) == hi);
  assert (E.be_to_n (B.of_list [hi]) == U8.v hi);
  assert (E.be_to_n (Seq.slice cand 0 1) == E.be_to_n (B.of_list [hi]));
  assert (E.be_to_n (Seq.slice cand 0 1) == U8.v hi);
  assert (Seq.length cand == 2);
  assert (Seq.length cand - 1 == 1);
  assert (Seq.slice cand 0 (Seq.length cand - 1) == Seq.slice cand 0 1);
  assert (E.be_to_n cand == U8.v (Seq.last cand) + 256 * E.be_to_n (Seq.slice cand 0 1));
  assert (E.be_to_n cand == U8.v lo + 256 * U8.v hi);
  FStar.Math.Lemmas.lemma_div_mod n 256;
  FStar.Math.Lemmas.swap_mul 256 (n / 256);
  assert (n == 256 * (n / 256) + n % 256);
  assert (E.be_to_n cand == n);
  E.n_to_be_be_to_n 2 cand

let lemma_u16_parts_fit_raw (x:U16.t)
  : Lemma (U8.fits (U16.v x / 256) /\ U8.fits (U16.v x % 256))
 =
  FStar.Math.Lemmas.lemma_div_lt (U16.v x) 16 8;
  assert_norm (pow2 8 == 256);
  assert (U16.v x / 256 < 256);
  FStar.Math.Lemmas.lemma_mod_lt (U16.v x <: int) 256;
  assert ((U16.v x <: int) % 256 < 256);
  assert (U16.v x % 256 == (U16.v x <: int) % 256);
  assert ((U16.v x % 256 <: int) < 256);
  assert (U8.fits (U16.v x / 256));
  assert (U8.fits (U16.v x % 256))

let lemma_u8_uint_to_t_eq_raw (n:nat{U8.fits n}) (b:U8.t)
  : Lemma (requires U8.v b == n)
          (ensures U8.uint_to_t n == b)
=
  U8.uv_inv b

let lemma_u16_uint_to_t_eq_raw (n:nat{U16.fits n}) (b:U16.t)
  : Lemma (requires U16.v b == n)
          (ensures U16.uint_to_t n == b)
=
  U16.uv_inv b

let lemma_serialize_u16_bytes_raw (x:U16.t)
  : Lemma
      (requires U8.fits (U16.v x / 256) /\ U8.fits (U16.v x % 256))
      (ensures Seq.equal (LP.serialize LP.serialize_u16 x)
                         (B.of_list [U8.uint_to_t (U16.v x / 256);
                                     U8.uint_to_t (U16.v x % 256)]))
=
  LP.serialize_u16_spec_be x;
  FStar.Math.Lemmas.lemma_div_lt (U16.v x) 16 8;
  assert_norm (pow2 8 == 256);
  assert (U16.v x / 256 < 256);
  FStar.Math.Lemmas.small_mod (U16.v x / 256) 256;
  let hi = U8.uint_to_t (U16.v x / 256) in
  let lo = U8.uint_to_t (U16.v x % 256) in
  lemma_n_to_be_2_raw (U16.v x) hi lo

let rec lemma_of_list_append_raw (l1 l2: list U8.t)
  : Lemma (ensures Seq.equal (Seq.append (B.of_list l1) (B.of_list l2))
                             (B.of_list (l1 `FStar.List.Tot.append` l2)))
          (decreases l1)
=
  match l1 with
  | [] ->
    Seq.lemma_seq_of_list_induction ([] <: list U8.t);
    Seq.append_empty_l (B.of_list l2)
  | hd :: tl ->
    lemma_of_list_append_raw tl l2;
    Seq.lemma_seq_of_list_induction (hd :: (tl `FStar.List.Tot.append` l2));
    Seq.lemma_seq_of_list_induction (hd :: tl);
    Seq.append_assoc (Seq.create 1 hd) (B.of_list tl) (B.of_list l2)

private let lemma_n_to_be_1_raw (n:nat{n < 256}) (b:U8.t)
  : Lemma (requires U8.v b == n)
          (ensures E.n_to_be 1 n == B.of_list [b])
=
  let cand : Seq.seq U8.t = B.of_list [b] in
  assert_norm (FStar.List.Tot.index [b] 0 == b);
  assert_norm (Seq.length (B.of_list [b]) == 1);
  assert_norm (Seq.index (B.of_list [b]) 0 == b);
  Seq.lemma_len_slice cand 0 0;
  Seq.lemma_eq_intro (Seq.slice cand 0 0) B.empty;
  Seq.lemma_eq_elim (Seq.slice cand 0 0) B.empty;
  assert (Seq.last cand == b);
  E.reveal_be_to_n cand;
  E.reveal_be_to_n (Seq.slice cand 0 0);
  assert_norm (pow2 8 == 256);
  assert (E.be_to_n (Seq.slice cand 0 0) == 0);
  assert (Seq.length cand - 1 == 0);
  assert (Seq.slice cand 0 (Seq.length cand - 1) == Seq.slice cand 0 0);
  assert (E.be_to_n cand == U8.v (Seq.last cand) + 256 * E.be_to_n (Seq.slice cand 0 0));
  assert (E.be_to_n cand == U8.v b);
  assert (E.be_to_n cand == n);
  E.n_to_be_be_to_n 1 cand

let lemma_bounded_int_1_raw (n:nat{n < 256 /\ U8.fits n /\ U32.fits n})
  : Lemma (Seq.equal (LP.serialize (LP.serialize_bounded_integer 1) (U32.uint_to_t n))
                     (B.of_list [U8.uint_to_t n]))
=
  LP.serialize_bounded_integer_spec 1 (U32.uint_to_t n);
  lemma_n_to_be_1_raw n (U8.uint_to_t n)

let lemma_bounded_int_2_fits_raw (n:nat{n < 65536})
  : Lemma (U32.fits n /\ U8.fits (n / 256) /\ U8.fits (n % 256))
=
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  assert_norm (pow2 32 == 4294967296);
  assert (n < pow2 16);
  FStar.Math.Lemmas.lemma_div_lt n 16 8;
  assert (n / 256 < 256);
  FStar.Math.Lemmas.lemma_mod_lt (n <: int) 256;
  assert ((n <: int) % 256 < 256);
  assert (n % 256 == (n <: int) % 256);
  assert ((n % 256 <: int) < 256);
  assert (n < 4294967296);
  assert (U32.fits n);
  assert (U8.fits (n / 256));
  assert (U8.fits (n % 256))

let lemma_bounded_int_2_raw (n:nat{n < 65536}) (hi lo: U8.t)
  : Lemma
      (requires U32.fits n /\ U8.v hi == n / 256 /\ U8.v lo == n % 256)
      (ensures Seq.equal (LP.serialize (LP.serialize_bounded_integer 2) (U32.uint_to_t n))
                         (B.of_list [hi; lo]))
=
  LP.serialize_bounded_integer_spec 2 (U32.uint_to_t n);
  FStar.Math.Lemmas.lemma_div_lt n 16 8;
  lemma_n_to_be_2_raw n hi lo

/// vldata / vlarray unfold helpers

#push-options "--fuel 4 --ifuel 4 --z3rlimit 100"
let lemma_vldata_strong_unfold_raw
  (min: nat) (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: LP.parser_kind) (#t: Type) (#p: LP.parser k t)
  (s: LP.serializer p)
  (x: LP.parse_bounded_vldata_strong_t min max s)
  : Lemma (LP.serialize (LP.serialize_bounded_vldata_strong min max s) x ==
           Seq.append
             (LP.serialize (LP.serialize_bounded_integer (LP.log256' max)) (U32.uint_to_t (Seq.length (LP.serialize s x))))
             (LP.serialize s x))
= ()

let lemma_vlarray_unfold_raw
  (amin: nat) (amax: nat)
  (#k: LP.parser_kind) (#t: Type) (#p: LP.parser k t)
  (s: LP.serializer p)
  (emin: nat) (emax: nat)
  (u: unit { LP.vldata_vlarray_precond amin amax p emin emax == true })
  (x: LP.vlarray t emin emax)
  : Lemma
      (let vd = LP.vlarray_to_vldata amin amax s emin emax u x in
       LP.serialize (LP.serialize_vlarray amin amax s emin emax u) x ==
       Seq.append
         (LP.serialize (LP.serialize_bounded_integer (LP.log256' amax))
                       (U32.uint_to_t (Seq.length (LP.serialize (LP.serialize_list _ s) vd))))
         (LP.serialize (LP.serialize_list _ s) vd))
=
  LP.vldata_to_vlarray_inj amin amax s emin emax u;
  LP.vlarray_to_vldata_to_vlarray amin amax s emin emax u;
  LP.serialize_synth_eq _
    (LP.vldata_to_vlarray amin amax s emin emax u)
    (LP.serialize_bounded_vldata_strong amin amax (LP.serialize_list _ s))
    (LP.vlarray_to_vldata amin amax s emin emax u)
    () x;
  let vd = LP.vlarray_to_vldata amin amax s emin emax u x in
  lemma_vldata_strong_unfold_raw amin amax (LP.serialize_list _ s) vd

let lemma_vldata_unfold_raw
  (min: nat) (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: LP.parser_kind) (#t: Type) (#p: LP.parser k t)
  (s: LP.serializer p { LP.serialize_bounded_vldata_precond min max k })
  (x: t)
  : Lemma (LP.serialize (LP.serialize_bounded_vldata min max s) x ==
           Seq.append
             (LP.serialize (LP.serialize_bounded_integer (LP.log256' max)) (U32.uint_to_t (Seq.length (LP.serialize s x))))
             (LP.serialize s x))
= ()
#pop-options

#restart-solver

/// fold: of_list a ++ (of_list b ++ s) == of_list (a@b) ++ s
let lemma_olcons_raw (a b: list U8.t) (s: Seq.seq U8.t)
  : Lemma (Seq.equal (Seq.append (B.of_list a) (Seq.append (B.of_list b) s))
                     (Seq.append (B.of_list (FStar.List.Tot.append a b)) s))
=
  lemma_of_list_append_raw a b;
  Seq.append_assoc (B.of_list a) (B.of_list b) s
