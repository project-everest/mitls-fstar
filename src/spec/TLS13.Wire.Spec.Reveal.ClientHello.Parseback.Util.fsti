module TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Util

module B = TLS13.Bytes
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module LP = LowParse.Spec

val lemma_u16_parts_fit_raw (x:U16.t)
  : Lemma (U8.fits (U16.v x / 256) /\ U8.fits (U16.v x % 256))

val lemma_u8_uint_to_t_eq_raw (n:nat{U8.fits n}) (b:U8.t)
  : Lemma (requires U8.v b == n)
          (ensures U8.uint_to_t n == b)

val lemma_u16_uint_to_t_eq_raw (n:nat{U16.fits n}) (b:U16.t)
  : Lemma (requires U16.v b == n)
          (ensures U16.uint_to_t n == b)

val lemma_serialize_u16_bytes_raw (x:U16.t)
  : Lemma
      (requires U8.fits (U16.v x / 256) /\ U8.fits (U16.v x % 256))
      (ensures Seq.equal (LP.serialize LP.serialize_u16 x)
                         (B.of_list [U8.uint_to_t (U16.v x / 256);
                                     U8.uint_to_t (U16.v x % 256)]))

val lemma_of_list_append_raw (l1 l2: list U8.t)
  : Lemma (ensures Seq.equal (Seq.append (B.of_list l1) (B.of_list l2))
                             (B.of_list (l1 `FStar.List.Tot.append` l2)))

val lemma_bounded_int_1_raw (n:nat{n < 256 /\ U8.fits n /\ U32.fits n})
  : Lemma (Seq.equal (LP.serialize (LP.serialize_bounded_integer 1) (U32.uint_to_t n))
                     (B.of_list [U8.uint_to_t n]))

val lemma_bounded_int_2_fits_raw (n:nat{n < 65536})
  : Lemma (U32.fits n /\ U8.fits (n / 256) /\ U8.fits (n % 256))

val lemma_bounded_int_2_raw (n:nat{n < 65536}) (hi lo: U8.t)
  : Lemma
      (requires U32.fits n /\ U8.v hi == n / 256 /\ U8.v lo == n % 256)
      (ensures Seq.equal (LP.serialize (LP.serialize_bounded_integer 2) (U32.uint_to_t n))
                         (B.of_list [hi; lo]))

val lemma_vldata_strong_unfold_raw
  (min: nat) (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: LP.parser_kind) (#t: Type) (#p: LP.parser k t)
  (s: LP.serializer p)
  (x: LP.parse_bounded_vldata_strong_t min max s)
  : Lemma (LP.serialize (LP.serialize_bounded_vldata_strong min max s) x ==
           Seq.append
             (LP.serialize (LP.serialize_bounded_integer (LP.log256' max)) (U32.uint_to_t (Seq.length (LP.serialize s x))))
             (LP.serialize s x))

val lemma_vlarray_unfold_raw
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

val lemma_vldata_unfold_raw
  (min: nat) (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (#k: LP.parser_kind) (#t: Type) (#p: LP.parser k t)
  (s: LP.serializer p { LP.serialize_bounded_vldata_precond min max k })
  (x: t)
  : Lemma (LP.serialize (LP.serialize_bounded_vldata min max s) x ==
           Seq.append
             (LP.serialize (LP.serialize_bounded_integer (LP.log256' max)) (U32.uint_to_t (Seq.length (LP.serialize s x))))
             (LP.serialize s x))

val lemma_olcons_raw (a b: list U8.t) (s: Seq.seq U8.t)
  : Lemma (Seq.equal (Seq.append (B.of_list a) (Seq.append (B.of_list b) s))
                     (Seq.append (B.of_list (FStar.List.Tot.append a b)) s))
