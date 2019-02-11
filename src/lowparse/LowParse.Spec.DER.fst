module LowParse.Spec.DER
include LowParse.Spec.Combinators
include LowParse.Spec.SeqBytes

include LowParse.Spec.Int
open FStar.Mul

module U8 = FStar.UInt8
module UInt = FStar.UInt
module Math = LowParse.Math
module E = LowParse.BigEndian
module Seq = FStar.Seq

#reset-options "--z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0"

let der_length_max : nat = normalize_term (pow2 (8 * 126) - 1)

let _ = intro_ambient der_length_max

let _ : unit = _ by (FStar.Tactics.(print (string_of_int der_length_max); exact (`())))

let der_length_t = (x: nat { x <= der_length_max })

inline_for_extraction
let parse_der_length_payload_kind : parser_kind = strong_parser_kind 0 126 None

let rec log256
  (x: nat { x > 0 })
: GTot (y: nat { y > 0 /\ pow2 (8 * (y - 1)) <= x /\ x < pow2 (8 * y)})
= assert_norm (pow2 8 == 256);
  if x < 256
  then 1
  else begin
    let n = log256 (x / 256) in
    Math.pow2_plus (8 * (n - 1)) 8;
    Math.pow2_plus (8 * n) 8;
    n + 1
  end

let log256_unique
  (x: nat)
  (y: nat)
: Lemma
  (requires (
    x > 0 /\
    y > 0 /\
    pow2 (8 * (y - 1)) <= x /\
    x < pow2 (8 * y)
  ))
  (ensures (y == log256 x))
= Math.pow2_lt_recip (8 * (y - 1)) (8 * log256 x);
  Math.pow2_lt_recip (8 * (log256 x - 1)) (8 * y)

let tag_of_der_length
  (x: der_length_t)
: GTot U8.t
= if x < 128
  then U8.uint_to_t x
  else
    let len_len = log256 x in
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126);
    128uy `U8.add` U8.uint_to_t len_len

let synth_be_int
  (len: nat)
  (b: Seq.lseq byte len)
: GTot (x: nat { x < pow2 (8 * len) })
= E.lemma_be_to_n_is_bounded b;
  E.be_to_n b

let synth_be_int_injective
  (len: nat)
: Lemma
  (synth_injective (synth_be_int len))
  [SMTPat (synth_injective (synth_be_int len))]
= 
  synth_injective_intro' (synth_be_int len) (fun (x x' : Seq.lseq byte len) ->
    E.be_to_n_inj x x'
  )

let synth_der_length_129
  (x: U8.t { x == 129uy } )
  (y: U8.t { U8.v y >= 128 } )
: GTot (refine_with_tag tag_of_der_length x)
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  log256_unique (U8.v y) 1;
  U8.v y

let synth_der_length_greater
  (x: U8.t { U8.v x > 129 /\ U8.v x < 255 } )
  (len: nat { len == U8.v x % 128 } )
  (y: (y: nat { y < pow2 (8 * len) } ) { y >= pow2 (8 * (len - 1)) } )
: Tot (refine_with_tag tag_of_der_length x)
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  Math.lemma_mod_lt (U8.v x) (pow2 7);
  Math.lemma_div_mod (U8.v x) (pow2 7);
  Math.division_definition (U8.v x) (pow2 7) 1;
  Math.pow2_le_compat (8 * 126) (8 * len);
  Math.pow2_le_compat (8 * (len - 1)) 7;
  log256_unique y len;
  y

let parse_der_length_payload
  (x: U8.t)
: Tot (parser parse_der_length_payload_kind (refine_with_tag tag_of_der_length x))
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  let (x' : der_length_t) = U8.v x in
  if x' < 128
  then begin
    weaken parse_der_length_payload_kind (parse_ret (x' <: refine_with_tag tag_of_der_length x))
  end else
   if x = 128uy
   then 
    fail_parser parse_der_length_payload_kind (refine_with_tag tag_of_der_length x) // DER representation of 0 is covered by the x<128 case
   else if x = 255uy
   then 
    fail_parser parse_der_length_payload_kind (refine_with_tag tag_of_der_length x) // forbidden in BER already
   else if x = 129uy
   then
    weaken parse_der_length_payload_kind
      ((parse_u8 `parse_filter` (fun y -> U8.v y >= 128))
        `parse_synth` synth_der_length_129 x)
  else begin
    let len : nat = U8.v x % pow2 7 in
    synth_be_int_injective len; // FIXME: WHY WHY WHY does the pattern not trigger, even with higher rlimit?
    weaken parse_der_length_payload_kind
      (((parse_seq_flbytes len `parse_synth` (synth_be_int len))
        `parse_filter` (fun (y: nat { y < pow2 (8 * len) } ) -> y >= pow2 (8 * (len - 1))))
       `parse_synth` synth_der_length_greater x len)
  end        
        
inline_for_extraction
let parse_der_length_kind : parser_kind = and_then_kind parse_u8_kind parse_der_length_payload_kind

let parse_der_length : parser parse_der_length_kind der_length_t
= parse_tagged_union
    parse_u8
    tag_of_der_length
    parse_der_length_payload

let tag_of_der_length_lt_128
  (x: der_length_t)
: Lemma
  (requires (U8.v (tag_of_der_length x) < 128))
  (ensures (x == U8.v (tag_of_der_length x)))
= if x < 128
  then ()
  else
    let len_len = log256 x in
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126)

let tag_of_der_length_invalid
  (x: der_length_t)
: Lemma
  (requires (let y = U8.v (tag_of_der_length x) in y == 128 \/ y == 255))
  (ensures False)
= if x < 128
  then ()
  else
    let len_len = log256 x in
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126)

let tag_of_der_length_eq_129
  (x: der_length_t)
: Lemma
  (requires (U8.v (tag_of_der_length x) == 129))
  (ensures (x >= 128 /\ x < 256))
= if x < 128
  then ()
  else
    let len_len = log256 x in
    assert_norm (der_length_max == pow2 (8 * 126) - 1);
    Math.pow2_lt_recip (8 * (len_len - 1)) (8 * 126)

let synth_der_length_129_recip
  (x: U8.t { x == 129uy })
  (y: refine_with_tag tag_of_der_length x)
: GTot (y: U8.t {U8.v y >= 128})
= tag_of_der_length_eq_129 y;
  U8.uint_to_t y

let synth_be_int_recip
  (len: nat)
  (x: nat { x < pow2 (8 * len) })
: GTot (b: Seq.lseq byte len)
= E.n_to_be'' len x

let synth_be_int_inverse
  (len: nat)
: Lemma
  (synth_inverse (synth_be_int len) (synth_be_int_recip len))
= ()

let synth_der_length_greater_recip
  (x: U8.t { U8.v x > 129 /\ U8.v x < 255 } )
  (len: nat { len == U8.v x % 128 } )
  (y: refine_with_tag tag_of_der_length x)
: Tot (y: (y: nat { y < pow2 (8 * len) } ) { y >= pow2 (8 * (len - 1)) } )
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  Math.pow2_lt_recip (8 * (log256 y - 1)) (8 * 126);
  y

let synth_der_length_greater_inverse
  (x: U8.t { U8.v x > 129 /\ U8.v x < 255 } )
  (len: nat { len == U8.v x % 128 } )
: Lemma
  (synth_inverse (synth_der_length_greater x len) (synth_der_length_greater_recip x len))
= ()

let serialize_der_length_payload
  (x: U8.t)
: Tot (serializer (parse_der_length_payload x))
= assert_norm (der_length_max == pow2 (8 * 126) - 1);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (256 < der_length_max);
  assert (U8.v x <= der_length_max);
  let (x' : der_length_t) = U8.v x in
  if x' < 128
  then begin
    serialize_weaken parse_der_length_payload_kind (serialize_ret (x' <: refine_with_tag tag_of_der_length x) (fun (y: refine_with_tag tag_of_der_length x) -> tag_of_der_length_lt_128 y))
  end else
   if x = 128uy || x = 255uy
   then
     fail_serializer parse_der_length_payload_kind (refine_with_tag tag_of_der_length x) (fun y -> tag_of_der_length_invalid y)
   else if x = 129uy
   then begin
     serialize_weaken
       parse_der_length_payload_kind
       (serialize_synth
          (parse_filter parse_u8 (fun y -> U8.v y >= 128))
          (synth_der_length_129 x)
          (serialize_filter serialize_u8 (fun y -> U8.v y >= 128))
          (synth_der_length_129_recip x)
          (synth_inverse_intro' (synth_der_length_129 x) (synth_der_length_129_recip x) (fun (y: refine_with_tag tag_of_der_length x) -> tag_of_der_length_eq_129 y))
       )
   end else begin
    let len : nat = U8.v x % pow2 7 in
    synth_be_int_injective len; // FIXME: WHY WHY WHY does the pattern not trigger, even with higher rlimit?
    serialize_weaken
      parse_der_length_payload_kind
      (serialize_synth
        _
        (synth_der_length_greater x len)
        (serialize_filter
          (serialize_synth
            _
            (synth_be_int len)
            (serialize_seq_flbytes len)
            (synth_be_int_recip len)
            ()
          )
          (fun (y: nat { y < pow2 (8 * len) } ) -> y >= pow2 (8 * (len - 1)))
        )
        (synth_der_length_greater_recip x len)
        ()
      )
   end
