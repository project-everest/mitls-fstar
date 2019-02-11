module LowParse.Spec.DER
include LowParse.Spec.Combinators
include LowParse.Spec.Bytes

include LowParse.Spec.Int
open FStar.Mul

module B32 = FStar.Bytes
module U8 = FStar.UInt8
module UInt = FStar.UInt
module Math = LowParse.Math
module E = LowParse.BigEndian

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
  (b: B32.lbytes len)
: GTot (x: nat { x < pow2 (8 * len) })
= E.lemma_be_to_n_is_bounded (B32.reveal b);
  E.be_to_n (B32.reveal b)

let synth_be_int_injective
  (len: nat)
: Lemma
  (synth_injective (synth_be_int len))
  [SMTPat (synth_injective (synth_be_int len))]
= 
  synth_injective_intro' (synth_be_int len) (fun (x x' : B32.lbytes len) ->
    E.be_to_n_inj (B32.reveal x) (B32.reveal x')
  )

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
        `parse_synth` (fun (y: U8.t { U8.v y >= 128 } ) -> (
          log256_unique (U8.v y) 1;
          U8.v y <: refine_with_tag tag_of_der_length x
      )))
  else begin
    let len = U8.v x % pow2 7 in
    Math.lemma_mod_lt (U8.v x) (pow2 7);
    Math.lemma_div_mod (U8.v x) (pow2 7);
    Math.division_definition (U8.v x) (pow2 7) 1;
    Math.pow2_le_compat (8 * 126) (8 * len);
    Math.pow2_le_compat (8 * (len - 1)) 7;
    synth_be_int_injective len;
    weaken parse_der_length_payload_kind
      (((parse_flbytes len `parse_synth` (synth_be_int len))
        `parse_filter` (fun (y: nat { y < pow2 (8 * len) } ) -> y >= pow2 (8 * (len - 1))))
       `parse_synth` (fun (y: (y: nat { y < pow2 (8 * len) } ) { y >= pow2 (8 * (len - 1)) } ) ->
         log256_unique y len;
         y <: refine_with_tag tag_of_der_length x
      ))
  end        
        
inline_for_extraction
let parse_der_length_kind : parser_kind = and_then_kind parse_u8_kind parse_der_length_payload_kind

let parse_der_length : parser parse_der_length_kind der_length_t
= parse_tagged_union
    parse_u8
    tag_of_der_length
    parse_der_length_payload
