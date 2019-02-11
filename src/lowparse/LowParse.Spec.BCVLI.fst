module LowParse.Spec.BCVLI
include LowParse.Spec.Int
include LowParse.Spec.VLData // for bounded_integer

module E = FStar.Kremlin.Endianness

module U32 = FStar.UInt32
module Seq = FStar.Seq

let bounded_integer_of_le
  (i: integer_size)
  (b: bytes { Seq.length b == i } )
: GTot (bounded_integer i)
= E.lemma_le_to_n_is_bounded b;
  U32.uint_to_t (E.le_to_n b)

#set-options "--z3rlimit 16"
let bounded_integer_of_le_injective'
  (i: integer_size)
  (b1: bytes { Seq.length b1 == i } )
  (b2: bytes { Seq.length b2 == i } )
: Lemma
  (bounded_integer_of_le i b1 == bounded_integer_of_le i b2 ==> Seq.equal b1 b2)
= if bounded_integer_of_le i b1 = bounded_integer_of_le i b2
  then begin
    E.lemma_le_to_n_is_bounded b1;
    E.lemma_le_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.le_to_n b1)) == E.le_to_n b1);
    assert (U32.v (U32.uint_to_t (E.le_to_n b2)) == E.le_to_n b2);
    assert (E.le_to_n b1 == E.le_to_n b2);
    E.le_to_n_inj b1 b2
  end else ()
#reset-options

let bounded_integer_of_le_injective
  (i: integer_size)
: Lemma
  (make_total_constant_size_parser_precond i (bounded_integer i) (bounded_integer_of_le i))
= Classical.forall_intro_2 (bounded_integer_of_le_injective' i)

let parse_bounded_integer_le
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))
= bounded_integer_of_le_injective i;
  make_total_constant_size_parser i (bounded_integer i) (bounded_integer_of_le i)

module U16 = FStar.UInt16
module Cast = FStar.Int.Cast

inline_for_extraction
let synth_u16_le
  (x: bounded_integer 2)
: Tot U16.t
= Cast.uint32_to_uint16 x

let synth_u16_le_injective : squash (synth_injective synth_u16_le) = ()

let parse_u16_le : parser parse_u16_kind U16.t = parse_bounded_integer_le 2 `parse_synth` synth_u16_le

inline_for_extraction
let synth_u32_le
  (x: bounded_integer 4)
: Tot U32.t
= x

let parse_u32_le : parser parse_u32_kind U32.t = parse_bounded_integer_le 4 `parse_synth` synth_u32_le

inline_for_extraction
let parse_bcvli_payload_kind = {
  parser_kind_low = 0;
  parser_kind_high = Some 4;
  parser_kind_subkind = Some ParserStrong;
  parser_kind_metadata = None;
}

let parse_bcvli_payload (x: bounded_integer 1) : Tot (parser parse_bcvli_payload_kind U32.t) =
  if U32.v x <= 252 then weaken parse_bcvli_payload_kind (parse_ret (x <: U32.t)) else
  if U32.v x = 253 then weaken parse_bcvli_payload_kind ((parse_bounded_integer_le 2 `parse_filter` (fun x -> U32.v x >= 253)) `parse_synth` (fun x -> (x <: U32.t))) else
  if U32.v x = 254 then weaken parse_bcvli_payload_kind ((parse_bounded_integer_le 4 `parse_filter` (fun x -> U32.v x >= 65536)) `parse_synth` (fun x -> (x <: U32.t))) else
  fail_parser parse_bcvli_payload_kind U32.t

#push-options "--z3rlimit 32"

let parse_bcvli_payload_and_then_cases_injective : squash (and_then_cases_injective parse_bcvli_payload) =
  and_then_cases_injective_intro parse_bcvli_payload (fun x1 x2 b1 b2 ->
    parse_synth_eq (parse_bounded_integer_le 2 `parse_filter` (fun x -> U32.v x >= 253)) (fun x -> (x <: U32.t)) b1;
    parse_synth_eq (parse_bounded_integer_le 2 `parse_filter` (fun x -> U32.v x >= 253)) (fun x -> (x <: U32.t)) b2;
    parse_synth_eq (parse_bounded_integer_le 4 `parse_filter` (fun x -> U32.v x >= 65536)) (fun x -> (x <: U32.t)) b1;
    parse_synth_eq (parse_bounded_integer_le 4 `parse_filter` (fun x -> U32.v x >= 65536)) (fun x -> (x <: U32.t)) b2
  )

#pop-options

inline_for_extraction
let parse_bcvli_kind = and_then_kind (parse_bounded_integer_kind 1) parse_bcvli_payload_kind

let parse_bcvli : parser parse_bcvli_kind U32.t =
  parse_bounded_integer_le 1 `and_then` parse_bcvli_payload

let parse_bcvli_eq (b: bytes) : Lemma
  (parse parse_bcvli b == (match parse (parse_bounded_integer_le 1) b with
  | None -> None
  | Some (x32, consumed_x) ->
    let x = U32.v x32 in
    if x <= 252 then Some (x32, consumed_x) else
    let b' = Seq.slice b consumed_x (Seq.length b) in
    if x = 253 then
      match parse (parse_bounded_integer_le 2) b' with
      | None -> None
      | Some (y, consumed_y) ->
        if U32.v y < 253 then None (* redundant representations not supported, non-malleability *) else Some (y, consumed_x + consumed_y)
    else if x = 254 then
      match parse (parse_bounded_integer_le 4) b' with
      | None -> None
      | Some (y, consumed_y) ->
        if U32.v y < 65536 then None (* redundant representations not supported, non-malleability *) else Some (y, consumed_x + consumed_y)
    else None (* 64-bit integers not supported *)
  ))
= and_then_eq (parse_bounded_integer_le 1) parse_bcvli_payload b;
  match parse (parse_bounded_integer_le 1) b with
  | None -> ()
  | Some (x32, consumed_x) ->
    let b' = Seq.slice b consumed_x (Seq.length b) in
    parse_synth_eq (parse_bounded_integer_le 2 `parse_filter` (fun x -> U32.v x >= 253)) (fun x -> (x <: U32.t)) b';
    parse_filter_eq (parse_bounded_integer_le 2) (fun x -> U32.v x >= 253) b';
    parse_synth_eq (parse_bounded_integer_le 4 `parse_filter` (fun x -> U32.v x >= 65536)) (fun x -> (x <: U32.t)) b';
    parse_filter_eq (parse_bounded_integer_le 4) (fun x -> U32.v x >= 65536) b'


let serialize_bounded_integer_le'
  (sz: integer_size)
: Tot (bare_serializer (bounded_integer sz))
= (fun (x: bounded_integer sz) ->
    let res = E.n_to_le (U32.uint_to_t sz) (U32.v x) in
    res
  )

#push-options "--z3rlimit 16"

let serialize_bounded_integer_le_correct
  (sz: integer_size)
: Lemma
  (serializer_correct (parse_bounded_integer_le sz) (serialize_bounded_integer_le' sz))
= let prf
    (x: bounded_integer sz)
  : Lemma
    (
      let res = serialize_bounded_integer_le' sz x in
      Seq.length res == (sz <: nat) /\
      parse (parse_bounded_integer_le sz) res == Some (x, (sz <: nat))
    )
  = ()
  in
  Classical.forall_intro prf

#pop-options

let serialize_bounded_integer_le
  (sz: integer_size)
: Tot (serializer (parse_bounded_integer_le sz))
= serialize_bounded_integer_le_correct sz;
  serialize_bounded_integer_le' sz

inline_for_extraction
let synth_u16_le_recip
  (x: U16.t)
: Tot (bounded_integer 2)
= Cast.uint16_to_uint32 x

#push-options "--z3rlimit 16"

let synth_u16_le_inverse : squash (synth_inverse synth_u16_le synth_u16_le_recip) = ()

let serialize_u16_le : serializer parse_u16_le =
  serialize_synth
    _
    synth_u16_le
    (serialize_bounded_integer_le 2)
    synth_u16_le_recip
    ()

#pop-options

inline_for_extraction
let synth_u32_le_recip
  (x: U32.t)
: Tot (bounded_integer 4)
= x

let serialize_u32_le : serializer parse_u32_le =
  serialize_synth
    _
    synth_u32_le
    (serialize_bounded_integer_le 4)
    synth_u32_le_recip
    ()

let bare_serialize_bcvli (x: U32.t) : GTot bytes =
  let c1 : bounded_integer 1 =
    if U32.v x <= 252 then
      x
    else if U32.v x <= 65535 then
      253ul
    else
      254ul
  in
  Seq.append
    (serialize (serialize_bounded_integer_le 1) c1)
    (
      if U32.v c1 <= 252 then Seq.empty else
      if U32.v c1 = 253 then serialize (serialize_bounded_integer_le 2) x else
      serialize (serialize_bounded_integer_le 4) x
    )

#push-options "--z3rlimit 32"

let bare_serialize_bcvli_correct : squash
  (serializer_correct parse_bcvli bare_serialize_bcvli)
= let prf (x: U32.t) : Lemma
    (let y = bare_serialize_bcvli x in
     parse parse_bcvli y == Some (x, Seq.length y))
  = let y = bare_serialize_bcvli x in
    let c1 : bounded_integer 1 =
      if U32.v x <= 252 then
        x
      else if U32.v x <= 65535 then
        253ul
      else
        254ul
    in
    let sc1 = serialize (serialize_bounded_integer_le 1) c1 in
    parse_strong_prefix (parse_bounded_integer_le 1) sc1 y;
    let y' = Seq.slice y (Seq.length sc1) (Seq.length y) in
    parse_bcvli_eq y;
    if U32.v c1 <= 252 then begin
      assert (y `Seq.equal` sc1)
    end else if U32.v c1 = 253 then begin
      assert (U32.v x <= 65535);
      assert (y' `Seq.equal` serialize (serialize_bounded_integer_le 2) x)
    end else begin
      assert (y' `Seq.equal` serialize (serialize_bounded_integer_le 4) x)
    end
  in
  Classical.forall_intro (Classical.move_requires prf)

#pop-options

let serialize_bcvli : serializer parse_bcvli = bare_serialize_bcvli

module U8 = FStar.UInt8

#push-options "--max_fuel 5 --z3rlimit 16"

let bounded_integer_of_le_1_eq
  (b: bytes { Seq.length b == 1 } )
: Lemma
  (U32.v (bounded_integer_of_le 1 b) == U8.v (Seq.index b 0))
= ()

let bounded_integer_of_le_2_eq
  (b: bytes { Seq.length b == 2 } )
: Lemma
  (U32.v (bounded_integer_of_le 2 b) == U8.v (Seq.index b 0) + 256 `FStar.Mul.op_Star` U8.v (Seq.index b 1))
= ()

let bounded_integer_of_le_4_eq
  (b: bytes { Seq.length b == 4 } )
: Lemma
  (U32.v (bounded_integer_of_le 4 b) == U8.v (Seq.index b 0) + 256 `FStar.Mul.op_Star` (U8.v (Seq.index b 1) + 256 `FStar.Mul.op_Star` (U8.v (Seq.index b 2) + 256 `FStar.Mul.op_Star` U8.v (Seq.index b 3))))
= ()

#pop-options

let serialize_bounded_integer_le_1_eq
  (x: bounded_integer 1)
  (i: nat { i < 1 } )
: Lemma
  (U8.v (Seq.index (serialize (serialize_bounded_integer_le 1) x) i) == U32.v x % 256)
= ()

#push-options "--max_fuel 5 --z3rlimit 64"

let serialize_bounded_integer_le_2_eq
  (x: bounded_integer 2)
  (i: nat { i < 2 } )
: Lemma
  (U8.v (Seq.index (serialize (serialize_bounded_integer_le 2) x) i) == (
    let rem = U32.v x % 256 in
    let div = U32.v x / 256 in
    if i = 0
    then rem
    else div % 256
  ))
= ()

let serialize_bounded_integer_le_4_eq
  (x: bounded_integer 4)
  (i: nat { i < 4 } )
: Lemma
  (U8.v (Seq.index (serialize (serialize_bounded_integer_le 4) x) i) == (
    let rem0 = U32.v x % 256 in
    let div0 = U32.v x / 256 in
    let rem1 = div0 % 256 in
    let div1 = div0 / 256 in
    let rem2 = div1 % 256 in
    let div2 = div1 / 256 in
    if i = 0
    then rem0
    else if i = 1
    then rem1
    else if i = 2
    then rem2
    else div2 % 256
  ))
= ()

#pop-options
