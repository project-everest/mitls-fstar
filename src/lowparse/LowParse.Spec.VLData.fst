module LowParse.Spec.VLData
include LowParse.Spec.FLData
include LowParse.Spec.Int

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast

let integer_size : Type0 = (sz: nat { 1 <= sz /\ sz <= 4 } )

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 32"

let integer_size_values (i: integer_size) : Lemma
  (i == 1 \/ i == 2 \/ i == 3 \/ i == 4)
= ()

#reset-options

inline_for_extraction
let bounded_integer
  (i: integer_size)
: Tot Type0
= (u: U32.t { U32.v u < pow2 (FStar.Mul.op_Star 8 i) } )

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --z3refresh"

let decode_bounded_integer
  (i: integer_size)
  (b: bytes { Seq.length b == i } )
: GTot (bounded_integer i)
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

#reset-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --z3refresh"

let decode_bounded_integer_injective'
  (i: integer_size)
  (b1: bytes { Seq.length b1 == i } )
  (b2: bytes { Seq.length b2 == i } )
: Lemma
  (decode_bounded_integer i b1 == decode_bounded_integer i b2 ==> Seq.equal b1 b2)
= if decode_bounded_integer i b1 = decode_bounded_integer i b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    be_to_n_inj b1 b2
  end else ()

#reset-options

let decode_bounded_integer_injective
  (i: integer_size)
: Lemma
  (make_total_constant_size_parser_precond i (bounded_integer i) (decode_bounded_integer i))
= Classical.forall_intro_2 (decode_bounded_integer_injective' i)

// unfold
let parse_bounded_integer_kind
  (i: integer_size)
: Tot parser_kind
= {
    parser_kind_low = i;
    parser_kind_high = Some i;
    parser_kind_total = true;
    parser_kind_subkind = Some ParserStrong;
  }

let parse_bounded_integer
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))
= decode_bounded_integer_injective i;
  make_total_constant_size_parser i (bounded_integer i) (decode_bounded_integer i)

#reset-options "--z3rlimit 64 --max_fuel 64 --max_ifuel 64 --z3refresh --z3cliopt smt.arith.nl=false"

let parse_vldata_payload_size
  (sz: integer_size)
: Pure nat
  (requires True)
  (ensures (fun y -> y == pow2 (FStar.Mul.op_Star 8 sz) - 1 ))
= match sz with
  | 1 -> 255
  | 2 -> 65535
  | 3 -> 16777215
  | 4 -> 4294967295

#reset-options

// unfold
let parse_vldata_payload_kind
  (sz: integer_size)
: parser_kind
= {
    parser_kind_low = 0;
    parser_kind_high = Some (parse_vldata_payload_size sz);
    parser_kind_total = false;
    parser_kind_subkind = Some ParserStrong;
  }

let parse_vldata_payload
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (i: bounded_integer sz { f i == true } )
: Tot (parser (parse_vldata_payload_kind sz) t)
= weaken (parse_vldata_payload_kind sz) (parse_fldata p (U32.v i))

#set-options "--z3rlimit 64"

let parse_fldata_and_then_cases_injective
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Lemma
  (and_then_cases_injective (parse_vldata_payload sz f p))
= let g
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1 b2: bytes)
  : Lemma
    (requires (and_then_cases_injective_precond (parse_vldata_payload sz f p) len1 len2 b1 b2))
    (ensures (len1 == len2))
  = assert (injective_precond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (injective_postcond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (len1 == len2)
  in
  let g'
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1: bytes)
  : Lemma
    (forall (b2: bytes) . and_then_cases_injective_precond (parse_vldata_payload sz f p) len1 len2 b1 b2 ==> len1 == len2)
  = Classical.forall_intro (Classical.move_requires (g len1 len2 b1))
  in
  Classical.forall_intro_3 g'

#reset-options

// unfold
let parse_vldata_gen_kind
  (sz: integer_size)
: Tot parser_kind
= {
    parser_kind_low = sz;
    parser_kind_high = Some (sz + parse_vldata_payload_size sz);
    parser_kind_total = false;
    parser_kind_subkind = Some ParserStrong;
  }

let parse_vldata_gen_kind_correct
  (sz: integer_size)
: Lemma
  ( (parse_vldata_gen_kind sz) == (and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) (parse_vldata_payload_kind sz)))
= let kl = parse_vldata_gen_kind sz in
  let kr = and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) (parse_vldata_payload_kind sz) in
  assert_norm (kl == kr)

let parse_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser (parse_vldata_gen_kind sz) t)
= parse_fldata_and_then_cases_injective sz f p;
  parse_vldata_gen_kind_correct sz;
  (parse_filter (parse_bounded_integer sz) f)
  `and_then`
  parse_vldata_payload sz f p

let unconstrained_bounded_integer
  (sz: integer_size)
  (i: bounded_integer sz)
: GTot bool
= true

let parse_vldata
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser _ t)
= parse_vldata_gen sz (unconstrained_bounded_integer sz) p


(** Explicit bounds on size *)

inline_for_extraction
val log256'
  (n: nat)
: Pure integer_size
  (requires (n > 0 /\ n < 4294967296))
  (ensures (fun l ->
    pow2 (FStar.Mul.op_Star 8 (l - 1)) <= n /\
    n < pow2 (FStar.Mul.op_Star 8 l)
  ))

#reset-options "--z3rlimit 16 --z3cliopt smt.arith.nl=false"

let log256' n =
  [@inline_let]
  let _ = assert_norm (pow2 32 == 4294967296) in
  [@inline_let]
  let _ = assert (n < pow2 32) in
  [@inline_let]
  let z0 = 1 in
  [@inline_let]
  let z1 = 256 in
  [@inline_let]
  let _ = assert_norm (z1 == Prims.op_Multiply 256 z0) in
  [@inline_let]
  let l = 1 in
  [@inline_let]
  let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == z1) in
  [@inline_let]
  let _ = assert_norm (pow2 (Prims.op_Multiply 8 (l - 1)) == z0) in
  if n < z1
  then begin
    [@inline_let]
    let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
    [@inline_let]
    let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
    l
  end else begin
    [@inline_let]
    let z2 = 65536 in
    [@inline_let]
    let _ = assert_norm (z2 == Prims.op_Multiply 256 z1) in
    [@inline_let]
    let l = 2 in
    [@inline_let]
    let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == z2) in
    if n < z2
    then begin
      [@inline_let]
      let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
      [@inline_let]
      let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
      l
    end else begin
      [@inline_let]
      let z3 = 16777216 in
      [@inline_let]
      let _ = assert_norm (z3 == Prims.op_Multiply 256 z2) in
      [@inline_let]
      let l = 3 in
      [@inline_let]
      let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == z3) in
      if n < z3
      then begin
        [@inline_let]
	let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
        [@inline_let]
	let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
        l    
      end else begin
        [@inline_let]
        let l = 4 in
        [@inline_let]
        let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == Prims.op_Multiply 256 z3) in
        [@inline_let]
	let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
        [@inline_let]
	let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
        l
      end
    end
  end

#reset-options

let in_bounds
  (min: nat)
  (max: nat)
  (x: U32.t)
: GTot bool
= not (U32.v x < min || max < U32.v x)

// unfold
let parse_bounded_vldata_kind
  (min: nat)
  (max: nat)
: Pure parser_kind
  (requires (min <= max /\ max > 0 /\ max < 4294967296 ))
  (ensures (fun _ -> True))
= {
    parser_kind_low = log256' max + min;
    parser_kind_high = Some (log256' max + max);
    parser_kind_total = false;
    parser_kind_subkind = Some ParserStrong;
  }

#reset-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --z3refresh"

let parse_bounded_vldata_elim'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (xbytes: bytes)
  (x: t)
  (consumed: consumed_length xbytes)
: Lemma
  (requires (parse (parse_vldata_gen (log256' max) (in_bounds min max) p) xbytes == Some (x, consumed)))
  (ensures (
    let sz : integer_size = log256' max in
    let plen = parse (parse_bounded_integer sz) xbytes in
    Some? plen /\ (
    let (Some (len, consumed_len)) = plen in
    (consumed_len <: nat) == (sz <: nat) /\
    in_bounds min max len /\
    U32.v len <= Seq.length xbytes - sz /\ (
    let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
    let pp = parse p input' in
    Some? pp /\ (
    let (Some (x', consumed_p)) = pp in
    x' == x /\
    (consumed_p <: nat) == U32.v len /\
    (consumed <: nat) == sz + U32.v len
  )))))
=   let sz : integer_size = log256' max in
    let plen_ = parse (parse_filter (parse_bounded_integer sz) (in_bounds min max)) xbytes in
    assert (Some? plen_);
    let (Some (len_, consumed_len_)) = plen_ in
    let plen = parse (parse_bounded_integer sz) xbytes in
    assert (Some? plen);
    let (Some (len, consumed_len)) = plen in
    assert ((len <: U32.t) == (len_ <: U32.t));
    assert (consumed_len_ == consumed_len);    
    assert ((consumed_len <: nat) == (sz <: nat));
    assert (in_bounds min max len);
    let input1 = Seq.slice xbytes sz (Seq.length xbytes) in
    let pp1 = parse (parse_vldata_payload sz (in_bounds min max) p len) input1 in
    assert (Some? pp1);
    let (Some (x1, consumed_p1)) = pp1 in
    assert (x == x1);
    let pp15 = parse (parse_fldata p (U32.v len)) input1 in
    assert (Some? pp15);
    let (Some (x15, consumed_p15)) = pp15 in
    assert (x == x15);
    assert (consumed_p1 == consumed_p15);
    assert (U32.v len <= Seq.length xbytes - sz);
    let input' = Seq.slice input1 0 (U32.v len) in
    assert (input' == Seq.slice xbytes (sz <: nat) (sz + U32.v len));
    let pp = parse p input' in
    assert (Some? pp);
    let (Some (x', consumed_p)) = pp in
    assert (x == x');
    assert ((consumed_p <: nat) == U32.v len);
    assert ((consumed <: nat) == sz + consumed_p);
    ()

let parse_bounded_vldata_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Lemma
  (parser_kind_prop (parse_bounded_vldata_kind min max) (parse_vldata_gen (log256' max) (in_bounds min max) p))
= let sz : integer_size = log256' max in
  let p' = parse_vldata_gen sz (in_bounds min max) p in
  let prf
    (input: bytes)
  : Lemma
    (requires (Some? (parse p' input)))
    (ensures (
      let pi = parse p' input in
      Some? pi /\ (
      let (Some (_, consumed)) = pi in
      sz + min <= (consumed <: nat) /\
      (consumed <: nat) <= sz + max
    )))
  = let (Some (data, consumed)) = parse p' input in
    parse_bounded_vldata_elim' min max p input data consumed 
  in
  Classical.forall_intro (Classical.move_requires prf)

#reset-options

let parse_bounded_vldata
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser (parse_bounded_vldata_kind min max) t)
= parse_bounded_vldata_correct min max p;
  strengthen (parse_bounded_vldata_kind min max) (parse_vldata_gen (log256' max) (in_bounds min max) p)

let parse_bounded_vldata_elim
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (xbytes: bytes)
  (x: t)
  (consumed: consumed_length xbytes)
: Lemma
  (requires (parse (parse_bounded_vldata min max p) xbytes == Some (x, consumed)))
  (ensures (
    let sz : integer_size = log256' max in
    let plen = parse (parse_bounded_integer sz) xbytes in
    Some? plen /\ (
    let (Some (len, consumed_len)) = plen in
    (consumed_len <: nat) == (sz <: nat) /\
    in_bounds min max len /\
    U32.v len <= Seq.length xbytes - sz /\ (
    let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
    let pp = parse p input' in
    Some? pp /\ (
    let (Some (x', consumed_p)) = pp in
    x' == x /\
    (consumed_p <: nat) == U32.v len /\
    (consumed <: nat) == sz + U32.v len
  )))))
= parse_bounded_vldata_elim' min max p xbytes x consumed

(* Serialization *)

let parse_bounded_vldata_strong_pred
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: GTot Type0
= let reslen = Seq.length (s x) in
  min <= reslen /\ reslen <= max

let parse_bounded_vldata_strong_t
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot Type0
= (x: t { parse_bounded_vldata_strong_pred min max s x } )

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --z3refresh"

let parse_bounded_vldata_strong_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (xbytes: bytes)
  (consumed: consumed_length xbytes)
  (x: t)
: Lemma
  (requires (parse (parse_bounded_vldata min max p) xbytes == Some (x, consumed)))
  (ensures (parse_bounded_vldata_strong_pred min max s x))
= parse_bounded_vldata_elim min max p xbytes x consumed;
  let sz : integer_size = log256' max in
  let plen = parse (parse_bounded_integer sz) xbytes in
  let f () : Lemma (Some? plen) =
    parse_bounded_vldata_elim min max p xbytes x consumed
  in
  f ();
  let (Some (len, _)) = plen in
  let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
  assert (Seq.equal input' (Seq.slice input' 0 (U32.v len)));
  serializer_correct_implies_complete p s;
  assert (s x == input');
  ()

#reset-options

let parse_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot (parser (parse_bounded_vldata_kind min max) (parse_bounded_vldata_strong_t min max s)) 
= coerce_parser
  (parse_bounded_vldata_strong_t min max s)
  (parse_strengthen (parse_bounded_vldata min max p) (parse_bounded_vldata_strong_pred min max s) (parse_bounded_vldata_strong_correct min max s))

let serialize_bounded_integer'
  (sz: integer_size)
: Tot (bare_serializer (bounded_integer sz))
= (fun (x: bounded_integer sz) ->
    let res = E.n_to_be (U32.uint_to_t sz) (U32.v x) in
    res
  )

#set-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8"

let serialize_bounded_integer_correct
  (sz: integer_size)
: Lemma
  (serializer_correct (parse_bounded_integer sz) (serialize_bounded_integer' sz))
= let prf
    (x: bounded_integer sz)
  : Lemma
    (
      let res = serialize_bounded_integer' sz x in
      Seq.length res == (sz <: nat) /\
      parse (parse_bounded_integer sz) res == Some (x, (sz <: nat))
    )
  = ()
  in
  Classical.forall_intro prf

#reset-options

let serialize_bounded_integer
  (sz: integer_size)
: Tot (serializer (parse_bounded_integer sz))
= serialize_bounded_integer_correct sz;
  serialize_bounded_integer' sz

#set-options "--z3rlimit 64"

let serialize_bounded_vldata_strong'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot (bare_serializer (parse_bounded_vldata_strong_t min max s))
= (fun (x: parse_bounded_vldata_strong_t min max s) ->
  let pl = s x in
  let sz = log256' max in
  let nlen = Seq.length pl in
  assert (min <= nlen /\ nlen <= max);
  let len = U32.uint_to_t nlen in
  let slen = serialize (serialize_bounded_integer sz) len in
  seq_slice_append_l slen pl;
  seq_slice_append_r slen pl;
  Seq.append slen pl
  )

val serialize_vldata_gen_correct_aux
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b b1 b2: bytes)
: Lemma
  (requires (
    Seq.length b1 == sz /\ (
    let vlen = parse (parse_bounded_integer sz) b1 in
    Some? vlen /\ (
    let (Some (len, _)) = vlen in
    f len == true /\
    Seq.length b2 == U32.v len /\ (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (_, consumed)) = vv in
    consumed == Seq.length b2 /\
    Seq.length b1 <= Seq.length b /\
    Seq.slice b 0 (Seq.length b1) == b1 /\
    Seq.slice b (Seq.length b1) (Seq.length b) == b2
  ))))))
  (ensures (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (v, consumed)) = vv in
    let vv' = parse (parse_vldata_gen sz f p) b in
    Some? vv' /\ (
    let (Some (v', consumed')) = vv' in
    v == v' /\
    consumed == Seq.length b2 /\
    consumed' == Seq.length b
  ))))

#reset-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --z3refresh"

let serialize_vldata_gen_correct_aux sz f #k #t p b b1 b2 =
  let (Some (len, consumed1)) = parse (parse_bounded_integer sz) b1 in
  assert (consumed1 == sz);
  assert (no_lookahead_on (parse_bounded_integer sz) b1 b);
  let v1' = parse (parse_bounded_integer sz) b in
  assert (Some? v1');
  let (Some (len', consumed1')) = v1' in
  assert (consumed1' == sz);
  assert (injective_postcond (parse_bounded_integer sz) b1 b);
  assert (len' == len);
  let v1_ = parse (parse_filter (parse_bounded_integer sz) f) b in
  assert (Some? v1_);
  let (Some (len_, consumed1_)) = v1_ in
  assert (consumed1_ == sz);
  assert ((len_ <: bounded_integer sz) == len);
  assert (Some? (parse p b2));
  assert (b2 == Seq.slice b2 0 (U32.v len));
  assert (Some? (parse (parse_fldata p (U32.v len)) b2));
  assert (Some? (parse (parse_vldata_payload sz f p len) b2));
  assert (Some? (parse (parse_vldata_gen sz f p) b));
//  admit
  ()

#reset-options

val serialize_vldata_gen_correct
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b1 b2: bytes)
: Lemma
  (requires (
    Seq.length b1 == sz /\ (
    let vlen = parse (parse_bounded_integer sz) b1 in
    Some? vlen /\ (
    let (Some (len, _)) = vlen in
    f len == true /\
    Seq.length b2 == U32.v len /\ (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (_, consumed)) = vv in
    consumed == Seq.length b2
  ))))))
  (ensures (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (v, consumed)) = vv in
    let vv' = parse (parse_vldata_gen sz f p) (Seq.append b1 b2) in
    Some? vv' /\ (
    let (Some (v', consumed')) = vv' in
    v == v' /\
    consumed == Seq.length b2 /\
    consumed' == sz + Seq.length b2
  ))))

let serialize_vldata_gen_correct sz f #k #t p b1 b2 =
  seq_slice_append_l b1 b2;
  seq_slice_append_r b1 b2;
  serialize_vldata_gen_correct_aux sz f p (Seq.append b1 b2) b1 b2

#reset-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false --z3refresh"

let serialize_bounded_vldata_strong_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: parse_bounded_vldata_strong_t min max s)
: Lemma
  (let formatted = serialize_bounded_vldata_strong' min max s input in
    parse (parse_bounded_vldata_strong min max s) formatted == Some (input, Seq.length formatted))
= let sz = log256' max in
  let sp = serialize s input in
  let nlen = Seq.length sp in
  assert (min <= nlen /\ nlen <= max);
  let len = U32.uint_to_t nlen in
  assert (U32.v len < pow2 (FStar.Mul.op_Star 8 sz));
  let (len: bounded_integer sz) = len in
  let slen = serialize (serialize_bounded_integer sz) len in
  assert (Seq.length slen == sz);
  let pslen = parse (parse_bounded_integer sz) slen in
  assert (Some? pslen);
  let (Some (len', consumed_len')) = pslen in
  assert (len == len');
  assert (in_bounds min max len' == true);
  assert (Seq.length sp == U32.v len);
  let psp = parse p sp in
  assert (Some? psp);
  let (Some (_, consumed_p)) = psp in
  assert ((consumed_p <: nat) == Seq.length sp);
  serialize_vldata_gen_correct sz (in_bounds min max) p
    slen
    sp
  ;
  ()

let serialize_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot (serializer (parse_bounded_vldata_strong min max s))
= Classical.forall_intro (serialize_bounded_vldata_strong_correct min max s);
  serialize_bounded_vldata_strong' min max s
