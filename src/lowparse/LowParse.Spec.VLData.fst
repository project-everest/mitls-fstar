module LowParse.Spec.VLData
include LowParse.Spec.FLData

module Seq = FStar.Seq
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module M = LowParse.Math

let integer_size : Type0 = (sz: nat { 1 <= sz /\ sz <= 4 } )

#reset-options "--z3cliopt smt.arith.nl=false --using_facts_from '*  -FStar.UInt8 -FStar.UInt16' --z3rlimit 32"

let integer_size_values (i: integer_size) : Lemma
  (i == 1 \/ i == 2 \/ i == 3 \/ i == 4)
= ()

#reset-options

inline_for_extraction
let bounded_integer
  (i: integer_size)
: Tot Type0
= (u: U32.t { U32.v u < pow2 (FStar.Mul.op_Star 8 i) } )

let decode_bounded_integer
  (i: integer_size)
  (b: bytes { Seq.length b == i } )
: GTot (bounded_integer i)
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)


#set-options "--z3rlimit 16"
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
    E.be_to_n_inj b1 b2
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
= total_constant_size_parser_kind i

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
= strong_parser_kind 0 (parse_vldata_payload_size sz) ({
    parser_kind_metadata_total = false;
  })

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
= strong_parser_kind sz (sz + parse_vldata_payload_size sz) ({
    parser_kind_metadata_total = false;
  })

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

let parse_vldata_gen_eq
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes)
: Lemma
  (parse (parse_vldata_gen sz f p) input == (match parse (parse_bounded_integer sz) input with
  | None -> None
  | Some (len, _) ->
    if f len
    then begin
      if Seq.length input < sz + U32.v len
      then None
      else
      let input' = Seq.slice input sz (sz + U32.v len) in
      match parse p input' with
      | Some (x, consumed_x) ->
        if consumed_x = U32.v len
        then Some (x, sz + U32.v len)
        else None
      | _ -> None
    end
    else None
  ))
= parse_filter_eq (parse_bounded_integer sz) f input;
  match parse (parse_bounded_integer sz) input with
  | None -> ()
  | Some (len, consumed_len) ->
    if f len
    then
      let input1 = Seq.slice input consumed_len (Seq.length input) in
      if Seq.length input1 < U32.v len
      then ()
      else begin
        let input' = Seq.slice input consumed_len (consumed_len + U32.v len) in
        assert (input' == Seq.slice input1 0 (U32.v len));
        assert (parse (parse_vldata_gen sz f p) input == (match parse_fldata' p (U32.v len) input1 with
        | None -> None
        | Some (x, consumed_x) -> Some (x, consumed_len + consumed_x)
        ));
        ()
      end
    else ()

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

let parse_vldata_eq
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes)
: Lemma
  (parse (parse_vldata sz p) input == (match parse (parse_bounded_integer sz) input with
  | None -> None
  | Some (len, _) ->
    begin
      if Seq.length input < sz + U32.v len
      then None
      else
      let input' = Seq.slice input sz (sz + U32.v len) in
      match parse p input' with
      | Some (x, consumed_x) ->
        if consumed_x = U32.v len
        then Some (x, sz + U32.v len)
        else None
      | _ -> None
    end
  ))
= parse_vldata_gen_eq sz (unconstrained_bounded_integer _) p input

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
= strong_parser_kind (log256' max + min) (log256' max + max) ({
    parser_kind_metadata_total = false;
  })

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
= parse_vldata_gen_eq (log256' max) (in_bounds min max) p xbytes

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

let parse_bounded_vldata_elim_forall
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (xbytes: bytes)
: Lemma
  (requires (Some? (parse (parse_bounded_vldata min max p) xbytes)))
  (ensures (
    let (Some (x, consumed)) = parse (parse_bounded_vldata min max p) xbytes in
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
= let (Some (x, consumed)) = parse (parse_bounded_vldata min max p) xbytes in
  parse_bounded_vldata_elim min max p xbytes x consumed

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

inline_for_extraction
let parse_bounded_vldata_strong_kind
  (min: nat)
  (max: nat)
  (k: parser_kind)
: Pure parser_kind
  (requires (min <= max /\ max > 0 /\ max < 4294967296 ))
  (ensures (fun _ -> True))
= [@inline_let]
  let kmin = k.parser_kind_low in
  [@inline_let]
  let min' = if kmin > min then kmin else min in
  [@inline_let]
  let max' = match k.parser_kind_high with
  | None -> max
  | Some kmax -> if kmax < max then kmax else max
  in
  [@inline_let]
  let max' = if max' < min' then min' else max' in
  (* the size of the length prefix must conform to the max bound given by the user, not on the metadata *)
  strong_parser_kind (log256' max + min') (log256' max + max') ({
    parser_kind_metadata_total = false;
  })

let parse_bounded_vldata_strong'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot (parser (parse_bounded_vldata_kind min max) (parse_bounded_vldata_strong_t min max s)) 
= // strengthen (parse_bounded_vldata_strong_kind min max k)
  (
  coerce_parser
  (parse_bounded_vldata_strong_t min max s)
  (parse_strengthen (parse_bounded_vldata min max p) (parse_bounded_vldata_strong_pred min max s) (parse_bounded_vldata_strong_correct min max s))
  )

#reset-options "--z3cliopt smt.arith.nl=false --using_facts_from '*  -FStar.UInt8 -FStar.UInt16' --z3rlimit 32"

let parse_bounded_vldata_strong'_consumed
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: bytes)
: Lemma
  (requires (Some? (parse (parse_bounded_vldata_strong' min max s) input)))
  (ensures (
    let pp = parse (parse_bounded_vldata_strong' min max s) input in
    Some? pp /\ (
    let Some (data, consumed) = pp in
    let max' = (parse_bounded_vldata_strong_kind min max k).parser_kind_high in
      (parse_bounded_vldata_strong_kind min max k).parser_kind_low <= consumed /\
      Some? max' /\
      consumed <= Some?.v max'
  )))
= ()

let parse_bounded_vldata_strong'_parser_kind_prop
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Lemma
  (parser_kind_prop (parse_bounded_vldata_strong_kind min max k) (parse_bounded_vldata_strong' min max s))
= Classical.forall_intro (Classical.move_requires (parse_bounded_vldata_strong'_consumed min max s))

#reset-options

let parse_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot (parser (parse_bounded_vldata_strong_kind min max k) (parse_bounded_vldata_strong_t min max s))
= let p' = parse_bounded_vldata_strong' min max s in
  let k' = parse_bounded_vldata_strong_kind min max k in
  parse_bounded_vldata_strong'_parser_kind_prop min max s;
  strengthen k' p'

let serialize_bounded_integer'
  (sz: integer_size)
: Tot (bare_serializer (bounded_integer sz))
= (fun (x: bounded_integer sz) ->
    let res = E.n_to_be (U32.uint_to_t sz) (U32.v x) in
    res
  )

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

let serialize_bounded_integer
  (sz: integer_size)
: Tot (serializer (parse_bounded_integer sz))
= serialize_bounded_integer_correct sz;
  serialize_bounded_integer' sz

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

let serialize_vldata_gen_correct_aux sz f #k #t p b b1 b2 =
  let (Some (len, consumed1)) = parse (parse_bounded_integer sz) b1 in
  assert (consumed1 == sz);
  assert (no_lookahead_on (parse_bounded_integer sz) b1 b);
  assert (injective_postcond (parse_bounded_integer sz) b1 b);
  assert (parse (parse_bounded_integer sz) b == Some (len, sz));
  assert (sz + U32.v len == Seq.length b);
  assert (b2 == Seq.slice b sz (sz + U32.v len));
  parse_vldata_gen_eq sz f p b

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

let serialize_bounded_vldata_strong_upd
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
  (y: t)
: Lemma
  (requires (Seq.length (serialize s y) == Seq.length (serialize s x)))
  (ensures (
    let sy = serialize s y in
    let y : parse_bounded_vldata_strong_t min max s = y in
    let sx = serialize (serialize_bounded_vldata_strong min max s) x in
    let lm = log256' max in
    lm + Seq.length sy == Seq.length sx /\
    serialize (serialize_bounded_vldata_strong min max s) y == seq_upd_seq sx lm sy
  ))
=   let y : parse_bounded_vldata_strong_t min max s = y in
    let sx = serialize s x in
    let sx' = serialize (serialize_bounded_vldata_strong min max s) x in
    let sy = serialize s y in
    let sy' = serialize (serialize_bounded_vldata_strong min max s) y in
    let lm = log256' max in
    let sz = serialize (serialize_bounded_integer lm) (U32.uint_to_t (Seq.length sx)) in
    assert (lm + Seq.length sy == Seq.length sx');
    seq_upd_seq_right sx' sy;
    Seq.lemma_split sx' lm;
    Seq.lemma_split sy' lm;
    Seq.lemma_append_inj (Seq.slice sx' 0 lm) (Seq.slice sx' lm (Seq.length sx')) sz sx;
    Seq.lemma_append_inj (Seq.slice sy' 0 lm) (Seq.slice sy' lm (Seq.length sy')) sz sy;
    assert (sy' `Seq.equal` seq_upd_seq sx' lm sy)

let serialize_bounded_vldata_strong_upd_bw
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
  (y: t)
: Lemma
  (requires (Seq.length (serialize s y) == Seq.length (serialize s x)))
  (ensures (
    let sy = serialize s y in
    let y : parse_bounded_vldata_strong_t min max s = y in
    let sx = serialize (serialize_bounded_vldata_strong min max s) x in
    let lm = log256' max in
    lm + Seq.length sy == Seq.length sx /\
    serialize (serialize_bounded_vldata_strong min max s) y == seq_upd_bw_seq sx 0 sy
  ))
= serialize_bounded_vldata_strong_upd min max s x y

let serialize_bounded_vldata_strong_upd_chain
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_seq sx i' s'
  ))
  (ensures (
    parse_bounded_vldata_strong_pred min max s y /\ (
    let y : parse_bounded_vldata_strong_t min max s = y in
    let sx' = serialize (serialize_bounded_vldata_strong min max s) x in
    let lm = log256' max in
    lm + Seq.length (serialize s x) == Seq.length sx' /\
    lm + i' + Seq.length s' <= Seq.length sx' /\
    serialize (serialize_bounded_vldata_strong min max s) y == seq_upd_seq sx' (lm + i') s'
  )))
= serialize_bounded_vldata_strong_upd min max s x y;
  let sx = serialize s x in
  let sx' = serialize (serialize_bounded_vldata_strong min max s) x in
  let lm = log256' max in
  let sz = serialize (serialize_bounded_integer lm) (U32.uint_to_t (Seq.length sx)) in
  seq_upd_seq_right_to_left sx' lm sx i' s';
  Seq.lemma_split sx' lm;
  Seq.lemma_append_inj (Seq.slice sx' 0 lm) (Seq.slice sx' lm (Seq.length sx')) sz sx;
  seq_upd_seq_seq_upd_seq_slice sx' lm (Seq.length sx') i' s'

#reset-options "--z3refresh --z3rlimit 32 --z3cliopt smt.arith.nl=false"

let serialize_bounded_vldata_strong_upd_bw_chain
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: parse_bounded_vldata_strong_t min max s)
  (y: t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let sx = serialize s x in
    i' + Seq.length s' <= Seq.length sx /\
    serialize s y == seq_upd_bw_seq sx i' s'
  ))
  (ensures (
    parse_bounded_vldata_strong_pred min max s y /\ (
    let y : parse_bounded_vldata_strong_t min max s = y in
    let sx' = serialize (serialize_bounded_vldata_strong min max s) x in
    let lm = log256' max in
    lm + Seq.length (serialize s x) == Seq.length sx' /\
    i' + Seq.length s' <= Seq.length sx' /\
    serialize (serialize_bounded_vldata_strong min max s) y == seq_upd_bw_seq sx' i' s'
  )))
= serialize_bounded_vldata_strong_upd_chain min max s x y (Seq.length (serialize s x) - i' - Seq.length s') s'
