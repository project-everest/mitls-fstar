module LowParse.Spec.Sum
include LowParse.Spec.Enum

module Seq = FStar.Seq

inline_for_extraction
val parse_tagged_union
  (#kt: parser_kind)
  (#tag: Type0)
  (#tu: tag -> Type0)
  (pt: parser kt tag)
  (#k: parser_kind)
  (p: (t: tag) -> Tot (parser k (tu t))) // Tot really needed here by validator
: Tot (parser (and_then_kind kt k) (t: tag & tu t))

let parse_tagged_union #kt #tag #tu pt #k p =
  pt `and_then` (fun (v: tag) ->
    let pv : parser k (tu v) = p v in
    let synth : tu v -> Tot (t: tag & tu t) = fun (v': tu v) -> (| v, v' |) in
    parse_synth #k #(tu v) #(t: tag & tu t) pv synth
  )

let bare_serialize_tagged_union
  (#kt: parser_kind)
  (#tag: Type0)
  (#tu: tag -> Type0)
  (pt: parser kt tag)
  (st: serializer pt)
  (#k: parser_kind)
  (p: (t: tag) -> Tot (parser k (tu t))) // Tot really needed here by validator
  (s: (t: tag) -> Tot (serializer (p t)))
: Tot (bare_serializer (t: tag & tu t))
= fun (x: (t: tag & tu t)) ->
  let (| t, u |) = x in
  Seq.append (st t) (serialize (s t) u)

let bare_serialize_tagged_union_correct
  (#kt: parser_kind)
  (#tag: Type0)
  (#tu: tag -> Type0)
  (pt: parser kt tag)
  (st: serializer pt)
  (#k: parser_kind)
  (p: (t: tag) -> Tot (parser k (tu t))) // Tot really needed here by validator
  (s: (t: tag) -> Tot (serializer (p t)))
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (serializer_correct (parse_tagged_union pt p) (bare_serialize_tagged_union pt st p s)))
= (* same proof as nondep_then *)
  let prf
    (x: (t: tag & tu t))
  : Lemma (parse (parse_tagged_union pt p) (bare_serialize_tagged_union pt st p s x) == Some (x, Seq.length (bare_serialize_tagged_union pt st p s x)))
  = let (| t, u |) = x in
    let v1' = parse pt (bare_serialize_tagged_union pt st p s x) in
    let v1 = parse pt (st t) in
    assert (Some? v1);
    assert (no_lookahead_on pt (st t) (bare_serialize_tagged_union pt st p s x));
    let (Some (_, len')) = parse pt (st t) in
    assert (len' == Seq.length (st t));
    assert (len' <= Seq.length (bare_serialize_tagged_union pt st p s x));
    assert (Seq.slice (st t) 0 len' == st t);
    seq_slice_append_l (st t) (serialize (s t) u);
    assert (no_lookahead_on_precond pt (st t) (bare_serialize_tagged_union pt st p s x));
    assert (no_lookahead_on_postcond pt (st t) (bare_serialize_tagged_union pt st p s x));
    assert (Some? v1');
    assert (injective_precond pt (st t) (bare_serialize_tagged_union pt st p s x));
    assert (injective_postcond pt (st t) (bare_serialize_tagged_union pt st p s x));
    let (Some (x1, len1)) = v1 in
    let (Some (x1', len1')) = v1' in
    assert (x1 == x1');
    assert ((len1 <: nat) == (len1' <: nat));
    assert (x1 == t);
    assert (len1 == Seq.length (st t));
    assert (bare_serialize_tagged_union pt st p s x == Seq.append (st t) (serialize (s t) u));
    seq_slice_append_r (st t) (serialize (s t) u);
    ()
  in
  Classical.forall_intro prf

let serialize_tagged_union
  (#kt: parser_kind)
  (#tag: Type0)
  (#tu: tag -> Type0)
  (pt: parser kt tag)
  (st: serializer pt)
  (#k: parser_kind)
  (p: (t: tag) -> Tot (parser k (tu t))) // Tot really needed here by validator
  (s: (t: tag) -> Tot (serializer (p t)))
: Pure (serializer (parse_tagged_union pt p))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= bare_serialize_tagged_union_correct pt st p s;
  bare_serialize_tagged_union pt st p s


inline_for_extraction
let sum = (key: eqtype & (repr: eqtype & (e: enum key repr & ((x: enum_key e) -> Tot Type0))))

inline_for_extraction
let sum_key_type (t: sum) : Tot eqtype =
  let (| key,  _ |) = t in key

inline_for_extraction
let sum_repr_type (t: sum) : Tot eqtype =
  let (| _, (| repr,  _ |) |) = t in repr

let sum_enum (t: sum) : Tot (enum (sum_key_type t) (sum_repr_type t)) =
  let (| _, (| _, (| e, _ |) |) |) = t in e

let sum_key (t: sum) : Tot Type0 =
  enum_key (sum_enum t)

let sum_cases (t: sum) : Tot ((x: sum_key t) -> Tot Type0) =
  let (|_, (| _, (| _, c |) |) |) = t in c

let sum_type (t: sum) : Tot Type0 =
  (x: sum_key t & sum_cases t x)

let weaken_parse_cases_kind
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_cases s x)))
: Tot parser_kind
= let keys : list (sum_key_type s) = List.Tot.map fst (sum_enum s) in
  glb_list_of #(sum_key_type s) (fun (x: sum_key_type s) ->
    if List.Tot.mem x keys
    then let (| k, _ |) = f x in k
    else default_parser_kind
  ) (List.Tot.map fst (sum_enum s))

let parse_sum_cases
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_cases s x)))
  (x: sum_key s)
: Tot (parser _ (sum_cases s x))
= let (| _, p |) = f x in
  weaken (weaken_parse_cases_kind s f) p

inline_for_extraction
let parse_sum
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: Tot (parser (and_then_kind (parse_filter_kind kt) k) (sum_type t))
= parse_tagged_union
    #(parse_filter_kind kt)
    #(sum_key t)
    #(fun (c: sum_key t) -> sum_cases t c) // eta-expansion required here because of the eta-expansion in parse_tagged_union, which could not unify with serialize_sum if not eta-expanded here
    (parse_enum_key p (sum_enum t))
    #k
    pc

let serialize_sum
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (pc x))))
: Pure (serializer (parse_sum t p pc))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_tagged_union
    #(parse_filter_kind kt)
    #(sum_key t)
    #(sum_cases t)
    (parse_enum_key p (sum_enum t))
    (serialize_enum_key p s (sum_enum t))
    #k
    pc
    sc

inline_for_extraction
let make_sum
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
: Tot sum
= (| key, (| repr, (| e, cases |) |) |)

(* Sum with default case *)

inline_for_extraction
let dsum = (sum * Type0)

let dsum_key (t: dsum) : Tot Type0 =
  maybe_enum_key (sum_enum (fst t))

let dsum_cases (t: dsum) (x: dsum_key t): Tot Type0 =
  match x with
  | Known x -> sum_cases (fst t) x
  | Unknown x -> snd t

let dsum_type (t: dsum) : Tot Type0 =
  (x: dsum_key t & dsum_cases t x)

let parse_dsum_cases
  (s: dsum)
  (#k: parser_kind)
  (pc: ((x: sum_key (fst s)) -> Tot (parser k (sum_cases (fst s) x))))
  (pd: parser k (snd s))
  (x: dsum_key s)
: Tot (parser k (dsum_cases s x))
= match x with
  | Known x -> pc x
  | Unknown _ -> pd

let serialize_dsum_cases
  (s: dsum)
  (#k: parser_kind)
  (pc: ((x: sum_key (fst s)) -> Tot (parser k (sum_cases (fst s) x))))
  (sc: ((x: sum_key (fst s)) -> Tot (serializer (pc x))))
  (pd: parser k (snd s))
  (sd: serializer pd)
  (x: dsum_key s)
: Tot (serializer (parse_dsum_cases s pc pd x))
= match x with
  | Known x -> sc x
  | Unknown _ -> sd

inline_for_extraction
let parse_dsum
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (sum_repr_type (fst t)))
  (#k: parser_kind)
  (pc: ((x: sum_key (fst t)) -> Tot (parser k (sum_cases (fst t) x))))
  (pd: parser k (snd t))
: Tot (parser (and_then_kind kt k) (dsum_type t))
= parse_tagged_union
    #kt
    #(dsum_key t)
    #(fun (c: dsum_key t) -> dsum_cases t c) // same as above
    (parse_maybe_enum_key p (sum_enum (fst t)))
    #k
    (parse_dsum_cases t pc pd)

let serialize_dsum
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (sum_repr_type (fst t)))
  (s: serializer p)
  (#k: parser_kind)
  (pc: ((x: sum_key (fst t)) -> Tot (parser k (sum_cases (fst t) x))))
  (sc: ((x: sum_key (fst t)) -> Tot (serializer (pc x))))
  (pd: parser k (snd t))
  (sd: serializer pd)
: Pure (serializer (parse_dsum t p pc pd))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_tagged_union
    #kt
    #(dsum_key t)
    #(dsum_cases t)
    (parse_maybe_enum_key p (sum_enum (fst t)))
    (serialize_maybe_enum_key p s (sum_enum (fst t)))
    #k
    (parse_dsum_cases t pc pd)
    (serialize_dsum_cases t pc sc pd sd)
