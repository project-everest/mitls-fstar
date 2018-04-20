module LowParse.Spec.Sum
include LowParse.Spec.Enum

module Seq = FStar.Seq

inline_for_extraction
let refine_with_tag (#tag_t: Type0) (#data_t: Type0) (tag_of_data: (data_t -> GTot tag_t)) (x: tag_t) : Tot Type0 =
  (y: data_t { tag_of_data y == x } )

inline_for_extraction
let synth_tagged_union_data
  (#tag_t: Type0)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (tg: tag_t)
  (x: refine_with_tag tag_of_data tg)
: Tot data_t
= x

val parse_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type0)
  (pt: parser kt tag_t)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
: Tot (parser (and_then_kind kt k) data_t)

#set-options "--z3rlimit 16"
let parse_tagged_union #kt #tag_t pt #data_t tag_of_data #k p =
  pt `and_then` (fun (tg: tag_t) ->
    parse_synth #k #(refine_with_tag tag_of_data tg) (p tg) (synth_tagged_union_data tag_of_data tg)
  )
#reset-options

let bare_serialize_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type0)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Tot (bare_serializer data_t)
= fun (d: data_t) ->
  let tg = tag_of_data d in
  Seq.append (st tg) (serialize (s tg) d)

#set-options "--z3rlimit 16"

let bare_serialize_tagged_union_correct
  (#kt: parser_kind)
  (#tag_t: Type0)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (serializer_correct (parse_tagged_union pt tag_of_data p) (bare_serialize_tagged_union st tag_of_data s)))
= (* same proof as nondep_then *)
  let prf
    (x: data_t)
  : Lemma (parse (parse_tagged_union pt tag_of_data p) (bare_serialize_tagged_union st tag_of_data s x) == Some (x, Seq.length (bare_serialize_tagged_union  st tag_of_data s x)))
  = let t = tag_of_data x in
    let (u: refine_with_tag tag_of_data t) = x in
    let v1' = parse pt (bare_serialize_tagged_union st tag_of_data s x) in
    let v1 = parse pt (st t) in
    assert (Some? v1);
    assert (no_lookahead_on pt (st t) (bare_serialize_tagged_union st tag_of_data s x));
    let (Some (_, len')) = parse pt (st t) in
    assert (len' == Seq.length (st t));
    assert (len' <= Seq.length (bare_serialize_tagged_union st tag_of_data s x));
    assert (Seq.slice (st t) 0 len' == st t);
    seq_slice_append_l (st t) (serialize (s t) u);
    assert (no_lookahead_on_precond pt (st t) (bare_serialize_tagged_union st tag_of_data s x));
    assert (no_lookahead_on_postcond pt (st t) (bare_serialize_tagged_union st tag_of_data s x));
    assert (Some? v1');
    assert (injective_precond pt (st t) (bare_serialize_tagged_union st tag_of_data s x));
    assert (injective_postcond pt (st t) (bare_serialize_tagged_union st tag_of_data s x));
    let (Some (x1, len1)) = v1 in
    let (Some (x1', len1')) = v1' in
    assert (x1 == x1');
    assert ((len1 <: nat) == (len1' <: nat));
    assert (x1 == t);
    assert (len1 == Seq.length (st t));
    assert (bare_serialize_tagged_union st tag_of_data s x == Seq.append (st t) (serialize (s t) u));
    seq_slice_append_r (st t) (serialize (s t) u);
    ()
  in
  Classical.forall_intro prf

#reset-options

let serialize_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type0)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Pure (serializer (parse_tagged_union pt tag_of_data p))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= bare_serialize_tagged_union_correct st tag_of_data s;
  bare_serialize_tagged_union st tag_of_data s

noeq
type sum =
| Sum:
    (key: eqtype) ->
    (repr: eqtype) ->
    (e: enum key repr) ->
    (data: Type0) ->
    (tag_of_data: (data -> GTot (enum_key e))) ->
    sum

inline_for_extraction
let sum_key_type (t: sum) : Tot eqtype =
  match t with (Sum key _ _ _ _) -> key

inline_for_extraction
let sum_repr_type (t: sum) : Tot eqtype =
  match t with (Sum _ repr _ _ _) -> repr

inline_for_extraction
let sum_enum (t: sum) : Tot (enum (sum_key_type t) (sum_repr_type t)) =
  match t with (Sum _ _ e _ _) -> e

inline_for_extraction
let sum_key (t: sum) : Tot Type0 =
  enum_key (sum_enum t)

inline_for_extraction
let sum_cases (t: sum) : Tot ((x: sum_key t) -> Tot Type0) =
  let (Sum _ _ _ _ tag_of_data) = t in
  (fun x -> refine_with_tag tag_of_data x)

inline_for_extraction
let sum_type (t: sum) : Tot Type0 =
  let (Sum _ _ _ data _) = t in
  data

inline_for_extraction
let sum_tag_of_data (t: sum) : Tot ((x: sum_type t) -> GTot (sum_key t)) =
  let (Sum _ _ _ _ tag_of_data) = t in
  tag_of_data

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
    (parse_enum_key p (sum_enum t))
    #(sum_type t)
    (sum_tag_of_data t)
    #k
    pc

let serialize_sum_cases
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_cases s x)))
  (sr: (x: sum_key s) -> Tot (serializer (dsnd (f x))))
  (x: sum_key s)
: Tot (serializer (parse_sum_cases s f x))
= serialize_ext
    (dsnd (f x))
    (sr x)
    (parse_sum_cases s f x)

let serialize_sum
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (pc x))))
: Pure (serializer (parse_sum t p pc))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_tagged_union
    #(parse_filter_kind kt)
    #(sum_key t)
    #(parse_enum_key p (sum_enum t))
    (serialize_enum_key p s (sum_enum t))
    #(sum_type t)
    (sum_tag_of_data t)
    #k
    #pc
    sc

inline_for_extraction
let make_sum
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type0)
  (tag_of_data: (data -> GTot (enum_key e)))
: Tot sum
= Sum key repr e data tag_of_data

(* Sum with a common non-dependent prefix (i.e. the input buffer is to be split in 3 parts: 1/ tag, 2/ non-dependent data, 3/ dependent data
   We specify it as a special case, but it will have its own separate implementation *)

let tag_of_data_with_nondep
  (nondep_t: Type0)
  (#tag_t: Type0)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (data_with_nondep: (nondep_t * data_t))
: GTot tag_t
= match data_with_nondep with
  | (_, data) -> tag_of_data data

inline_for_extraction
let make_sum_with_nondep
  (nondep_part: Type0)
  (s: sum)
= Sum (sum_key_type s) (sum_repr_type s) (sum_enum s) (nondep_part * sum_type s) (tag_of_data_with_nondep nondep_part (sum_tag_of_data s))

#set-options "--use_two_phase_tc false"

inline_for_extraction
val synth_sum_with_nondep_case
  (nondep_part: Type0)
  (t: sum)
  (x: sum_key (make_sum_with_nondep nondep_part t))
  (d: nondep_part * sum_cases t (let x : sum_key_type t = x in x))
: Tot (sum_cases (make_sum_with_nondep nondep_part t) (let x : sum_key_type t = x in x))

let synth_sum_with_nondep_case nondep_part t x d
= match d with
  | (df, ds) -> 
    [@inline_let]
    let ds : sum_type t = ds in
    (df, ds)

#reset-options

let parse_sum_with_nondep_cases
  (#nondep_part: Type0)
  (t: sum)
  (#knd: parser_kind)
  (pnd: parser knd nondep_part)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (x: sum_key (make_sum_with_nondep nondep_part t))
: Tot (parser _ (sum_cases (make_sum_with_nondep nondep_part t) x))
= let (x' : sum_key t) = (x <: sum_key_type t) in
  (pnd `nondep_then` (pc x')) `parse_synth` (synth_sum_with_nondep_case nondep_part t x)

let parse_sum_with_nondep
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#knd: parser_kind)
  (#nondep_t: Type0)
  (pnd: parser knd nondep_t)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: Tot (parser _ (sum_type (make_sum_with_nondep nondep_t t)))
= parse_sum (make_sum_with_nondep nondep_t t) p (parse_sum_with_nondep_cases t pnd pc)

(* Sum with default case *)

inline_for_extraction
let dsum = (sum * Type0)

type maybe_data (known_data: Type0) (unknown_repr: eqtype) (unknown_data: Type0) =
  | KnownData : (d: known_data) -> maybe_data known_data unknown_repr unknown_data
  | UnknownData : (r: unknown_repr) -> (d: unknown_data) -> maybe_data known_data unknown_repr unknown_data

inline_for_extraction
let sum_of_dsum
  (d: dsum)
: Tot sum
= let (s, _) = d in s

inline_for_extraction
let dsum_key (t: dsum) : Tot Type0 =
  maybe_enum_key (sum_enum (sum_of_dsum t))

inline_for_extraction
let dsum_unknown_type
  (t: dsum)
: Tot Type0
= let (_, ud) = t in
  ud

inline_for_extraction
let dsum_type
  (t: dsum)
: Tot Type0
= maybe_data
    (sum_type (sum_of_dsum t)) 
    (unknown_enum_repr (sum_enum (sum_of_dsum t)))
    (dsum_unknown_type t)

inline_for_extraction
let dsum_tag_of_data
  (d: dsum)
  (data: dsum_type d)
: GTot (dsum_key d)
= match data with
  | KnownData kd -> Known (sum_tag_of_data (sum_of_dsum d) kd)
  | UnknownData r _ -> Unknown r

inline_for_extraction
let synth_dsum_known
  (d: dsum)
  (kt: sum_key (sum_of_dsum d))
  (d' : sum_cases (sum_of_dsum d) kt)
: Tot (refine_with_tag (dsum_tag_of_data d) (Known kt))
= (KnownData d' <: dsum_type d)

inline_for_extraction
let synth_dsum_unknown
  (d: dsum)
  (r: unknown_enum_repr (sum_enum (sum_of_dsum d)))
  (d' : dsum_unknown_type d)
: Tot (refine_with_tag (dsum_tag_of_data d) (Unknown r))
= (UnknownData r d' <: dsum_type d)

let parse_dsum_cases
  (d: dsum)
  (#k: parser_kind)
  (pk: ((kt: sum_key (sum_of_dsum d)) -> Tot (parser k (sum_cases (sum_of_dsum d) kt))))
  (pu: parser k (dsum_unknown_type d))
  (t: dsum_key d)
: Tot (parser k (refine_with_tag (dsum_tag_of_data d) t))
= match t with
  | Known kt ->
    parse_synth (pk kt) (synth_dsum_known d kt)
  | Unknown r ->
    parse_synth pu (synth_dsum_unknown d r)

let parse_dsum
  (d: dsum)
  (#tk: parser_kind)
  (tp: parser tk (sum_repr_type (sum_of_dsum d)))
  (#k: parser_kind)
  (pk: ((kt: sum_key (sum_of_dsum d)) -> Tot (parser k (sum_cases (sum_of_dsum d) kt))))
  (pu: parser k (dsum_unknown_type d))
: Tot (parser (and_then_kind tk k) (dsum_type d))
= parse_tagged_union
    #tk
    #(dsum_key d)
    (parse_maybe_enum_key tp (sum_enum (sum_of_dsum d)))
    #(dsum_type d)
    (dsum_tag_of_data d)
    #k
    (parse_dsum_cases d pk pu)

inline_for_extraction
let synth_dsum_known_recip
  (d: dsum)
  (kt: sum_key (sum_of_dsum d))
  (d' : refine_with_tag (dsum_tag_of_data d) (Known kt))
: Tot (sum_cases (sum_of_dsum d) kt)
= let (KnownData d_) = (d' <: dsum_type d) in d_

inline_for_extraction
let synth_dsum_unknown_recip
  (d: dsum)
  (r: unknown_enum_repr (sum_enum (sum_of_dsum d)))
  (d' : refine_with_tag (dsum_tag_of_data d) (Unknown r)) 
: Tot (dsum_unknown_type d)
= let (UnknownData r d_) = (d' <: dsum_type d) in d_

let serialize_dsum_cases
  (d: dsum)
  (#k: parser_kind)
  (#pk: ((kt: sum_key (sum_of_dsum d)) -> Tot (parser k (sum_cases (sum_of_dsum d) kt))))
  (sk: ((kt: sum_key (sum_of_dsum d)) -> Tot (serializer (pk kt))))
  (#pu: parser k (dsum_unknown_type d))
  (su: serializer pu)
  (t: dsum_key d)
: Tot (serializer (parse_dsum_cases d pk pu t))
= match t with
  | Known kt ->
    serialize_synth
      _
      (synth_dsum_known d kt)
      (sk kt)
      (synth_dsum_known_recip d kt)
      ()
  | Unknown r ->
    serialize_synth
      _
      (synth_dsum_unknown d r)
      su
      (synth_dsum_unknown_recip d r)
      ()

let serialize_dsum
  (d: dsum)
  (#tk: parser_kind)
  (#tp: parser tk (sum_repr_type (sum_of_dsum d)))
  (ts: serializer tp)
  (#k: parser_kind)
  (#pk: ((kt: sum_key (sum_of_dsum d)) -> Tot (parser k (sum_cases (sum_of_dsum d) kt))))
  (sk: ((kt: sum_key (sum_of_dsum d)) -> Tot (serializer (pk kt))))
  (#pu: parser k (dsum_unknown_type d))
  (su: serializer pu)
: Pure (serializer (parse_dsum d tp pk pu))
  (requires (tk.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_tagged_union
    #tk
    #(dsum_key d)
    #(parse_maybe_enum_key tp (sum_enum (sum_of_dsum d)))
    (serialize_maybe_enum_key _ ts (sum_enum (sum_of_dsum d)))
    #(dsum_type d)
    (dsum_tag_of_data d)
    #k
    #(parse_dsum_cases d pk pu)
    (serialize_dsum_cases d sk su)
