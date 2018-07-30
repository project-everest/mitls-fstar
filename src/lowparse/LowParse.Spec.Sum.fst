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

let parse_tagged_union_eq
  (#kt: parser_kind)
  (#tag_t: Type0)
  (pt: parser kt tag_t)
  (#data_t: Type0)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (input: bytes)
: Lemma
  (parse (parse_tagged_union pt tag_of_data p) input == (match parse pt input with
  | None -> None
  | Some (tg, consumed_tg) ->
    let input_tg = Seq.slice input consumed_tg (Seq.length input) in
    begin match parse (p tg) input_tg with
    | Some (x, consumed_x) -> Some ((x <: data_t), consumed_tg + consumed_x)
    | None -> None
    end
  ))
= ()

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
let sum_key_type_of_sum_key (t: sum) (k: sum_key t) : Pure (sum_key_type t)
  (requires True)
  (ensures (fun k' -> k' == (k <: sum_key_type t)))
= k

inline_for_extraction
let sum_type (t: sum) : Tot Type0 =
  let (Sum _ _ _ data _) = t in
  data

inline_for_extraction
let sum_tag_of_data (t: sum) : Tot ((x: sum_type t) -> GTot (sum_key t)) =
  let (Sum _ _ _ _ tag_of_data) = t in
  tag_of_data

inline_for_extraction
let sum_cases (t: sum) (x: sum_key t) : Type0 =
  refine_with_tag #(sum_key t) #(sum_type t) (sum_tag_of_data t) x

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

let parse_sum_eq
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (input: bytes)
: Lemma
  (parse (parse_sum t p pc) input == (match parse (parse_enum_key p (sum_enum t)) input with
  | None -> None
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match parse (pc k) input_k with
    | None -> None
    | Some (x, consumed_x) -> Some ((x <: sum_type t), consumed_k + consumed_x)
    end
  ))
= parse_tagged_union_eq #(parse_filter_kind kt) #(sum_key t) (parse_enum_key p (sum_enum t)) #(sum_type t) (sum_tag_of_data t) #k pc input

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

inline_for_extraction
val synth_sum_with_nondep_case
  (nondep_part: Type0)
  (t: sum)
  (x: sum_key (make_sum_with_nondep nondep_part t))
  (d: nondep_part * sum_cases t (coerce' (sum_key t) x))
: Tot (sum_cases (make_sum_with_nondep nondep_part t) x)

let synth_sum_with_nondep_case nondep_part t x d
= match d with
  | (df, ds) -> 
    [@inline_let]
    let ds : sum_type t = ds in
    (df, ds)

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

let parse_sum_with_nondep_eq
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#knd: parser_kind)
  (#nondep_t: Type0)
  (pnd: parser knd nondep_t)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (input: bytes)
: Lemma
  (parse (parse_sum_with_nondep t p pnd pc) input == (match parse (parse_enum_key p (sum_enum t)) input with
  | Some (tg, consumed_tg) ->
    let input1 = Seq.slice input consumed_tg (Seq.length input) in
    begin match parse pnd input1 with
    | Some (nd, consumed_nd) ->
      let input2 = Seq.slice input1 consumed_nd (Seq.length input1) in
      begin match parse (pc tg) input2 with
      | Some (d, consumed_d) ->
        Some ((nd, d), consumed_tg + (consumed_nd + consumed_d))
      | _ -> None
    end
    | _ -> None
    end
  | _ -> None
  ))
= parse_sum_eq (make_sum_with_nondep nondep_t t) p (parse_sum_with_nondep_cases t pnd pc) input;
  match parse (parse_enum_key p (sum_enum t)) input with
  | Some (tg, consumed_tg) ->
    let input1 = Seq.slice input consumed_tg (Seq.length input) in
    parse_synth_eq (nondep_then pnd (pc tg)) (synth_sum_with_nondep_case _ t tg) input1;
    nondep_then_eq pnd (pc tg) input1
  | _ -> ()


(* Sum with default case *)

noeq
type dsum =
| DSum:
    (key: eqtype) ->
    (repr: eqtype) ->
    (e: enum key repr) ->
    (data: Type0) ->
    (tag_of_data: (data -> GTot (maybe_enum_key e))) ->
    dsum

inline_for_extraction
let dsum_key_type (t: dsum) : Tot eqtype =
  match t with (DSum key _ _ _ _) -> key

inline_for_extraction
let dsum_repr_type (t: dsum) : Tot eqtype =
  match t with (DSum _ repr _ _ _) -> repr

inline_for_extraction
let dsum_enum (t: dsum) : Tot (enum (dsum_key_type t) (dsum_repr_type t)) =
  match t with (DSum _ _ e _ _) -> e

inline_for_extraction
let dsum_key (t: dsum) : Tot Type0 =
  maybe_enum_key (dsum_enum t)

inline_for_extraction
let dsum_known_key (t: dsum) : Tot Type0 =
  enum_key (dsum_enum t)

inline_for_extraction
let dsum_unknown_key (t: dsum) : Tot Type0 =
  unknown_enum_repr (dsum_enum t)

inline_for_extraction
let dsum_type (t: dsum) : Tot Type0 =
  let (DSum _ _ _ data _) = t in
  data

inline_for_extraction
let dsum_tag_of_data (t: dsum) : Tot ((x: dsum_type t) -> GTot (dsum_key t)) =
  let (DSum _ _ _ _ tag_of_data) = t in
  tag_of_data

inline_for_extraction
let dsum_cases (t: dsum) (x: dsum_key t) : Type0 =
  refine_with_tag #(dsum_key t) #(dsum_type t) (dsum_tag_of_data t) x

let weaken_parse_dsum_cases_kind
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_cases s (Known x))))
  (k' : parser_kind)
: Tot parser_kind
= let keys : list (dsum_key_type s) = List.Tot.map fst (dsum_enum s) in
  glb_list_of #(dsum_key_type s) (fun (x: dsum_key_type s) ->
    if List.Tot.mem x keys
    then let (| k, _ |) = f x in k
    else k'
  ) (List.Tot.map fst (dsum_enum s)) `glb` k'

let parse_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_cases s (Known x))))
  (#k: parser_kind)
  (g: (x: dsum_unknown_key s) -> Tot (parser k (dsum_cases s (Unknown x))))
  (x: dsum_key s)
: Tot (parser (weaken_parse_dsum_cases_kind s f k) (dsum_cases s x))
= match x with
  | Known x ->  
    let (| _, p |) = f x in
    weaken (weaken_parse_dsum_cases_kind s f k) p
  | Unknown x ->
    weaken (weaken_parse_dsum_cases_kind s f k) (g x)

let parse_dsum
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
: Tot (parser (and_then_kind kt k) (dsum_type t))
= parse_tagged_union
    #kt
    #(dsum_key t)
    (parse_maybe_enum_key p (dsum_enum t))
    #(dsum_type t)
    (dsum_tag_of_data t)
    #k
    pc

let parse_dsum_eq
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (input: bytes)
: Lemma
  (parse (parse_dsum t p pc) input == (match parse (parse_maybe_enum_key p (dsum_enum t)) input with
  | None -> None
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match parse (pc k) input_k with
    | None -> None
    | Some (x, consumed_x) -> Some ((x <: dsum_type t), consumed_k + consumed_x)
    end
  ))
= parse_tagged_union_eq #(kt) #(dsum_key t) (parse_maybe_enum_key p (dsum_enum t)) #(dsum_type t) (dsum_tag_of_data t) #k pc input

let serialize_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_cases s (Known x))))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))  
  (#k: parser_kind)
  (g: (x: dsum_unknown_key s) -> Tot (parser k (dsum_cases s (Unknown x))))
  (sg: (x: dsum_unknown_key s) -> Tot (serializer (g x)))
  (x: dsum_key s)
: Tot (serializer (parse_dsum_cases s f g x))
= match x with
  | Known x ->
    serialize_ext
      (dsnd (f x))
      (sr x)
      (parse_dsum_cases s f g (Known x))
  | Unknown x ->
    serialize_ext
      (g x)
      (sg x)
      (parse_dsum_cases s f g (Unknown x))

let serialize_dsum
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
: Pure (serializer (parse_dsum t p pc))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_tagged_union
    #(kt)
    #(dsum_key t)
    #(parse_maybe_enum_key p (dsum_enum t))
    (serialize_maybe_enum_key p s (dsum_enum t))
    #(dsum_type t)
    (dsum_tag_of_data t)
    #k
    #pc
    sc

inline_for_extraction
let make_dsum
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type0)
  (tag_of_data: (data -> GTot (maybe_enum_key e)))
: Tot dsum
= DSum key repr e data tag_of_data
