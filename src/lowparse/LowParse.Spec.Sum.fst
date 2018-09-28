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
    (tag_of_data: (data -> Tot (enum_key e))) ->
    (type_of_tag: (enum_key e -> Tot Type0)) ->
    (synth_case: ((x: enum_key e) -> (y: type_of_tag x) -> Tot (refine_with_tag tag_of_data x))) ->
    (synth_case_recip: ((x: data) -> Tot (type_of_tag (tag_of_data x)))) ->
    (synth_case_recip_synth_case: (
      (x: enum_key e) ->
      (y: type_of_tag x) ->
      Lemma
      (synth_case_recip (synth_case x y) == y)
    )) ->
    (synth_case_synth_case_recip: (
      (x: data) ->
      Lemma
      (synth_case (tag_of_data x) (synth_case_recip x) == x)
    )) ->
    sum

inline_for_extraction
let sum_key_type (t: sum) : Tot eqtype =
  match t with (Sum key _ _ _ _ _ _ _ _ _) -> key

inline_for_extraction
let sum_repr_type (t: sum) : Tot eqtype =
  match t with (Sum _ repr _ _ _ _ _ _ _ _) -> repr

inline_for_extraction
let sum_enum (t: sum) : Tot (enum (sum_key_type t) (sum_repr_type t)) =
  match t with (Sum _ _ e _ _ _ _ _ _ _) -> e

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
  let (Sum _ _ _ data _ _ _ _ _ _) = t in
  data

inline_for_extraction
let sum_tag_of_data (t: sum) : Tot ((x: sum_type t) -> Tot (sum_key t)) =
  match t with
  | Sum _ _ _ _ tag_of_data _ _ _ _ _ -> tag_of_data

inline_for_extraction
let sum_cases (t: sum) (x: sum_key t) : Type0 =
  refine_with_tag #(sum_key t) #(sum_type t) (sum_tag_of_data t) x

inline_for_extraction
let sum_type_of_tag (t: sum) : (x: sum_key t) -> Type =
  let (Sum _ _ _ _ _ type_of_tag _ _ _ _) = t in
  type_of_tag

let weaken_parse_cases_kind
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
: Tot parser_kind
= let keys : list (sum_key_type s) = List.Tot.map fst (sum_enum s) in
  glb_list_of #(sum_key_type s) (fun (x: sum_key_type s) ->
    if List.Tot.mem x keys
    then let (| k, _ |) = f x in k
    else default_parser_kind
  ) (List.Tot.map fst (sum_enum s))

inline_for_extraction
let synth_sum_case (s: sum) : (k: sum_key s) -> (x: sum_type_of_tag s k) -> Tot (sum_cases s k) =
  match s with
  | Sum _ _ _ _ _ _ synth_case _ _ _ -> synth_case

let synth_sum_case_injective (s: sum) (k: sum_key s) : Lemma
  (synth_injective (synth_sum_case s k))
= Classical.forall_intro (Sum?.synth_case_recip_synth_case s k)

let parse_sum_cases
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
  (x: sum_key s)
: Tot (parser (weaken_parse_cases_kind s f) (sum_cases s x))
= let (| _, p |) = f x in
  synth_sum_case_injective s x;
  weaken (weaken_parse_cases_kind s f) p `parse_synth` (synth_sum_case s x)

let parse_sum'
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

inline_for_extraction
let parse_sum_kind
  (kt: parser_kind)
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
: Tot parser_kind
= and_then_kind (parse_filter_kind kt) (weaken_parse_cases_kind t pc)

let parse_sum
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
: Tot (parser (parse_sum_kind kt t pc) (sum_type t))
= parse_sum' t p (parse_sum_cases t pc)

#set-options "--z3rlimit 16"

let parse_sum_eq'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (input: bytes)
: Lemma
  (parse (parse_sum t p pc) input == (match parse (parse_enum_key p (sum_enum t)) input with
  | None -> None
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    synth_sum_case_injective t k;
    begin match parse (parse_synth (dsnd (pc k)) (synth_sum_case t k)) input_k with
    | None -> None
    | Some (x, consumed_x) -> Some ((x <: sum_type t), consumed_k + consumed_x)
    end
  ))
= parse_tagged_union_eq #(parse_filter_kind kt) #(sum_key t) (parse_enum_key p (sum_enum t)) #(sum_type t) (sum_tag_of_data t) (parse_sum_cases t pc) input

#reset-options

let parse_sum_eq
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (input: bytes)
: Lemma
  (parse (parse_sum t p pc) input == (match parse (parse_enum_key p (sum_enum t)) input with
  | None -> None
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match parse (dsnd (pc k)) input_k with
    | None -> None
    | Some (x, consumed_x) -> Some ((synth_sum_case t k x <: sum_type t), consumed_k + consumed_x)
    end
  ))
= parse_tagged_union_eq #(parse_filter_kind kt) #(sum_key t) (parse_enum_key p (sum_enum t)) #(sum_type t) (sum_tag_of_data t) (parse_sum_cases t pc) input;
  match parse (parse_enum_key p (sum_enum t)) input with
  | None -> ()
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    synth_sum_case_injective t k;
    parse_synth_eq (dsnd (pc k)) (synth_sum_case t k) input_k

inline_for_extraction
let synth_sum_case_recip (s: sum) (k: sum_key s) (x: sum_cases s k) : Tot (sum_type_of_tag s k) =
  match s with (Sum _ _ _ _ _ _ _ synth_case_recip _ _) ->
  synth_case_recip x

let synth_sum_case_inverse (s: sum) (k: sum_key s) : Lemma
  (synth_inverse (synth_sum_case s k) (synth_sum_case_recip s k))
= Classical.forall_intro (Sum?.synth_case_synth_case_recip s)

let serialize_sum_cases
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_type_of_tag s x)))
  (sr: (x: sum_key s) -> Tot (serializer (dsnd (f x))))
  (x: sum_key s)
: Tot (serializer (parse_sum_cases s f x))
= synth_sum_case_injective s x;
  synth_sum_case_inverse s x;
  serialize_ext
    (dsnd (f x) `parse_synth` (synth_sum_case s x))
    (serialize_synth
      _
      (synth_sum_case s x)
      (sr x)
      (synth_sum_case_recip s x)
      ()
    )
    (parse_sum_cases s f x)

let serialize_sum'
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (pc x))))
: Pure (serializer (parse_sum' t p pc))
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

let serialize_sum
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
: Pure (serializer (parse_sum t p pc))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= // FIXME: WHY WHY WHY is implicit argument inference failing here? (i.e. introducing an eta-expansion)
  serialize_sum' t s #_ #(parse_sum_cases t pc) (serialize_sum_cases t pc sc)

#set-options "--z3rlimit 32"

let serialize_sum_eq
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (s: serializer p)
  (#pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (sc: ((x: sum_key t) -> Tot (serializer (dsnd (pc x)))))
  (x: sum_type t)
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (
    serialize (serialize_sum t s sc) x == (
    let tg = sum_tag_of_data t x in
    serialize (serialize_enum_key _ s (sum_enum t)) tg `Seq.append`
    serialize (sc tg) (synth_sum_case_recip t tg x)
  )))
= ()

#reset-options

inline_for_extraction
let make_sum
  (#key #repr: eqtype)
  (e: enum key repr)
  (#data: Type0)
  (tag_of_data: (data -> Tot (enum_key e)))
: Tot (
    (type_of_tag: (enum_key e -> Tot Type0)) ->
    (synth_case: ((x: enum_key e) -> (y: type_of_tag x) -> Tot (refine_with_tag tag_of_data x))) ->
    (synth_case_recip: ((x: data) -> Tot (type_of_tag (tag_of_data x)))) ->
    (synth_case_recip_synth_case: (
      (x: enum_key e) ->
      (y: type_of_tag x) ->
      Lemma
      (synth_case_recip (synth_case x y) == y)
    )) ->
    (synth_case_synth_case_recip: (
      (x: data) ->
      Lemma
      (synth_case (tag_of_data x) (synth_case_recip x) == x)
    )) ->
  Tot sum)
= Sum key repr e data tag_of_data

(* Sum with default case *)

inline_for_extraction
let dsum_type_of_tag'
  (#key: eqtype)
  (#repr: eqtype)
  (e: total_enum key repr)
  (type_of_known_tag: (key -> Tot Type0))
  (type_of_unknown_tag: Type0)
  (k: maybe_total_enum_key e)
: Type0
= match k with
  | TotalUnknown _ -> type_of_unknown_tag
  | TotalKnown k -> type_of_known_tag k

let synth_dsum_case'
  (#key: eqtype)
  (#repr: eqtype)
  (e: total_enum key repr)
  (#data: Type0)
  (tag_of_data: (data -> GTot (maybe_total_enum_key e)))
  (type_of_known_tag: (key -> Tot Type0))
  (type_of_unknown_tag: Type0)
  (synth_known_case: ((x: key) -> (y: type_of_known_tag x) -> Tot (refine_with_tag tag_of_data (TotalKnown x))))
  (synth_unknown_case: ((x: unknown_enum_repr e) -> type_of_unknown_tag -> Tot (refine_with_tag tag_of_data (TotalUnknown x))))
  (xy: (x: maybe_total_enum_key e & dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x))
: GTot data
= let (| x, y |) = xy in
  match x with
  | TotalUnknown x -> synth_unknown_case x y
  | TotalKnown x -> synth_known_case x y

let synth_dsum_case_recip'
  (#key: eqtype)
  (#repr: eqtype)
  (e: total_enum key repr)
  (#data: Type0)
  (tag_of_data: (data -> GTot (maybe_total_enum_key e)))
  (type_of_known_tag: (key -> Tot Type0))
  (type_of_unknown_tag: Type0)
  (synth_case_recip: ((x: data) -> Tot (dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag (tag_of_data x))))
  (y: data)
: GTot (x: maybe_total_enum_key e & dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x)
= (| tag_of_data y, synth_case_recip y |)

noeq
type dsum =
| DSum:
    (key: eqtype) ->
    (repr: eqtype) ->
    (e: total_enum key repr) ->
    (data: Type0) ->
    (tag_of_data: (data -> Tot (maybe_total_enum_key e))) ->
    (type_of_known_tag: (key -> Tot Type0)) ->
    (type_of_unknown_tag: Type0) ->
    (synth_known_case: ((x: key) -> (y: type_of_known_tag x) -> Tot (refine_with_tag tag_of_data (TotalKnown x)))) ->
    (synth_unknown_case: ((x: unknown_enum_repr e) -> type_of_unknown_tag -> Tot (refine_with_tag tag_of_data (TotalUnknown x)))) ->
    (synth_case_recip: ((x: data) -> Tot (dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag (tag_of_data x)))) ->
    (synth_case_recip_synth_case: (
      (xy: (x: maybe_total_enum_key e & dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x)) ->
      Tot (squash
      (synth_dsum_case_recip' e tag_of_data type_of_known_tag type_of_unknown_tag synth_case_recip
        (synth_dsum_case' e tag_of_data type_of_known_tag type_of_unknown_tag synth_known_case synth_unknown_case xy) == xy))
    )) ->
    (synth_case_synth_case_recip: (
      (x: data) ->
      Tot (squash
      (synth_dsum_case' e tag_of_data type_of_known_tag type_of_unknown_tag synth_known_case synth_unknown_case
        (synth_dsum_case_recip' e tag_of_data type_of_known_tag type_of_unknown_tag synth_case_recip x) == x))
    )) ->
    dsum

inline_for_extraction
let dsum_key_type (t: dsum) : Tot eqtype =
  match t with (DSum key _ _ _ _ _ _ _ _ _ _ _) -> key

inline_for_extraction
let dsum_repr_type (t: dsum) : Tot eqtype =
  match t with (DSum _ repr _ _ _ _ _ _ _ _ _ _) -> repr

inline_for_extraction
let dsum_enum (t: dsum) : Tot (total_enum (dsum_key_type t) (dsum_repr_type t)) =
  match t with (DSum _ _ e _ _ _ _ _ _ _ _ _) -> e

inline_for_extraction
let dsum_key (t: dsum) : Tot Type0 =
  maybe_total_enum_key (dsum_enum t)

inline_for_extraction
let dsum_known_key (t: dsum) : Tot Type0 =
  dsum_key_type t

inline_for_extraction
let dsum_unknown_key (t: dsum) : Tot Type0 =
  unknown_enum_repr (dsum_enum t)

inline_for_extraction
let dsum_type (t: dsum) : Tot Type0 =
  let (DSum _ _ _ data _ _ _ _ _ _ _ _) = t in
  data

inline_for_extraction
let dsum_tag_of_data (t: dsum) : Tot ((x: dsum_type t) -> Tot (dsum_key t)) =
  match t with (DSum _ _ _ _ tag_of_data _ _ _ _ _ _ _) -> tag_of_data

inline_for_extraction
let dsum_cases (t: dsum) (x: dsum_key t) : Type0 =
  refine_with_tag #(dsum_key t) #(dsum_type t) (dsum_tag_of_data t) x

inline_for_extraction
let dsum_type_of_known_tag (t: dsum) : Tot ((k: dsum_known_key t) -> Tot Type0) =
  let (DSum _ _ _ _ _ type_of_known_tag _ _ _ _ _ _) = t in
  type_of_known_tag

inline_for_extraction
let dsum_type_of_unknown_tag (t: dsum) : Tot Type0 =
  let (DSum _ _ _ _ _ _ type_of_unknown_tag _ _ _ _ _) = t in
  type_of_unknown_tag

let weaken_parse_dsum_cases_kind
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (k' : parser_kind)
: Tot parser_kind
= let keys : list (dsum_key_type s) = List.Tot.map fst (dsum_enum s) in
  glb_list_of #(dsum_key_type s) (fun (x: dsum_key_type s) ->
    if List.Tot.mem x keys
    then let (| k, _ |) = f x in k
    else k'
  ) (List.Tot.map fst (dsum_enum s)) `glb` k'

let weaken_parse_dsum_cases_kind'
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k' : parser_kind)
  (p: parser k' (dsum_type_of_unknown_tag s))
: Tot parser_kind
= weaken_parse_dsum_cases_kind s f k'

inline_for_extraction
let synth_dsum_known_case
  (s: dsum)
: Tot ((x: dsum_known_key s) -> dsum_type_of_known_tag s x -> Tot (refine_with_tag (dsum_tag_of_data s) (TotalKnown x)))
= match s with DSum _ _ _ _ _ _ _ synth_known_case _ _ _ _ -> synth_known_case

let synth_dsum_known_case_injective
  (s: dsum)
  (x: dsum_known_key s)
: Lemma
  (synth_injective (synth_dsum_known_case s x))
= let f
    (y1: dsum_type_of_known_tag s x)
    (y2: dsum_type_of_known_tag s x)
  : Lemma
    (requires (synth_dsum_known_case s x y1 == synth_dsum_known_case s x y2))
    (ensures (y1 == y2))
  = DSum?.synth_case_recip_synth_case s (| TotalKnown x, y1 |);
    DSum?.synth_case_recip_synth_case s (| TotalKnown x, y2 |)
  in
  let g
    (y1: dsum_type_of_known_tag s x)
    (y2: dsum_type_of_known_tag s x)
  : Lemma
    (synth_dsum_known_case s x y1 == synth_dsum_known_case s x y2 ==> y1 == y2)
  = Classical.move_requires (f y1) y2
  in
  Classical.forall_intro_2 g

inline_for_extraction
let synth_dsum_unknown_case
  (s: dsum)
: Tot ((x: dsum_unknown_key s) -> dsum_type_of_unknown_tag s -> Tot (refine_with_tag (dsum_tag_of_data s) (TotalUnknown x)))
= match s with DSum _ _ _ _ _ _ _ _ synth_unknown_case _ _ _ -> synth_unknown_case

let synth_dsum_unknown_case_injective
  (s: dsum)
  (x: dsum_unknown_key s)
: Lemma
  (synth_injective (synth_dsum_unknown_case s x))
= let f
    (y1: dsum_type_of_unknown_tag s)
    (y2: dsum_type_of_unknown_tag s)
  : Lemma
    (requires (synth_dsum_unknown_case s x y1 == synth_dsum_unknown_case s x y2))
    (ensures (y1 == y2))
  = DSum?.synth_case_recip_synth_case s (| TotalUnknown x, y1 |);
    DSum?.synth_case_recip_synth_case s (| TotalUnknown x, y2 |)
  in
  let g
    (y1: dsum_type_of_unknown_tag s)
    (y2: dsum_type_of_unknown_tag s)
  : Lemma
    (synth_dsum_unknown_case s x y1 == synth_dsum_unknown_case s x y2 ==> y1 == y2)
  = Classical.move_requires (f y1) y2
  in
  Classical.forall_intro_2 g

let parse_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (x: dsum_key s)
: Tot (parser (weaken_parse_dsum_cases_kind s f k) (dsum_cases s x))
= match x with
  | TotalKnown x ->  
    let (| _, p |) = f x in
    synth_dsum_known_case_injective s x;
    weaken (weaken_parse_dsum_cases_kind s f k) p `parse_synth` synth_dsum_known_case s x
  | TotalUnknown x ->
    synth_dsum_unknown_case_injective s x;
    weaken (weaken_parse_dsum_cases_kind s f k) g `parse_synth` synth_dsum_unknown_case s x

let parse_dsum'
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
: Tot (parser (and_then_kind kt k) (dsum_type t))
= parse_tagged_union
    #kt
    #(dsum_key t)
    (parse_maybe_total_enum_key p (dsum_enum t))
    #(dsum_type t)
    (dsum_tag_of_data t)
    #k
    pc

inline_for_extraction
let parse_dsum_kind
  (kt: parser_kind)
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (k: parser_kind)
: Tot parser_kind
= and_then_kind kt (weaken_parse_dsum_cases_kind s f k)

let parse_dsum
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag t))
: Tot (parser (parse_dsum_kind kt t f k) (dsum_type t))
= parse_dsum' t p (parse_dsum_cases t f g)

#set-options "--z3rlimit 32"

let parse_dsum_eq'
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (input: bytes)
: Lemma
  (parse (parse_dsum t p f g) input == (match parse p input with
  | None -> None
  | Some (k', consumed_k) ->
    let k = maybe_total_enum_key_of_repr (dsum_enum t) k' in
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match k with
    | TotalKnown k ->
      synth_dsum_known_case_injective t k;
      begin match parse (dsnd (f k) `parse_synth` synth_dsum_known_case t k) input_k with
      | None -> None
      | Some (x, consumed_x) -> Some ((x <: dsum_type t), consumed_k + consumed_x)
      end
    | TotalUnknown k ->
      synth_dsum_unknown_case_injective t k;
      begin match parse (g `parse_synth` synth_dsum_unknown_case t k) input_k with
      | None -> None
      | Some (x, consumed_x) -> Some ((x <: dsum_type t), consumed_k + consumed_x)
      end
    end
  ))
= parse_tagged_union_eq #(kt) #(dsum_key t) (parse_maybe_total_enum_key p (dsum_enum t)) #(dsum_type t) (dsum_tag_of_data t) (parse_dsum_cases t f g) input;
  parse_synth_eq p (maybe_total_enum_key_of_repr (dsum_enum t)) input

let parse_dsum_eq
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (dsum_repr_type t))
  (f: (x: dsum_known_key t) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag t x)))
  (#k': parser_kind)
  (g: parser k' (dsum_type_of_unknown_tag t))
  (input: bytes)
: Lemma
  (parse (parse_dsum t p f g) input == (match parse (parse_maybe_total_enum_key p (dsum_enum t)) input with
  | None -> None
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match k with
    | TotalKnown k ->
      begin match parse (dsnd (f k)) input_k with
      | None -> None
      | Some (x, consumed_x) -> Some ((synth_dsum_known_case t k x <: dsum_type t), consumed_k + consumed_x)
      end
    | TotalUnknown k ->
      begin match parse g input_k with
      | None -> None
      | Some (x, consumed_x) -> Some ((synth_dsum_unknown_case t k x <: dsum_type t), consumed_k + consumed_x)
      end
    end
  ))
= parse_tagged_union_eq #(kt) #(dsum_key t) (parse_maybe_total_enum_key p (dsum_enum t)) #(dsum_type t) (dsum_tag_of_data t) (parse_dsum_cases t f g) input;
  let j = parse (parse_maybe_total_enum_key p (dsum_enum t)) input in
  match j with
  | None -> ()
  | Some (k, consumed_k) ->
    let input_k = Seq.slice input consumed_k (Seq.length input) in
    begin match k with
    | TotalKnown k ->
      synth_dsum_known_case_injective t k;
      parse_synth_eq (weaken (weaken_parse_dsum_cases_kind t f k') (dsnd (f k))) (synth_dsum_known_case t k) input_k
    | TotalUnknown k ->
      synth_dsum_unknown_case_injective t k;
      parse_synth_eq (weaken (weaken_parse_dsum_cases_kind t f k') g) (synth_dsum_unknown_case t k) input_k
    end

#reset-options

inline_for_extraction
let dsum_type_of_tag
  (t: dsum)
  (k: dsum_key t)
: Tot Type0
= dsum_type_of_tag' (dsum_enum t) (dsum_type_of_known_tag t) (dsum_type_of_unknown_tag t) k

inline_for_extraction
let synth_dsum_case_recip
  (t: dsum)
  (x: dsum_type t)
: Tot (dsum_type_of_tag t (dsum_tag_of_data t x))
= let (DSum _ _ _ _ _ _ _ _ _ synth_case_recip _ _) = t in
  synth_case_recip x

inline_for_extraction
let synth_dsum_known_case_recip
  (t: dsum)
  (k: dsum_known_key t)
  (x: refine_with_tag (dsum_tag_of_data t) (TotalKnown k))
: Tot (dsum_type_of_known_tag t k)
= synth_dsum_case_recip t x

let synth_dsum_known_case_inverse
  (s: dsum)
  (x: dsum_known_key s)
: Lemma
  (synth_inverse (synth_dsum_known_case s x) (synth_dsum_known_case_recip s x))
= let f
    (y: refine_with_tag (dsum_tag_of_data s) (TotalKnown x))
  : Lemma
    (synth_dsum_known_case s x (synth_dsum_known_case_recip s x y) == y)
  = DSum?.synth_case_synth_case_recip s y
  in
  Classical.forall_intro f

inline_for_extraction
let synth_dsum_unknown_case_recip
  (t: dsum)
  (k: dsum_unknown_key t)
  (x: refine_with_tag (dsum_tag_of_data t) (TotalUnknown k))
: Tot (dsum_type_of_unknown_tag t)
= synth_dsum_case_recip t x

let synth_dsum_unknown_case_inverse
  (s: dsum)
  (x: dsum_unknown_key s)
: Lemma
  (synth_inverse (synth_dsum_unknown_case s x) (synth_dsum_unknown_case_recip s x))
= let f
    (y: refine_with_tag (dsum_tag_of_data s) (TotalUnknown x))
  : Lemma
    (synth_dsum_unknown_case s x (synth_dsum_unknown_case_recip s x y) == y)
  = DSum?.synth_case_synth_case_recip s y
  in
  Classical.forall_intro f

let serialize_dsum_cases
  (s: dsum)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (sg: serializer g)
  (x: dsum_key s)
: Tot (serializer (parse_dsum_cases s f g x))
= match x with
  | TotalKnown x ->
    synth_dsum_known_case_injective s x;
    synth_dsum_known_case_inverse s x;
    serialize_ext
      (dsnd (f x) `parse_synth` synth_dsum_known_case s x)
      (serialize_synth
        _
        (synth_dsum_known_case s x)
        (sr x)
        (synth_dsum_known_case_recip s x)
        ()
      )
      (parse_dsum_cases s f g (TotalKnown x))
  | TotalUnknown x ->
    synth_dsum_unknown_case_injective s x;
    synth_dsum_unknown_case_inverse s x;
    serialize_ext
      (g `parse_synth` synth_dsum_unknown_case s x)
      (serialize_synth
        _
        (synth_dsum_unknown_case s x)
        sg
        (synth_dsum_unknown_case_recip s x)
        ()
      )
      (parse_dsum_cases s f g (TotalUnknown x))

let serialize_dsum'
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
: Pure (serializer (parse_dsum' t p pc))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_tagged_union
    #(kt)
    #(dsum_key t)
    #(parse_maybe_total_enum_key p (dsum_enum t))
    (serialize_maybe_total_enum_key p s (dsum_enum t))
    #(dsum_type t)
    (dsum_tag_of_data t)
    #k
    #pc
    sc

let serialize_dsum
  (#kt: parser_kind)  
  (s: dsum)
  (#pt: parser kt (dsum_repr_type s))
  (st: serializer pt)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (sg: serializer g)
: Pure (serializer (parse_dsum s pt f g))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= serialize_dsum' s st #_ #(parse_dsum_cases s f g) (serialize_dsum_cases s f sr g sg)

inline_for_extraction
let make_dsum
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (#data: Type0)
  (tag_of_data: (data -> Tot (maybe_total_enum_key e)))
: Tot (
    (type_of_known_tag: (key -> Tot Type0)) ->
    (type_of_unknown_tag: Type0) ->
    (synth_known_case: ((x: key) -> (y: type_of_known_tag x) -> Tot (refine_with_tag tag_of_data (TotalKnown x)))) ->
    (synth_unknown_case: ((x: unknown_enum_repr e) -> type_of_unknown_tag -> Tot (refine_with_tag tag_of_data (TotalUnknown x)))) ->
    (synth_case_recip: ((x: data) -> Tot (dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag (tag_of_data x)))) ->
    (synth_case_recip_synth_case: (
      (xy: (x: maybe_total_enum_key e & dsum_type_of_tag' e type_of_known_tag type_of_unknown_tag x)) ->
      Tot (squash
      (synth_dsum_case_recip' e tag_of_data type_of_known_tag type_of_unknown_tag synth_case_recip
        (synth_dsum_case' e tag_of_data type_of_known_tag type_of_unknown_tag synth_known_case synth_unknown_case xy) == xy))
    )) ->
    (synth_case_synth_case_recip: (
      (x: data) ->
      Tot (squash
      (synth_dsum_case' e tag_of_data type_of_known_tag type_of_unknown_tag synth_known_case synth_unknown_case
        (synth_dsum_case_recip' e tag_of_data type_of_known_tag type_of_unknown_tag synth_case_recip x) == x))
    )) ->
    dsum
  )
= DSum key repr e data tag_of_data

#set-options "--z3rlimit 16"

let serialize_dsum_eq
  (#kt: parser_kind)  
  (s: dsum)
  (#pt: parser kt (dsum_repr_type s))
  (st: serializer pt)
  (f: (x: dsum_known_key s) -> Tot (k: parser_kind & parser k (dsum_type_of_known_tag s x)))
  (sr: (x: dsum_known_key s) -> Tot (serializer (dsnd (f x))))
  (#k: parser_kind)
  (g: parser k (dsum_type_of_unknown_tag s))
  (sg: serializer g)
  (x: dsum_type s)
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (
    serialize (serialize_dsum s st f sr g sg) x == (
    let tg = dsum_tag_of_data s x in
    serialize (serialize_maybe_total_enum_key _ st (dsum_enum s)) tg `Seq.append` (
    match tg with
    | TotalKnown k -> serialize (sr k) (synth_dsum_known_case_recip s k x)
    | TotalUnknown k -> serialize sg (synth_dsum_unknown_case_recip s k x)
  ))))
= ()

#reset-options

(*
let serialize_dsum_upd
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
  (x: dsum_type t)
  (y: dsum_type t)
: Lemma
  (requires (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    kt.parser_kind_subkind == Some ParserStrong /\
    ty == tx /\
    Seq.length (serialize (sc ty) y) == Seq.length (serialize (sc tx) x)
  ))
  (ensures (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
    let sx' = serialize (serialize_dsum t s sc) x in
    let sy = serialize (sc ty) y in
    tlen + Seq.length sy == Seq.length sx' /\
    serialize (serialize_dsum t s sc) y == seq_upd_seq sx' tlen sy
  ))
=   let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let st = serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx in
    let tlen = Seq.length st in
    let sx' = serialize (serialize_dsum t s sc) x in
    let sx = serialize (sc tx) x in
    let sy = serialize (sc ty) y in 
    let sy' = serialize (serialize_dsum t s sc) y in
    assert (tlen + Seq.length sy == Seq.length sx');
    seq_upd_seq_right sx' sy;
    Seq.lemma_split sx' tlen;
    Seq.lemma_split sy' tlen;
    Seq.lemma_append_inj (Seq.slice sx' 0 tlen) (Seq.slice sx' tlen (Seq.length sx')) st sx;
    Seq.lemma_append_inj (Seq.slice sy' 0 tlen) (Seq.slice sy' tlen (Seq.length sy')) st sy;
    assert (sy' `Seq.equal` seq_upd_seq sx' tlen sy)

#reset-options "--z3refresh --z3rlimit 32 --z3cliopt smt.arith.nl=false"

let serialize_dsum_upd_bw
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
  (x: dsum_type t)
  (y: dsum_type t)
: Lemma
  (requires (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    kt.parser_kind_subkind == Some ParserStrong /\
    ty == tx /\
    Seq.length (serialize (sc ty) y) == Seq.length (serialize (sc tx) x)
  ))
  (ensures (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
    let sx' = serialize (serialize_dsum t s sc) x in
    let sy = serialize (sc ty) y in
    tlen + Seq.length sy == Seq.length sx' /\
    serialize (serialize_dsum t s sc) y == seq_upd_bw_seq sx' 0 sy
  ))
= serialize_dsum_upd t s sc x y;
  let tx = dsum_tag_of_data t x in
  let ty = dsum_tag_of_data t y in
  let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
  let sx' = serialize (serialize_dsum t s sc) x in
  let sy = serialize (sc ty) y in
  assert (Seq.length sx' - Seq.length sy == tlen)

let serialize_dsum_upd_chain
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
  (x: dsum_type t)
  (y: dsum_type t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let sx = serialize (sc tx) x in
    kt.parser_kind_subkind == Some ParserStrong /\
    ty == tx /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize (sc ty) y == seq_upd_seq sx i' s'
  ))
  (ensures (
    let tx = dsum_tag_of_data t x in
    let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
    let sx' = serialize (serialize_dsum t s sc) x in
    tlen + Seq.length (serialize (sc tx) x) == Seq.length sx' /\
    tlen + i' + Seq.length s' <= Seq.length sx' /\
    serialize (serialize_dsum t s sc) y == seq_upd_seq sx' (tlen + i') s'
  ))
= serialize_dsum_upd t s sc x y;
  let tx = dsum_tag_of_data t x in
  let sx = serialize (sc tx) x in
  let sx' = serialize (serialize_dsum t s sc) x in
  let st = serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx in
  let tlen = Seq.length st in
  seq_upd_seq_right_to_left sx' tlen sx i' s';
  Seq.lemma_split sx' tlen;
  Seq.lemma_append_inj (Seq.slice sx' 0 tlen) (Seq.slice sx' tlen (Seq.length sx')) st sx;
  seq_upd_seq_seq_upd_seq_slice sx' tlen (Seq.length sx') i' s'

let serialize_dsum_upd_bw_chain
  (#kt: parser_kind)
  (t: dsum)
  (#p: parser kt (dsum_repr_type t))
  (s: serializer p)
  (#k: parser_kind)
  (#pc: ((x: dsum_key t) -> Tot (parser k (dsum_cases t x))))
  (sc: ((x: dsum_key t) -> Tot (serializer (pc x))))
  (x: dsum_type t)
  (y: dsum_type t)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let tx = dsum_tag_of_data t x in
    let ty = dsum_tag_of_data t y in
    let sx = serialize (sc tx) x in
    kt.parser_kind_subkind == Some ParserStrong /\
    ty == tx /\
    i' + Seq.length s' <= Seq.length sx /\
    serialize (sc ty) y == seq_upd_bw_seq sx i' s'
  ))
  (ensures (
    let tx = dsum_tag_of_data t x in
    let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
    let sx' = serialize (serialize_dsum t s sc) x in
    tlen + Seq.length (serialize (sc tx) x) == Seq.length sx' /\
    i' + Seq.length s' <= Seq.length sx' /\
    serialize (serialize_dsum t s sc) y == seq_upd_bw_seq sx' (i') s'
  ))
= let tx = dsum_tag_of_data t x in
  let j' = Seq.length (serialize (sc tx) x) - i' - Seq.length s' in
  serialize_dsum_upd_chain t s sc x y j' s';
  let sx' = serialize (serialize_dsum t s sc) x in
  let tlen = Seq.length (serialize (serialize_maybe_enum_key _ s (dsum_enum t)) tx) in
  assert (tlen + j' == Seq.length sx' - i' - Seq.length s');
  assert (seq_upd_bw_seq sx' i' s' == seq_upd_seq sx' (tlen + j') s');
  ()
