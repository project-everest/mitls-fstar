module LowParse.Low.Combinators
include LowParse.Low.Base
include LowParse.Spec.Combinators

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

#set-options "--z3rlimit 16"

let valid_nondep_then
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (live_slice h s))
  (ensures ((
    valid (nondep_then p1 p2) h s pos \/
    (valid p1 h s pos /\ valid p2 h s (get_valid_pos p1 h s pos))
  ) ==> (
    valid p1 h s pos /\ (
    let pos1 = get_valid_pos p1 h s pos in
    valid p2 h s (get_valid_pos p1 h s pos) /\
    valid_content_pos (nondep_then p1 p2) h s pos (contents p1 h s pos, contents p2 h s pos1) (get_valid_pos p2 h s pos1)
  ))))
= valid_facts p1 h s pos;
  valid_facts (nondep_then p1 p2) h s pos;
  if valid_dec p1 h s pos
  then begin
    let pos1 = get_valid_pos p1 h s pos in
    nondep_then_eq p1 p2 (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos)));
    valid_facts p2 h s pos1
  end

inline_for_extraction
let validate_nondep_then
  [| validator_cls |]
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (p1' : validator p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (p2' : validator p2)
: Tot (validator (nondep_then p1 p2))
= fun (input: slice) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_nondep_then h p1 p2 input pos in
  let pos1 = p1' input pos in
  if pos1 `U32.gt` validator_max_length
  then begin
    pos1
  end
  else
    [@inline_let] let _ = valid_facts p2 h input pos1 in
    p2' input pos1

inline_for_extraction
let jump_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (p1' : jumper p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (p2' : jumper p2)
: Tot (jumper (nondep_then p1 p2))
= fun (input: slice) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_nondep_then h p1 p2 input pos in
  p2' input (p1' input pos)

let valid_synth
  (h: HS.mem)
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    live_slice h input /\ synth_injective f2
  ))
  (ensures (
    (valid (parse_synth p1 f2) h input pos \/ valid p1 h input pos) ==> (
      valid p1 h input pos /\
      valid_content_pos (parse_synth p1 f2) h input pos (f2 (contents p1 h input pos)) (get_valid_pos p1 h input pos)
  )))
= valid_facts p1 h input pos;
  valid_facts (parse_synth p1 f2) h input pos;
  if valid_dec p1 h input pos
  then parse_synth_eq p1 f2 (B.as_seq h (B.gsub input.base pos (input.len `U32.sub` pos)))

inline_for_extraction
let validate_synth
  [| validator_cls |]
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser k t1)
  (p1' : validator p1)
  (f2: t1 -> GTot t2)
  (u: unit {
    synth_injective f2
  })
: Tot (validator (parse_synth p1 f2))
= fun (input: slice) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_synth h p1 f2 input pos in
  p1' input pos

inline_for_extraction
let jump_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser k t1)
  (p1' : jumper p1)
  (f2: t1 -> GTot t2)
  (u: unit {
    synth_injective f2
  })
: Tot (jumper (parse_synth p1 f2))
= fun (input: slice) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_synth h p1 f2 input pos in
  p1' input pos

let valid_total_constant_size
  (h: HS.mem)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: U32.t)
  (input: slice)
  (pos: U32.t)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz /\
    k.parser_kind_metadata.parser_kind_metadata_total = true
  ))
  (ensures (
    (valid p h input pos <==> (live_slice h input /\ U32.v input.len - U32.v pos >= k.parser_kind_low)) /\
    (valid p h input pos ==> content_length p h input pos == k.parser_kind_low)
  ))
= valid_facts p h input pos

inline_for_extraction
let validate_total_constant_size
  [| validator_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: U32.t)
  (u: unit {
    U32.v sz <= U32.v validator_max_length /\
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz /\
    k.parser_kind_metadata.parser_kind_metadata_total = true
  })
: Tot (validator p)
= fun (input: slice) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_total_constant_size h p sz input pos in
  if U32.lt (input.len `U32.sub` pos) sz
  then validator_max_length `U32.add` 1ul // FIXME: more control over failures
  else
    pos `U32.add` sz

inline_for_extraction
let validate_ret
  [| validator_cls |]
  (#t: Type)
  (v: t)
: Tot (validator (parse_ret v))
= validate_total_constant_size (parse_ret v) 0ul ()

inline_for_extraction
let validate_empty [| validator_cls |] () : Tot (validator parse_empty)
= validate_ret ()

inline_for_extraction
let jump_constant_size
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: U32.t)
  (u: unit {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz
  })
: Tot (jumper p)
= fun (input: slice) (pos: U32.t) ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts p h input pos in
  pos `U32.add` sz

let clens_synth
  (#t1: Type)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_injective f } )
: Tot (clens (fun (x: t1) -> True) t2)
= {
  clens_get = (fun (x: t1) -> f x);
  clens_put = (fun (x: t1) (y: t2) -> g y);
  clens_get_put = (fun (x: t1) (y: t2) -> ());
  clens_put_put = (fun (x: t1) (y y' : t2) -> ());
  clens_put_get = (fun (x: t1) -> ());
}

let gaccessor_synth'
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_inverse g f } )
  (input: bytes)
: Ghost nat
  (requires (gaccessor_pre (parse_synth p1 f) p1 (clens_synth g f ()) input))
  (ensures (fun pos' -> gaccessor_post (parse_synth p1 f) p1 (clens_synth g f ()) input pos'))
= 0

let gaccessor_synth
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (#t2: Type)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_inverse g f } )
: Tot (gaccessor (parse_synth p1 f) p1 (clens_synth g f ()))
= gaccessor_synth' p1 f g u

inline_for_extraction
let accessor_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f: t1 -> GTot t2)
  (g: t2 -> GTot t1)
  (u: unit { synth_inverse f g /\ synth_inverse g f } )
: Tot (accessor (gaccessor_synth p1 f g u))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_synth p1 f g u) input pos in
  pos

let clens_fst
  (t1: Type)
  (t2: Type)
: Tot (clens (fun (x: (t1 & t2)) -> True) t1)
= {
  clens_get = fst;
  clens_put = (fun x y -> (y, snd x));
  clens_get_put = (fun x y -> ());
  clens_put_put = (fun x y y' -> ());
  clens_put_get = (fun x -> ());
}

let clens_snd
  (t1: Type)
  (t2: Type)
: Tot (clens (fun (x: (t1 & t2)) -> True) t2)
= {
  clens_get = snd;
  clens_put = (fun x y -> (fst x, y));
  clens_get_put = (fun x y -> ());
  clens_put_put = (fun x y y' -> ());
  clens_put_get = (fun x -> ());
}

let gaccessor_fst'
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (input: bytes)
: Ghost nat
  (requires (gaccessor_pre (p1 `nondep_then` p2) p1 (clens_fst _ _) input))
  (ensures (fun pos' -> gaccessor_post (p1 `nondep_then` p2) p1 (clens_fst _ _) input pos'))
= 0

let gaccessor_fst
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (gaccessor (p1 `nondep_then` p2) p1 (clens_fst _ _))
= gaccessor_fst' p1 p2

let gaccessor_snd'
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (input: bytes)
: Ghost nat
  (requires (gaccessor_pre (p1 `nondep_then` p2) p2 (clens_snd _ _) input))
  (ensures (fun pos' -> gaccessor_post (p1 `nondep_then` p2) p2 (clens_snd _ _) input pos'))
= let (Some (_, consumed)) = parse p1 input in
  consumed

let gaccessor_snd
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (gaccessor (p1 `nondep_then` p2) p2 (clens_snd _ _))
= gaccessor_snd' p1 p2

let clens_fst_snd_disjoint
  (t1 t2: Type)
: Lemma
  (clens_disjoint (clens_fst t1 t2) (clens_snd t1 t2))
= clens_disjoint_l_intro (clens_fst t1 t2) (clens_snd t1 t2) (fun x1 x2 -> ());
  clens_disjoint_l_intro (clens_snd t1 t2) (clens_fst t1 t2) (fun x1 x2 -> ())

let gaccessor_fst_snd_disjoint
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Lemma
  (gaccessors_disjoint (gaccessor_fst p1 p2) (gaccessor_snd p1 p2))
= clens_fst_snd_disjoint t1 t2;
  gaccessors_disjoint_intro (gaccessor_fst p1 p2) (gaccessor_snd p1 p2) () (fun x -> ())

inline_for_extraction
let accessor_fst
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (accessor (gaccessor_fst p1 p2))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_fst p1 p2) input pos in
  pos

inline_for_extraction
let accessor_snd
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: jumper p1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (accessor (gaccessor_snd p1 p2))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_snd p1 p2) input pos in
  [@inline_let] let _ = valid_facts p1 h input pos in
  j1 input pos

inline_for_extraction
let make_total_constant_size_parser32
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (t)))
  (u: unit {
    make_total_constant_size_parser_precond sz t f
  })
  (f' : ((s: buffer8) -> HST.Stack t
    (requires (fun h -> B.live h s /\ B.length s == sz))
    (ensures (fun h res h' ->
      h == h' /\
      res == f (B.as_seq h s)
  ))))
: Tot (leaf_reader (make_total_constant_size_parser sz t f))
= fun sl pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_facts (make_total_constant_size_parser sz t f) h sl pos in
  f' (B.sub sl.base pos sz')

let valid_filter
  (h: HS.mem)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (f: (t -> GTot bool))
  (input: slice)
  (pos: U32.t)
: Lemma
  (
    (valid (parse_filter p f) h input pos \/ (valid p h input pos /\ f (contents p h input pos))) ==> (
    valid p h input pos /\
    f (contents p h input pos) == true /\
    valid_content_pos (parse_filter p f) h input pos (contents p h input pos) (get_valid_pos p h input pos)
  ))
= valid_facts (parse_filter p f) h input pos;
  valid_facts p h input pos

inline_for_extraction
let validate_filter
  [| validator_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v32: validator p)
  (p32: leaf_reader p)
  (f: (t -> GTot bool))
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Tot (validator (parse_filter p f))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h p f input pos in
  let res = v32 input pos in
  if res `U32.gt` validator_max_length
  then res
  else
    let va = p32 input pos in
    if f' va
    then res
    else validator_max_length `U32.add` 1ul // FIXME: more control on error

inline_for_extraction
let jump_filter
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (j: jumper p)
  (f: (t -> GTot bool))
: Tot (jumper (parse_filter p f))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h p f input pos in
  j input pos

inline_for_extraction
let parse32_filter
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: leaf_reader p)
  (f: (t -> GTot bool))
: Tot (leaf_reader (parse_filter p f))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_filter h p f input pos in
  (p32 input pos <: (res: t { f res == true } )) // FIXME: WHY WHY WHY do we need this coercion?

inline_for_extraction
let parse32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (f2': (x: t1) -> Tot (y: t2 { y == f2 x } )) 
  (p1' : leaf_reader p1)
  (u: unit {
    synth_injective f2
  })
: Tot (leaf_reader (parse_synth p1 f2))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = valid_synth h p1 f2 input pos in
  let res = p1' input pos in
  f2' res <: t2 // FIXME: WHY WHY WHY this coercion AND the separate let binding?

inline_for_extraction
let parse32_synth'
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
  (p1' : leaf_reader p1)
  (u: unit {
    synth_injective f2
  })
: Tot (leaf_reader (parse_synth p1 f2))
= parse32_synth p1 f2 (fun x -> f2 x) p1' u

(*
#set-options "--z3rlimit 32"

inline_for_extraction
let validate32_filter_and_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (v1: validator32 p1)
  (p1': parser32 p1)
  (f: (t1 -> GTot bool))
  (f' : ((x: t1) -> Tot (y: bool { y == f x } )))
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: ((x: t1 { f x == true} ) -> parser k2 t2))
  (v2: ((x1: t1 { f x1 == true } ) -> validator32 (p2 x1)))
  (u: unit {
    and_then_cases_injective p2
  })
: Tot (validator32 (parse_filter p1 f `and_then` p2))
= fun input len ->
  let res = v1 input len in
  if res `I32.lt` 0l
  then res
  else
    let va = p1' input in
    if f' va
    then
      v2 va (B.offset input (Cast.int32_to_uint32 (len `I32.sub` res))) res
    else -1l
