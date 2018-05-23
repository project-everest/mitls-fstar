module LowParse.Low.Base
include LowParse.Spec.Base

module B = FStar.Buffer
module M = FStar.Modifies
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

inline_for_extraction
type buffer8 = B.buffer FStar.UInt8.t

inline_for_extraction
type pointer (t: Type) = (b: Buffer.buffer t { B.length b == 1 } )

let is_slice (h: HS.mem) (#t: Type) (b: Buffer.buffer t) (len: U32.t) : GTot Type0 =
  B.live h b /\
  B.length b == U32.v len

let is_slice_ptr (h: HS.mem) (#t: Type) (b: pointer (B.buffer t)) (len: pointer U32.t) : GTot Type0 =
  B.live h b /\
  B.live h len /\
  B.disjoint b len /\ (
    let b' = B.get h b 0 in
    let len' = B.get h len 0 in
    B.disjoint b' b /\
    B.disjoint b' len /\
    is_slice h b' len'
  )

let includes_slice_ptr (h h' : HS.mem) (#t: Type) (b: pointer (B.buffer t)) (len: pointer U32.t) : GTot Type0 =
  is_slice_ptr h b len /\
  is_slice_ptr h' b len /\
  B.get h b 0 `B.includes` B.get h' b 0

let slice_ptr_as_seq 
  (h: HS.mem) (#t: Type) (b: pointer (B.buffer t)) (len: pointer U32.t) : Ghost (Seq.seq t)
  (requires (is_slice_ptr h b len))
  (ensures (fun _ -> True))
= let b' = B.get h b 0 in
  B.as_seq h b'

let is_tail_of (#t: Type) (b' b : B.buffer t) : GTot Type0 =
  B.length b' <= B.length b /\
  b' == B.sub b (U32.uint_to_t (B.length b - B.length b')) (U32.uint_to_t (B.length b'))

let tail_ptr (h h' : HS.mem) (#t: Type) (p: pointer (B.buffer t)) : GTot Type0 =
  B.live h p /\
  B.live h' p /\ (
    let b = B.get h p 0 in
    let b' = B.get h' p 0 in
    B.live h b /\
    B.live h' b /\
    b' `is_tail_of` b
  )

let parse_from_slice
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (b: buffer8)
  (sz: U32.t)
: Ghost (option (t * nat))
  (requires (is_slice h b sz))
  (ensures (fun y ->
    match y with
    | None -> parse p (B.as_seq h b) == None
    | Some (x, len) -> len <= B.length b /\ parse p (B.as_seq h b) == Some (x, len)
  ))
= match parse p (B.as_seq h b) with
  | Some (x, len) -> Some (x, len)
  | _ -> None

let exactly_parse_from_slice
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (b: buffer8)
  (sz: U32.t)
: Ghost (option t)
  (requires (is_slice h b sz))
  (ensures (fun y ->
    match y with
    | None ->
      begin match parse p (B.as_seq h b) with
      | None -> True
      | Some (_, consumed) -> consumed <> B.length b
      end
    | Some x -> parse p (B.as_seq h b) == Some (x, B.length b)
  ))
= match parse p (B.as_seq h b) with
  | Some (x, len) ->
    if len = U32.v sz
    then Some x
    else None
  | _ -> None

unfold
let gsub
  (#t: Type)
  (b: B.buffer t)
  (i: U32.t)
  (len: U32.t)
: Ghost (B.buffer t)
  (requires (U32.v i + U32.v len <= B.length b))
  (ensures (fun b' -> B.length b' == U32.v len))
= B.sub b i len

let exactly_parse_from_slice_intro'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (b: buffer8)
  (sz: U32.t)
  (x: t)
  (consumed: nat)
  (u: unit {
    is_slice h b sz /\
    parse_from_slice p h b sz == Some (x, consumed)
  })
: Lemma
  (ensures (
    is_slice h b sz /\
    consumed <= U32.v sz /\
    exactly_parse_from_slice p h (gsub b 0ul (U32.uint_to_t consumed)) (U32.uint_to_t consumed) == Some x
  ))
= assert (no_lookahead_weak_on p (B.as_seq h b) (B.as_seq h (gsub b 0ul (U32.uint_to_t consumed))))

let exactly_parse_from_slice_intro
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (b: buffer8)
  (sz: U32.t)
: Lemma
  (requires (
    is_slice h b sz /\
    Some? (parse_from_slice p h b sz)
  ))
  (ensures (
    let (Some (x, consumed)) = parse_from_slice p h b sz in
    consumed <= U32.v sz /\
    exactly_parse_from_slice p h (gsub b 0ul (U32.uint_to_t consumed)) (U32.uint_to_t consumed) == Some x
  ))
//  [SMTPat (parse_from_slice p h b sz)]
= let (Some (x, consumed)) = parse_from_slice p h b sz in
  exactly_parse_from_slice_intro' p h b sz x consumed ()

unfold
let parse_from_slice_ptr
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (b: pointer buffer8)
  (sz: pointer U32.t)
: Ghost (option (t * nat))
  (requires (is_slice_ptr h b sz))
  (ensures (fun _ -> True))
= parse_from_slice p h (B.get h b 0) (B.get h sz 0)

unfold
let exactly_parse_from_slice_ptr
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (b: pointer buffer8)
  (sz: pointer U32.t)
: Ghost (option t)
  (requires (is_slice_ptr h b sz))
  (ensures (fun _ -> True))
= exactly_parse_from_slice p h (B.get h b 0) (B.get h sz 0)

let exactly_parse_from_slice_ptr_intro
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (b: pointer buffer8)
  (sz: pointer U32.t)
: Lemma
  (requires (
    is_slice_ptr h b sz /\
    Some? (parse_from_slice_ptr p h b sz)
  ))
  (ensures (
    let (Some (x, consumed)) = parse_from_slice_ptr p h b sz in
    consumed <= U32.v (B.get h sz 0) /\
    exactly_parse_from_slice p h (gsub (B.get h b 0) 0ul (U32.uint_to_t consumed)) (U32.uint_to_t consumed) == Some x
  ))
= exactly_parse_from_slice_intro p h (B.get h b 0) (B.get h sz 0)

(* A validator, if succeeds, returns true and leaves the tail slice; otherwise returns false. *)

let loc_slice (b: pointer buffer8) (sz: pointer U32.t) : GTot M.loc =
  M.loc_union (M.loc_buffer b) (M.loc_buffer sz)

let validator32_postcond
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: pointer buffer8)
  (sz: pointer U32.t)
  (h: HS.mem)
  (res: bool)
  (h' : HS.mem)
: GTot Type0
= is_slice_ptr h input sz /\
  M.modifies (loc_slice input sz) h h' /\ (
    let pv = parse_from_slice_ptr p h input sz in
    if res
    then
      is_slice_ptr h' input sz /\
      Some? pv /\ (
        let Some (_, consumed) = pv in
        let len' = U32.uint_to_t (U32.v (B.get h sz 0) - consumed) in
        B.get h' input 0 == B.sub (B.get h input 0) (U32.uint_to_t consumed) len' /\
        B.get h' sz 0 == len'
      )
    else
      B.live h' input /\
      B.live h' sz /\
      None? pv
  )

inline_for_extraction
let validator32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: pointer buffer8) ->
  (sz: pointer U32.t) ->
  HST.Stack bool
  (requires (fun h ->
    is_slice_ptr h input sz
  ))
  (ensures (fun h res h' ->
    validator32_postcond p input sz h res h'
  ))

(* Derivative: if vp is a validator, then validate_and_truncate vp returns true iff input is valid, and if so, truncates to the parsing slice. *)

inline_for_extraction
val validate32_and_truncate32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (vp: validator32 p)
  (b: pointer buffer8)
  (sz: pointer U32.t)
: HST.Stack bool
  (requires (fun h ->
    is_slice_ptr h b sz
  ))
  (ensures (fun h res h' ->
    M.modifies (loc_slice b sz) h h' /\
    is_slice_ptr h b sz /\ (
    let pb = parse_from_slice_ptr p h b sz in
    if res
    then
      Some? pb /\ (
        let (Some (v, consumed)) = pb in
        is_slice_ptr h' b sz /\
        consumed <= B.length (B.get h b 0) /\
        B.get h' b 0 == gsub (B.get h b 0) 0ul (U32.uint_to_t consumed) /\
        exactly_parse_from_slice_ptr p h' b sz == Some v
      )
    else
      B.live h' b /\
      B.live h' sz /\
      None? pb
  )))

#set-options "--z3rlimit 16"

let validate32_and_truncate32 #k #t #p vp b sz =
  let h = HST.get () in
  let b0 = B.index b 0ul in
  let sz0 = B.index sz 0ul in
  if vp b sz
  then begin
    let tail_sz = B.index sz 0ul in
    let sz' = U32.sub sz0 tail_sz in
    let b' = B.sub b0 0ul sz' in
    B.upd b 0ul b' ;
    B.upd sz 0ul sz' ;
    exactly_parse_from_slice_intro p h b0 sz0 ;
    true
  end
  else false

#reset-options

inline_for_extraction
let parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) ->
  HST.Stack t
  (requires (fun h ->
    B.live h input /\
    Some? (parse p (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    M.modifies M.loc_none h h' /\
    B.live h' input /\ (
    let ps = parse p (B.as_seq h input) in
    let (Some (res', _)) = ps in
    res == res'
  )))

inline_for_extraction
let validator_nochk32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) ->
  HST.Stack U32.t
  (requires (fun h ->
    B.live h input /\
    Some? (parse p (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    M.modifies M.loc_none h h' /\
    B.live h' input /\
    U32.v res <= B.length input /\ (
    let (Some (x, res')) = parse p (B.as_seq h input) in
    U32.v res == res'
  )))

inline_for_extraction
val truncate32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator_nochk32 p)
  (input: pointer buffer8)
  (sz: pointer U32.t)
: HST.Stack unit
  (requires (fun h ->
    is_slice_ptr h input sz /\
    Some? (parse_from_slice_ptr p h input sz)
  ))
  (ensures (fun h _ h' ->
    M.modifies (loc_slice input sz) h h' /\
    is_slice_ptr h' input sz /\ (
    let (Some (v, consumed)) = parse_from_slice_ptr p h input sz in
    consumed <= B.length (B.get h input 0) /\
    B.get h' input 0 == gsub (B.get h input 0) 0ul (U32.uint_to_t consumed) /\
    exactly_parse_from_slice_ptr p h' input sz == Some v
  )))

#set-options "--z3rlimit 16"

let truncate32 #k #t #p v input sz =
  let h = HST.get () in
  let b0 = B.index input 0ul in
  let sz0 = B.index sz 0ul in
  let sz' = v b0 in
  let b' = B.sub b0 0ul sz' in
  B.upd input 0ul b' ;
  B.upd sz 0ul sz' ;
  exactly_parse_from_slice_intro p h b0 sz0

#reset-options

inline_for_extraction
let truncate_slice_ptr
  (b: pointer buffer8)
  (len: pointer U32.t)
  (len' : U32.t)
: HST.Stack unit
  (requires (fun h -> is_slice_ptr h b len /\ U32.v len' <= U32.v (B.get h len 0)))
  (ensures (fun h _ h' ->
    M.modifies (loc_slice b len) h h' /\
    is_slice_ptr h' b len /\
    B.get h' len 0 == len' /\
    B.get h' b 0 == B.sub (B.get h b 0) 0ul len'
  ))
= let b0 = B.index b 0ul in
  let b' = B.sub b0 0ul len' in
  B.upd b 0ul b';
  B.upd len 0ul len'

inline_for_extraction
let advance_slice_ptr
  (b: pointer buffer8)
  (len: pointer U32.t)
  (ofs: U32.t)
: HST.Stack unit
  (requires (fun h -> is_slice_ptr h b len /\ U32.v ofs <= U32.v (B.get h len 0)))
  (ensures (fun h _ h' ->
    M.modifies (loc_slice b len) h h' /\
    is_slice_ptr h' b len /\ (
    let len' = U32.sub (B.get h len 0) ofs in
    B.get h' len 0 == len' /\
    B.get h' b 0 == B.sub (B.get h b 0) ofs len'
  )))
= let b0 = B.index b 0ul in
  let len0 = B.index len 0ul in
  let len' = U32.sub len0 ofs in
  let b' = B.sub b0 ofs len' in
  B.upd b 0ul b' ;
  B.upd len 0ul len'

abstract
let rec is_buffer_concat
  (#t: Type)
  (b: B.buffer t)
  (l: list (B.buffer t))
: GTot Type0
  (decreases l)
= match l with
  | [] -> False
  | [b'] -> b == b'
  | b1 :: q ->
    B.length b1 <= B.length b /\ (
      let len1 = U32.uint_to_t (B.length b1) in
      b1 == B.sub b 0ul len1 /\
      B.sub b len1 (U32.uint_to_t (B.length b - B.length b1)) `is_buffer_concat` q
    )

abstract
let is_buffer_concat_singleton
  (#t: Type)
  (b1 b2: B.buffer t)
: Lemma
  (is_buffer_concat b1 [b2] <==> b1 == b2)
  [SMTPat (is_buffer_concat b1 [b2])]
= ()

abstract
let is_buffer_concat_pair
  (#t: Type)
  (b b1 b2: B.buffer t)
: Lemma
  (is_buffer_concat b [b1; b2] <==> (
    B.length b1 + B.length b2 == B.length b /\
    b1 == B.sub b 0ul (U32.uint_to_t (B.length b1)) /\
    b2 == B.sub b (U32.uint_to_t (B.length b1)) (U32.uint_to_t (B.length b2))
  ))
  [SMTPat (is_buffer_concat b [b1; b2])]
= ()

abstract
let is_buffer_concat_cons
  (#t: Type)
  (b b1: B.buffer t)
  (q: list (B.buffer t))
: Lemma
  (is_buffer_concat b (b1 :: q) <==> (
    B.length b1 <= B.length b /\ (
    let len1 = U32.uint_to_t (B.length b1) in
    b1 == B.sub b 0ul len1 /\ (
    if Cons? q
    then
      B.sub b len1 (U32.uint_to_t (B.length b - B.length b1)) `is_buffer_concat` q
    else
      b == b1
  ))))
  [SMTPat (is_buffer_concat b (b1 :: q))]
= ()

module L = FStar.List.Tot

#set-options "--z3rlimit 16"

abstract
private
let rec is_buffer_concat_subst_l
  (#t: Type)
  (b b': B.buffer t)
  (l' l2: list (B.buffer t))
: Lemma
  (requires (
    b `is_buffer_concat` (b' :: l2) /\
    b' `is_buffer_concat` l'
  ))
  (ensures (
    b `is_buffer_concat` (l' `L.append` l2)
  ))
  (decreases l')
= match l' with
  | [_] -> ()
  | bq :: q ->
    let len_bq = U32.uint_to_t (B.length bq) in
    is_buffer_concat_subst_l
      (B.sub b len_bq (U32.uint_to_t (B.length b - B.length bq)))
      (B.sub b' len_bq (U32.uint_to_t (B.length b' - B.length bq)))
      q
      l2

abstract
let rec is_buffer_concat_subst
  (#t: Type)
  (b b': B.buffer t)
  (l1 l' l2: list (B.buffer t))
: Lemma
  (requires (
    b `is_buffer_concat` (l1 `L.append` (b' :: l2)) /\
    b' `is_buffer_concat` l'
  ))
  (ensures (
    b `is_buffer_concat` (l1 `L.append` (l' `L.append` l2))
  ))
  (decreases l1)
= match l1 with
  | [] -> is_buffer_concat_subst_l b b' l' l2
  | bq :: q ->
    let len_bq = U32.uint_to_t (B.length bq) in
    is_buffer_concat_subst
      (B.sub b len_bq (U32.uint_to_t (B.length b - B.length bq)))
      b'
      q
      l'
      l2

abstract
let rec is_buffer_concat_includes
  (#t: Type)
  (b b' : B.buffer t)
  (l1 l2: list (B.buffer t))
: Lemma
  (requires (b `is_buffer_concat` (l1 `L.append` (b' :: l2))))
  (ensures (b `B.includes` b'))
  (decreases l1)
= match l1 with
  | [] -> ()
  | bq :: q ->
    is_buffer_concat_includes
      (B.sub b (U32.uint_to_t (B.length bq)) (U32.uint_to_t (B.length b - B.length bq)))
      b'
      q
      l2

abstract
let rec is_buffer_concat_disjoint
  (#t: Type)
  (b b1 b2: B.buffer t)
  (l0 l1 l2: list (B.buffer t))
: Lemma
  (requires (b `is_buffer_concat` (l0 `L.append` (b1 :: (l1 `L.append` (b2 :: l2))))))
  (ensures (B.disjoint b1 b2))
  (decreases l0)
= match l0 with
  | [] ->
    is_buffer_concat_includes
      (B.sub b (U32.uint_to_t (B.length b1)) (U32.uint_to_t (B.length b - B.length b1)))
      b2
      l1
      l2
  | bq :: q ->
    is_buffer_concat_disjoint
      (B.sub b (U32.uint_to_t (B.length bq)) (U32.uint_to_t (B.length b - B.length bq)))
      b1
      b2
      q
      l1
      l2

inline_for_extraction
let accessor
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (rel: (t1 -> t2 -> GTot Type0))
: Tot Type
= (input: buffer8) ->
  HST.Stack buffer8
  (requires (fun h ->
    B.live h input /\
    Some? (parse p1 (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    M.modifies (M.loc_none) h h' /\
    B.live h' input /\
    B.includes input res /\ (
    let Some (x1, _) = parse p1 (B.as_seq h input) in
    let ps2 = parse p2 (B.as_seq h res) in
    Some? ps2 /\ (
    let Some (x2, _) = ps2 in
    rel x1 x2
  ))))

inline_for_extraction
let read_from_buffer
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#rel: (t1 -> t2 -> GTot Type0))
  (a12: accessor p1 p2 rel)
  (p2' : parser32 p2)
  (input: buffer8)
: HST.Stack t2
  (requires (fun h ->
    B.live h input /\
    Some? (parse p1 (B.as_seq h input))
  ))
  (ensures (fun h y h' ->
    M.modifies M.loc_none h h' /\ (
    let (Some (x, _)) = parse p1 (B.as_seq h input) in
    rel x y
  )))
= p2' (a12 input)
