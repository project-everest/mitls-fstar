module LowParse.Low.Base
include LowParse.Spec.Base

module B = FStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module S = LowParse.Slice

type buffer8 = B.buffer FStar.UInt8.t

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

let slice_ptr_as_seq 
  (h: HS.mem) (#t: Type) (b: pointer (B.buffer t)) (len: pointer U32.t) : Ghost (Seq.seq t)
  (requires (is_slice_ptr h b len))
  (ensures (fun _ -> True))
= let b' = B.get h b 0 in
  B.as_seq h b'

let is_tail_of (#t: Type) (b' b : B.buffer t) : GTot Type0 =
  B.length b' <= B.length b /\
  b' == B.sub b (U32.uint_to_t (B.length b - B.length b')) (U32.uint_to_t (B.length b'))

let tail_ptr (h h' : HS.mem) (#t: Type) (p: pointer (B.buffer t)) =
  B.live h p /\
  B.live h' p /\ (
    let b = B.get h p 0 in
    let b' = B.get h' p 0 in
    B.live h b /\
    B.live h' b /\
    b' `is_tail_of` b
  )

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
  B.modifies_2 input sz h h' /\ (
    let pv = parse p (B.as_seq h (B.get h input 0)) in
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

inline_for_extraction
val validate
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (s: S.bslice)
: HST.Stack (option S.bslice)
  (requires (fun h -> S.live h s))
  (ensures (fun h res h' ->
    B.modifies_0 h h' /\ (
    let ps = parse p (S.as_seq h s) in
    match res with
    | None -> None? ps
    | Some s' ->
      Some? ps /\ (
      let Some (_, consumed) = ps in
      s' == S.advanced_slice s (U32.uint_to_t consumed)
  ))))

let validate #k #t #p v s =
  HST.push_frame ();
  let input : pointer buffer8 = B.create (S.as_buffer s) 1ul in
  HST.push_frame ();
  let sz : pointer U32.t = B.create (S.length s) 1ul in
  let h1 = HST.get () in
  let vl = v input sz in
  let res =
    if vl then
      let input' = B.index input 0ul in
      let sz' = B.index sz 0ul in
      Some (S.of_buffer input' sz')
    else
      None
  in
  HST.pop_frame ();
  HST.pop_frame ();
  res

#reset-options

let parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: pointer buffer8) ->
  (sz: pointer U32.t) ->
  HST.Stack t
  (requires (fun h ->
    is_slice_ptr h input sz /\
    Some? (parse p (B.as_seq h (B.get h input 0)))
  ))
  (ensures (fun h res h' ->
    let ps = parse p (B.as_seq h (B.get h input 0)) in
    let (Some (res', _)) = ps in
    res == res' /\
    validator32_postcond p input sz h true h'
  ))

let validator_nochk32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: pointer buffer8) ->
  (sz: pointer U32.t) ->
  HST.Stack unit
  (requires (fun h ->
    is_slice_ptr h input sz /\
    Some? (parse p (B.as_seq h (B.get h input 0)))
  ))
  (ensures (fun h res h' ->
    validator32_postcond p input sz h true h'
  ))

inline_for_extraction
let truncate_slice_ptr
  (b: pointer buffer8)
  (len: pointer U32.t)
  (len' : U32.t)
: HST.Stack unit
  (requires (fun h -> is_slice_ptr h b len /\ U32.v len' <= U32.v (B.get h len 0)))
  (ensures (fun h _ h' ->
    B.modifies_2 b len h h' /\
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
    B.modifies_2 b len h h' /\
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
