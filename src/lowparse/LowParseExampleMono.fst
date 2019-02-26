module LowParseExampleMono
include LowParse.MLow.Base
open LowStar.FreezableBuffer

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack

let compl
  (t: Type)
  (pos: U32.t)
  (v: t)
  (pos' : U32.t)
  (x: Seq.seq byte)
: GTot Type0
= U32.v pos >= 4 /\
  Seq.length x >= 4 /\ (
  let len = get_w x in
  len >= 4 /\ len <= Seq.length x /\
  U32.v pos' <= len
  )

let wvalid_stable
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (s: slice freezable_preorder freezable_preorder)
  (pos: U32.t)
  (gpos' : Ghost.erased U32.t)
  (v' : Ghost.erased t)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    stable_on (wvalid p s (compl t) pos gpos' v') freezable_preorder
  ))
= let pf (s1 s2: Seq.seq byte) : Lemma
    (requires (wvalid p s (compl t) pos gpos' v' s1 /\ freezable_preorder s1 s2))
    (ensures (wvalid p s (compl t) pos gpos' v' s1 /\ freezable_preorder s1 s2 /\ wvalid p s (compl t) pos gpos' v' s2))
  = parse_strong_prefix p (Seq.slice s1 (U32.v pos) (U32.v s.len)) (Seq.slice s2 (U32.v pos) (U32.v s.len))
  in
  let pf' (s1 s2: Seq.seq byte) : Lemma
    ((wvalid p s (compl t) pos gpos' v' s1 /\ freezable_preorder s1 s2) ==> wvalid p s (compl t) pos gpos' v' s2)
  = Classical.move_requires (pf s1) s2
  in
  Classical.forall_intro_2 pf'

module HST = FStar.HyperStack.ST
module B = LowStar.Monotonic.Buffer

inline_for_extraction
let irepr
  (#t: Type)
  (#k: parser_kind)
  (p: parser k t)
  (s: slice freezable_preorder freezable_preorder)
= irepr p s (compl t)

inline_for_extraction
noextract
let witness_valid
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (s: slice freezable_preorder freezable_preorder)
  (pos: U32.t)
: HST.Stack (irepr p s)
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid p h s pos /\
    (* conditions on global size header *)
    U32.v pos >= 4 /\
    U32.v s.len >= 4 /\ (
    let len = get_w (B.as_seq h s.base) in
    len >= 4 /\ len <= U32.v s.len /\
    U32.v (get_valid_pos p h s pos) <= len
  )))
  (ensures (fun h res h' ->
    h' == h /\
    irepr_pos res == pos /\
    valid_content_pos p h s pos (irepr_v res) (irepr_pos' res)
  ))
= let h = HST.get () in
  wvalid_stable p s pos (Ghost.hide (get_valid_pos p h s pos)) (Ghost.hide (contents p h s pos));
  witness_valid_gen s (compl t) pos

inline_for_extraction
noextract
let recall_valid
  (#t: Type)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: slice freezable_preorder freezable_preorder)
  (i: irepr p s)
: HST.Stack unit
  (requires (fun h -> B.recallable s.base \/ live_slice h s))
  (ensures (fun h _ h' ->
    h' == h /\
    live_slice h s /\
    valid_content_pos p h s (irepr_pos i) (irepr_v i) (irepr_pos' i) /\
    U32.v s.len >= 4 /\
    U32.v (irepr_pos i) >= 4 /\
    U32.v (irepr_pos' i) <= get_w (B.as_seq h s.base)
  ))
= recall_valid_gen i

inline_for_extraction
noextract
let iaccess
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#cl: clens t1 t2)
  (#g: gaccessor p1 p2 cl)
  ($a: accessor g)
  (#s: slice freezable_preorder freezable_preorder)
  (i1: irepr p1 s)
: HST.Stack (irepr p2 s)
  (requires (fun h ->
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    cl.clens_cond (irepr_v i1) /\
    witnessed s.base (w_pred 4) /\
    (B.recallable s.base \/ live_slice h s)
  ))
  (ensures (fun h i2 h' ->
    B.modifies B.loc_none h h' /\
    valid_content_pos p1 h s (irepr_pos i1) (irepr_v i1) (irepr_pos' i1) /\
    valid_content_pos p2 h s (irepr_pos i2) (irepr_v i2) (irepr_pos' i2) /\
    irepr_pos i2 == slice_access h g s (irepr_pos i1) /\
    irepr_v i2 == cl.clens_get (irepr_v i1)
  ))
= recall_valid i1;
  let x = a s (irepr_pos i1) in
  recall_w_default s.base;
  witness_valid s x

let freezable_buffer_writable_intro
  (b: mbuffer byte freezable_preorder freezable_preorder)
  (pos pos' : nat)
  (h: HS.mem)
: Lemma
  (requires (
    B.length b >= 4 /\ (
    let len = get_w (B.as_seq h b) in
    B.live h b /\
    4 <= len /\
    len <= pos
  )))
  (ensures (writable b pos pos' h))
  [SMTPat (writable b pos pos' h)]
= if pos <= pos' && pos' <= B.length b
  then
    let s = B.as_seq h b in
    let slen = Seq.slice s 0 4 in
    writable_intro b pos pos' h () (fun s1 s2 ->
      assert (Seq.slice (Seq.replace_subseq s pos pos' s1) 0 4 `Seq.equal` slen);
      assert (Seq.slice (Seq.replace_subseq s pos pos' s2) 0 4 `Seq.equal` slen)
    )

val main: FStar.Int32.t -> LowStar.Buffer.buffer (LowStar.Buffer.buffer C.char) ->
  FStar.HyperStack.ST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main _ _ = C.EXIT_SUCCESS
