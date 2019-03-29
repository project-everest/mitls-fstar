module Stash

module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Monotonic.Buffer
module FB = LowStar.PrefixFreezableBuffer
module LP = LowParse.Low.Base

(* Type definition and constructor *)

inline_for_extraction
noextract
type stash = (s: LP.slice (LP.srel_of_buffer_srel FB.prefix_freezable_preorder) (LP.srel_of_buffer_srel FB.prefix_freezable_preorder) {
  B.length s.LP.base >= 4 /\
  U32.v s.LP.len <= U32.v LP.validator_max_length /\
  B.witnessed s.LP.base (FB.frozen_until_at_least 4)
})

inline_for_extraction
noextract
let make_stash
  (b: FB.buffer)
  (len: U32.t { U32.v len <= B.length b /\ U32.v len <= U32.v LP.validator_max_length /\ B.witnessed b (FB.frozen_until_at_least 4) } )
: Tot stash
= LP.make_slice b len

(* Allocators *)

unfold
let malloc_pre
  (r: HS.rid)
  (len: U32.t)
: GTot Type0
= B.malloc_pre r len /\
  U32.v len <= U32.v LP.validator_max_length

unfold
let alloc_post_mem_common
  (h0: HS.mem)
  (s: stash)
  (h1: HS.mem)
: GTot Type0
= FB.alloc_post_mem_common h0 s.LP.base h1

inline_for_extraction
noextract
let gcmalloc
  (r: HS.rid)
  (len: U32.t)
: HST.ST (s: stash { B.frameOf s.LP.base == r /\ FB.recallable s.LP.base } )
  (requires (fun _ -> malloc_pre r len))
  (ensures alloc_post_mem_common)
= let b = FB.gcmalloc r len in
  make_stash b len

inline_for_extraction
noextract
let malloc
  (r: HS.rid)
  (len: U32.t)
: HST.ST (s: stash { B.frameOf s.LP.base == r /\ FB.freeable s.LP.base })
  (requires (fun _ -> malloc_pre r len))
  (ensures alloc_post_mem_common)
= let b = FB.malloc r len in
  make_stash b len

unfold
let alloca_pre
  (len: U32.t)
: GTot Type0
= U32.v len <= U32.v LP.validator_max_length /\
  B.alloca_pre len

inline_for_extraction
noextract
let alloca
  (len: U32.t)
: HST.StackInline stash
  (requires (fun _ -> alloca_pre len))
  (ensures (fun h0 s h1 ->
    alloc_post_mem_common h0 s h1 /\
    B.frameOf s.LP.base == HS.get_tip h0
  ))
= let b = FB.alloca len in
  make_stash b len

(* Witness and recall *)

let witness_compl
  (t: Type)
  (pos: U32.t)
  (v: t)
  (pos' : U32.t)
  (x: Seq.seq LP.byte)
: GTot Type0
= U32.v pos >= 4 /\
  Seq.length x >= 4 /\ (
  let len = FB.frozen_until x in
  len >= 4 /\ len <= Seq.length x /\
  U32.v pos' <= len
  )

let wvalid_stable
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (s: stash)
  (pos: U32.t)
  (gpos' : Ghost.erased U32.t)
  (v' : Ghost.erased t)
: Lemma
  (requires (k.LP.parser_kind_subkind == Some LP.ParserStrong))
  (ensures (
    FB.stable_on (LP.wvalid p s (witness_compl t) pos gpos' v') FB.prefix_freezable_preorder
  ))
= let pf (s1 s2: Seq.seq LP.byte) : Lemma
    (requires (LP.wvalid p s (witness_compl t) pos gpos' v' s1 /\ FB.prefix_freezable_preorder s1 s2))
    (ensures (LP.wvalid p s (witness_compl t) pos gpos' v' s1 /\ FB.prefix_freezable_preorder s1 s2 /\ LP.wvalid p s (witness_compl t) pos gpos' v' s2))
  = FB.prefix_freezable_preorder_elim s1 s2;
    LP.parse_strong_prefix p (Seq.slice s1 (U32.v pos) (U32.v s.LP.len)) (Seq.slice s2 (U32.v pos) (U32.v s.LP.len))
  in
  let pf' (s1 s2: Seq.seq LP.byte) : Lemma
    ((LP.wvalid p s (witness_compl t) pos gpos' v' s1 /\ FB.prefix_freezable_preorder s1 s2) ==> LP.wvalid p s (witness_compl t) pos gpos' v' s2)
  = Classical.move_requires (pf s1) s2
  in
  Classical.forall_intro_2 pf'

inline_for_extraction
noextract
let irepr
  (#t: Type)
  (#k: LP.parser_kind)
  (p: LP.parser k t)
  (s: stash)
= LP.irepr p s (witness_compl t)

let buffer_frozen_until (buf: FB.buffer) (h:HS.mem) : GTot nat =
  FB.frozen_until (B.as_seq h buf)

inline_for_extraction
noextract
let witness_valid
  (#t: Type)
  (#k: LP.parser_kind)
  (#p: LP.parser k t)
  (s: stash)
  (pos: U32.t)
: HST.Stack (irepr p s)
  (requires (fun h ->
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\
    LP.valid p h s pos /\
    (* conditions on global size header *)
    U32.v pos >= 4 /\ (
    let len = buffer_frozen_until s.LP.base h in
    U32.v (LP.get_valid_pos p h s pos) <= len
  )))
  (ensures (fun h res h' ->
    h' == h /\
    LP.irepr_pos res == pos /\
    LP.valid_content_pos p h s pos (LP.irepr_v res) (LP.irepr_pos' res)
  ))
= let h = HST.get () in
  FB.recall_frozen_until_default s.LP.base;
  wvalid_stable p s pos (Ghost.hide (LP.get_valid_pos p h s pos)) (Ghost.hide (LP.contents p h s pos));
  LP.witness_valid_gen s (witness_compl t) pos

inline_for_extraction
noextract
let recall_valid
  (#t: Type)
  (#k: LP.parser_kind)
  (#p: LP.parser k t)
  (#s: stash)
  (i: irepr p s)
: HST.Stack unit
  (requires (fun h -> B.recallable s.LP.base \/ LP.live_slice h s))
  (ensures (fun h _ h' ->
    h' == h /\
    LP.live_slice h s /\
    LP.valid_content_pos p h s (LP.irepr_pos i) (LP.irepr_v i) (LP.irepr_pos' i) /\
    U32.v s.LP.len >= 4 /\
    U32.v (LP.irepr_pos i) >= 4 /\
    U32.v (LP.irepr_pos' i) <= buffer_frozen_until s.LP.base h
  ))
= LP.recall_valid_gen i

(* LowParse operators: reading *)

inline_for_extraction
noextract
let iaccess
  (#k1: LP.parser_kind)
  (#t1: Type)
  (#p1: LP.parser k1 t1)
  (#k2: LP.parser_kind)
  (#t2: Type)
  (#p2: LP.parser k2 t2)
  (#cl: LP.clens t1 t2)
  (#g: LP.gaccessor p1 p2 cl)
  ($a: LP.accessor g)
  (#s: stash)
  (i1: irepr p1 s)
: HST.Stack (irepr p2 s)
  (requires (fun h ->
    k1.LP.parser_kind_subkind == Some LP.ParserStrong /\
    k2.LP.parser_kind_subkind == Some LP.ParserStrong /\
    cl.LP.clens_cond (LP.irepr_v i1) /\
    (B.recallable s.LP.base \/ LP.live_slice h s)
  ))
  (ensures (fun h i2 h' ->
    B.modifies B.loc_none h h' /\
    LP.valid_content_pos p1 h s (LP.irepr_pos i1) (LP.irepr_v i1) (LP.irepr_pos' i1) /\
    LP.valid_content_pos p2 h s (LP.irepr_pos i2) (LP.irepr_v i2) (LP.irepr_pos' i2) /\
    LP.irepr_pos i2 == LP.slice_access h g s (LP.irepr_pos i1) /\
    LP.irepr_v i2 == cl.LP.clens_get (LP.irepr_v i1)
  ))
= recall_valid i1;
  let x = a s (LP.irepr_pos i1) in
  FB.recall_frozen_until_default s.LP.base;
  witness_valid s x

inline_for_extraction
noextract
let iread
  (#k: LP.parser_kind)
  (#t: Type)
  (#p: LP.parser k t)
  (r: LP.leaf_reader p)
  (#s: stash)
  (i: irepr p s)
: HST.Stack t
  (requires (fun h -> (B.recallable s.LP.base \/ LP.live_slice h s)))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    LP.valid_content_pos p h s (LP.irepr_pos i) (LP.irepr_v i) (LP.irepr_pos' i) /\
    res == LP.irepr_v i
  ))
= recall_valid i;
  r s (LP.irepr_pos i)

inline_for_extraction
noextract
let ijump
  (#k: LP.parser_kind)
  (#t: Type)
  (#p: LP.parser k t)
  (j: LP.jumper p)
  (#s: stash)
  (i: irepr p s)
: HST.Stack U32.t
  (requires (fun h -> (B.recallable s.LP.base \/ LP.live_slice h s)))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    LP.valid_content_pos p h s (LP.irepr_pos i) (LP.irepr_v i) (LP.irepr_pos' i) /\
    res == LP.irepr_pos' i
  ))
= recall_valid i;
  j s (LP.irepr_pos i)

(* Validation and writing *)

let freezable_buffer_writable_intro
  (b: FB.buffer)
  (pos pos' : nat)
  (h: HS.mem)
: Lemma
  (requires (
    let len = buffer_frozen_until b h in
    B.live h b /\
    4 <= len /\
    len <= pos
  ))
  (ensures (LP.writable b pos pos' h))
  [SMTPat (LP.writable b pos pos' h)]
= if pos <= pos' && pos' <= B.length b
  then
    let s = B.as_seq h b in
    let slen = Seq.slice s 0 4 in
    Classical.forall_intro_2 FB.prefix_freezable_preorder_elim;
    LP.writable_intro b pos pos' h () (fun s1 s2 ->
      assert (Seq.slice (Seq.replace_subseq s pos pos' s1) 0 4 `Seq.equal` slen);
      assert (Seq.slice (Seq.replace_subseq s pos pos' s2) 0 4 `Seq.equal` slen)
    )

inline_for_extraction
noextract
let freeze_valid
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (sl: stash)
  (pos: U32.t)
  (pos' : U32.t)
: HST.Stack (irepr p sl)
  (requires (fun h ->
    (B.recallable sl.LP.base \/ LP.live_slice h sl) /\
    buffer_frozen_until sl.LP.base h <= U32.v pos /\
    LP.valid_pos p h sl pos pos' /\
    k.LP.parser_kind_subkind == Some LP.ParserStrong // for valid_exact_ext_intro
  ))
  (ensures (fun h res h' ->
    B.modifies (B.loc_buffer sl.LP.base) h h' /\
    buffer_frozen_until sl.LP.base h' == U32.v pos' /\
    LP.irepr_pos res == pos /\
    LP.irepr_pos' res == pos' /\
    LP.irepr_v res == LP.contents p h sl pos
  ))
=    B.recall_p sl.LP.base (FB.frozen_until_at_least 4); // to recover liveness
     let h1 = HST.get () in
     FB.freeze sl.LP.base pos' ;
     let h2 = HST.get () in
     LP.valid_pos_valid_exact p h1 sl pos pos' ;
     LP.valid_exact_ext_intro p h1 sl pos pos' h2 sl pos pos' ;
     witness_valid sl pos

let frozen_until_frame
  (sl: stash)
  (l: B.loc)
  (h h' : HS.mem)
: Lemma
  (requires (LP.live_slice h sl /\ B.modifies l h h' /\ B.loc_disjoint l (LP.loc_slice_from_to sl 0ul 4ul)))
  (ensures (buffer_frozen_until sl.LP.base h' == buffer_frozen_until sl.LP.base h))
  [SMTPatOr [
    [SMTPat (B.modifies l h h'); SMTPat (buffer_frozen_until sl.LP.base h);];
    [SMTPat (B.modifies l h h'); SMTPat (buffer_frozen_until sl.LP.base h');];
  ]]
= B.modifies_buffer_from_to_elim sl.LP.base 0ul 4ul l h h'

inline_for_extraction
noextract
let iwrite
  (#k: LP.parser_kind)
  (#t: Type)
  (#p: LP.parser k t)
  (#s: LP.serializer p)
  (w: LP.leaf_writer_strong s)
  (v: t)
  (sl: stash)
  (pos: U32.t)
: HST.Stack (irepr p sl)
  (requires (fun h ->
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\ // for valid_exact_ext_intro
    buffer_frozen_until sl.LP.base h <= U32.v pos /\
    U32.v pos + LP.serialized_length s v <= U32.v sl.LP.len /\
    (FB.recallable sl.LP.base \/ LP.live_slice h sl)
  ))
  (ensures (fun h i h' ->
    LP.irepr_v i == v /\
    LP.irepr_pos i == pos /\
    LP.irepr_pos' i == pos `U32.add` U32.uint_to_t (LP.serialized_length s v) /\
    buffer_frozen_until sl.LP.base h' == U32.v (LP.irepr_pos' i) /\
    B.modifies (B.loc_buffer sl.LP.base) h h'
  ))
=    B.recall_p sl.LP.base (FB.frozen_until_at_least 4); // to recover liveness
     let pos' = w v sl pos in
     freeze_valid p sl pos pos'

inline_for_extraction
noextract
let icopy
  (#rrel #rel: _)
  (#k: LP.parser_kind)
  (#t: Type)
  (p: LP.parser k t)
  (src: LowParse.Low.Base.slice rrel rel)
  (spos spos' : U32.t)
  (dst: stash)
  (dpos: U32.t)
: HST.Stack (irepr p dst)
  (requires (fun h ->
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\
    LP.valid_pos p h src spos spos' /\
    U32.v dpos + U32.v spos' - U32.v spos <= U32.v dst.LP.len /\
    B.loc_disjoint (LP.loc_slice_from_to src spos spos') (LP.loc_slice_from_to dst dpos (dpos `U32.add` (spos' `U32.sub` spos))) /\ (
    let len = buffer_frozen_until dst.LP.base h in
    (FB.recallable dst.LP.base \/ LP.live_slice h dst) /\
    len <= U32.v dpos
  )))
  (ensures (fun h i h' ->
    B.modifies (B.loc_buffer dst.LP.base) h h' /\
    LP.irepr_pos i == dpos /\
    LP.irepr_v i == LP.contents p h src spos /\
    buffer_frozen_until dst.LP.base h' == U32.v (LP.irepr_pos' i)
  ))
= B.recall_p dst.LP.base (FB.frozen_until_at_least 4); // to recover liveness
  let dpos' = LP.copy_strong p src spos spos' dst dpos in
  let i = freeze_valid p dst dpos dpos' in
  i
