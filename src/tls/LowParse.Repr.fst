(*
  Copyright 2015--2019 INRIA and Microsoft Corporation

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

  Authors: T. Ramananandro, A. Rastogi, N. Swamy, A. Fromherz
*)
module LowParse.Repr

module LP = LowParse.Low.Base
module LS = LowParse.SLow.Base
module B = LowStar.Buffer
module HS = FStar.HyperStack
module C = LowStar.ConstBuffer
module U32 = FStar.UInt32
module D = LowStar.Native.DynamicRegion

open FStar.Integers
open FStar.HyperStack.ST
module I = LowStar.ImmutableBuffer

(* Summary:

   A pointer-based representation type.

   See
   https://github.com/mitls/mitls-papers/wiki/The-Memory-Model-of-miTLS#pointer-based-transient-reprs

   Calling it LowParse.Ptr since it should eventually move to everparse/src/lowparse
 *)

/// `strong_parser_kind`: We restrict our attention to the
/// representation of types whose parsers have the strong-prefix
/// property.
let strong_parser_kind =
    k:LP.parser_kind{
      LP.(k.parser_kind_subkind == Some ParserStrong)
    }

let preorder (c:C.const_buffer LP.byte) = C.qbuf_pre (C.as_qbuf c)

let slice_of_const_buffer (b:C.const_buffer LP.byte) (len:uint_32{U32.v len <= C.length b})
  : LP.slice (preorder b) (preorder b)
  = let b = C.cast b in
    LP.({
       base = b;
       len = len
    })

let mut_p = LowStar.Buffer.trivial_preorder LP.byte


/// A slice is a const uint_8* and a length.
///
/// It is a layer around LP.slice, effectively guaranteeing that no
/// writes are performed via this pointer.
///
/// It allows us to uniformly represent `ptr t` backed by either
/// mutable or immutable arrays.
noeq
type const_slice =
  | MkSlice:
      base:C.const_buffer LP.byte ->
      slice_len:uint_32 {
        UInt32.v slice_len <= C.length base /\
        slice_len <= LP.validator_max_length
      } ->
      const_slice

let to_slice (x:const_slice)
  : Tot (LP.slice (preorder x.base) (preorder x.base))
  = slice_of_const_buffer x.base x.slice_len

let of_slice (x:LP.slice mut_p mut_p {x.LP.len <= LP.validator_max_length} )
  : Tot const_slice
  = let b = C.of_buffer x.LP.base in
    let len = x.LP.len in
    MkSlice b len


(*** Pointer-based Representation types ***)

/// `meta t`: Each representation is associated with
/// specification metadata that records
///
///  -- the parser(s) that defines its wire format
///  -- the represented value
///  -- the bytes of its wire format
///
///  We retain both the value and its wire format for convenience.
///
///  An alternative would be to also retain here a serializer and then
///  compute the bytes when needed from the serializer. But that's a
///  bit heavy
[@erasable]
noeq
type meta (t:Type) = {
  parser_kind: strong_parser_kind;
  parser:LP.parser parser_kind t;
  parser32:LS.parser32 parser;
  v: t;
  len: uint_32;
  repr_bytes: Seq.lseq LP.byte (U32.v len);
  meta_ok: squash (LowParse.Spec.Base.parse parser repr_bytes == Some (v, U32.v len) /\
                   0ul < len /\
                   len < LP.validator_max_length)
}

/// `repr_ptr t`: The main type of this module.
///
///   * The const pointer `b` refers to a representation of `t`
///
///   * The representation is described by erased the `meta` field
///
/// Temporary fields:
///
///   * At this stage, we also keep a real high-level value (vv). We
///     plan to gradually access instead its ghost (.meta.v) and
///     eventually get rid of it to lower implicit heap allocations.
///
///   * We also retain a concrete length field to facilitate using the
///     LowParse APIs for accessors and jumpers, which are oriented
///     towards using slices rather than pointers. As those APIs
///     change, we will remove the length field.
noeq
type repr_ptr (t:Type) =
  | Ptr: b:C.const_buffer LP.byte ->
         meta:meta t ->
         vv:t ->
         length:U32.t { U32.v meta.len == C.length b /\
                       meta.len == length /\
                       vv == meta.v } ->
       repr_ptr t

let region_of #t (p:repr_ptr t) : GTot HS.rid = B.frameOf (C.cast p.b)

let value #t (p:repr_ptr t) : GTot t = p.meta.v

let repr_ptr_p (t:Type) (#k:strong_parser_kind) (parser:LP.parser k t) =
  p:repr_ptr t{ p.meta.parser_kind == k /\ p.meta.parser == parser }

let slice_of_repr_ptr #t (p:repr_ptr t)
  : GTot (LP.slice (preorder p.b) (preorder p.b))
  = slice_of_const_buffer p.b p.meta.len

let sub_ptr (p2:repr_ptr 'a) (p1: repr_ptr 'b) =
  exists pos len. Ptr?.b p2 `C.const_sub_buffer pos len` Ptr?.b p1

let intro_sub_ptr (x:repr_ptr 'a) (y:repr_ptr 'b) (from to:uint_32)
  : Lemma
    (requires
       to >= from /\
       Ptr?.b x `C.const_sub_buffer from (to - from)` Ptr?.b y)
    (ensures
      x `sub_ptr` y)
  = ()

/// TEMPORARY: DO NOT USE THIS FUNCTION UNLESS YOU REALLY HAVE SOME
/// SPECIAL REASON FOR IT
///
/// It is meant to support migration towards an EverParse API that
/// will eventually provide accessors and jumpers for pointers rather
/// than slices
let temp_slice_of_repr_ptr #t (p:repr_ptr t)
  : Tot (LP.slice (preorder p.b) (preorder p.b))
  = slice_of_const_buffer p.b p.length

(*** Validity ***)

/// `valid' r h`:
///   We define validity in two stages:
///
///   First, we provide `valid'`, a transparent definition and then
///   turn it `abstract` by the `valid` predicate just below.
///
///   Validity encapsulates three related LowParse properties:notions:
///
///    1. The underlying pointer contains a valid wire-format
///    (`valid_pos`)
///
///    2. The ghost value associated with the `repr` is the
///        parsed value of the wire format.
///
///    3. The bytes of the slice are indeed the representation of the
///       ghost value in wire format
unfold
let valid_slice (#t:Type) (#r #s:_) (slice:LP.slice r s) (meta:meta t) (h:HS.mem) =
  LP.valid_content_pos meta.parser h slice 0ul meta.v meta.len /\
  meta.repr_bytes == LP.bytes_of_slice_from_to h slice 0ul meta.len

unfold
let valid' (#t:Type) (p:repr_ptr t) (h:HS.mem) =
  let slice = slice_of_const_buffer p.b p.meta.len in
  valid_slice slice p.meta h

/// `valid`: abstract validity
abstract
let valid (#t:Type) (p:repr_ptr t) (h:HS.mem)
  = valid' p h

/// `reveal_valid`:
///   An explicit lemma exposes the definition of `valid`
let reveal_valid ()
  : Lemma (forall (t:Type) (p:repr_ptr t) (h:HS.mem).
              {:pattern (valid #t p h)}
           valid #t p h <==> valid' #t p h)
  = ()

/// `fp r`: The memory footprint of a repr_ptr is the underlying pointer
let fp #t (p:repr_ptr t)
  : GTot B.loc
  = C.loc_buffer p.b

/// `frame_valid`:
///    A framing principle for `valid r h`
///    It is invariant under footprint-preserving heap updates
let frame_valid #t (p:repr_ptr t) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      valid p h0 /\
      B.modifies l h0 h1 /\
      B.loc_disjoint (fp p) l)
    (ensures
      valid p h1)
    [SMTPat (valid p h1);
     SMTPat (B.modifies l h0 h1)]
  = ()

(***  Contructors ***)

/// `mk b from to p`:
///    Constructing a `repr_ptr` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
#set-options "--z3rlimit 20"
inline_for_extraction
let mk_from_const_slice
         (b:const_slice)
         (from to:uint_32)
         (#k:strong_parser_kind) #t (#parser:LP.parser k t)
         (parser32:LS.parser32 parser)
  : Stack (repr_ptr_p t parser)
    (requires fun h ->
      LP.valid_pos parser h (to_slice b) from to)
    (ensures fun h0 p h1 ->
      B.(modifies loc_none h0 h1) /\
      valid p h1 /\
      p.meta.v == LP.contents parser h1 (to_slice b) from /\
      p.b `C.const_sub_buffer from (to - from)` b.base)
  = let h = get () in
    let slice = to_slice b in
    assume (from =!= to);
    assume (to - from < LP.validator_max_length);
    LP.contents_exact_eq parser h slice from to;
    let meta :meta t = {
        parser_kind = _;
        parser = parser;
        parser32 = parser32;
        v = LP.contents parser h slice from;
        len = to - from;
        repr_bytes = LP.bytes_of_slice_from_to h slice from to;
        meta_ok = ()
    } in
    let sub_b = C.sub b.base from (to - from) in
    let value =
      // Compute [.v]; this code will eventually disappear
      let sub_b_bytes = FStar.Bytes.of_buffer (to - from) (C.cast sub_b) in
      let Some (v, _) = parser32 sub_b_bytes in
      v
    in
    let p = Ptr sub_b meta value (to - from) in
    let h1 = get () in
    let slice' = slice_of_const_buffer sub_b (to - from) in
    LP.valid_facts p.meta.parser h1 slice from; //elim valid_pos slice
    LP.valid_facts p.meta.parser h1 slice' 0ul; //intro valid_pos slice'
    p

/// `mk b from to p`:
///    Constructing a `repr_ptr` from a LowParse slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
inline_for_extraction
let mk #q
       (slice:LP.slice (C.q_preorder q LP.byte) (C.q_preorder q LP.byte){ slice.LP.len <= LP.validator_max_length })
       (from to:uint_32)
       (#k:strong_parser_kind) #t (#parser:LP.parser k t)
       (parser32:LS.parser32 parser)
  : Stack (repr_ptr_p t parser)
    (requires fun h ->
      LP.valid_pos parser h slice from to)
    (ensures fun h0 p h1 ->
      B.(modifies loc_none h0 h1) /\
      valid p h1 /\
      p.b `C.const_sub_buffer from (to - from)` (C.of_qbuf slice.LP.base) /\
      p.meta.v == LP.contents parser h1 slice from)
  = let c = MkSlice (C.of_qbuf slice.LP.base) slice.LP.len in
    mk_from_const_slice c from to parser32

/// A high-level constructor, taking a value instead of a slice.
///
/// Can we remove the `noextract` for the time being? Can we
/// `optimize` it so that vv is assigned x? It will take us a while to
/// lower all message writing.
inline_for_extraction
noextract
let mk_from_serialize
    (b:LP.slice mut_p mut_p{ LP.(b.len <= validator_max_length) })
    (from:uint_32 { from <= b.LP.len })
    (#k:strong_parser_kind) #t (#parser:LP.parser k t) (#serializer: LP.serializer parser)
    (parser32: LS.parser32 parser) (serializer32: LS.serializer32 serializer)
    (size32: LS.size32 serializer) (x: t)
  : Stack (option (repr_ptr_p t parser))
    (requires fun h ->
       LP.live_slice h b)
    (ensures fun h0 popt h1 ->
       B.modifies (LP.loc_slice_from b from) h0 h1 /\
       (match popt with
       | None ->
         (* not enough space in output slice *)
         Seq.length (LP.serialize serializer x) > FStar.UInt32.v (b.LP.len - from)
       | Some p ->
         let size = size32 x in
         valid p h1 /\
         U32.v from + U32.v size <= U32.v b.LP.len /\
         p.b == C.gsub (C.of_buffer b.LP.base) from size /\
         p.meta.v == x))
  = let size = size32 x in
    let len = b.LP.len - from in
    if len < size
    then None
    else begin
      let bytes = serializer32 x in
      let dst = B.sub b.LP.base from size in
      (if size > 0ul then FStar.Bytes.store_bytes bytes dst);
        let to = from + size in
      let h = get () in
      LP.serialize_valid_exact serializer h b x from to;
      let r = mk b from to parser32 in
      Some r
    end

(*** Destructors ***)


/// Computes the length in bytes of the representation
/// Using a LowParse "jumper"
let length #t (p: repr_ptr t) (j:LP.jumper p.meta.parser)
  : Stack U32.t
    (requires fun h ->
      valid p h)
    (ensures fun h n h' ->
      B.modifies B.loc_none h h' /\
      n == p.meta.len)
  = let s = temp_slice_of_repr_ptr p in
    (* TODO: Need to revise the type of jumpers to take a pointer as an argument, not a slice *)
    j s 0ul

/// `to_bytes`: for intermediate purposes only, extract bytes from the repr
let to_bytes #t (p: repr_ptr t) (len:uint_32)
  : Stack FStar.Bytes.bytes
    (requires fun h ->
      valid p h /\
      len == p.meta.len
    )
    (ensures fun h x h' ->
      B.modifies B.loc_none h h' /\
      FStar.Bytes.reveal x == p.meta.repr_bytes /\
      FStar.Bytes.len x == p.meta.len
    )
  = FStar.Bytes.of_buffer len (C.cast p.b)


(*** Stable Representations ***)

(*
   By copying a representation into an immutable buffer `i`,
   we obtain a stable representation, which remains valid so long
   as the `i` remains live.

   We achieve this by relying on support for monotonic state provided
   by Low*, as described in the POPL '18 paper "Recalling a Witness"

   TODO: The feature also relies on an as yet unimplemented feature to
         atomically allocate and initialize a buffer to a chosen
         value. This will soon be added to the LowStar library.
*)


/// `valid_if_live`: A pure predicate on `r:repr_ptr t` that states that
/// so long as the underlying buffer is live in a given state `h`,
/// `p` is valid in that state
let valid_if_live #t (p:repr_ptr t) =
  C.qbuf_qual (C.as_qbuf p.b) == C.IMMUTABLE /\
  (let i : I.ibuffer LP.byte = C.as_mbuf p.b in
   let m = p.meta in
   i `I.value_is` Ghost.hide m.repr_bytes /\
   (exists (h:HS.mem).{:pattern valid p h}
      m.repr_bytes == B.as_seq h i /\
      valid p h /\
      (forall h'.
        C.live h' p.b /\
        B.as_seq h i `Seq.equal` B.as_seq h' i ==>
        valid p h')))

/// `stable_repr_ptr t`: A representation that is valid if its buffer is
/// live
let stable_repr_ptr t= p:repr_ptr t { valid_if_live p }


/// `valid_if_live_intro` :
///    An internal lemma to introduce `valid_if_live`

// Note: the next proof is flaky and occasionally enters a triggering
// vortex with the notorious FStar.Seq.Properties.slice_slice
// Removing that from the context makes the proof instantaneous
#push-options "--max_ifuel 1 --initial_ifuel 1 \
                --using_facts_from '* -FStar.Seq.Properties.slice_slice'"
let valid_if_live_intro #t (r:repr_ptr t) (h:HS.mem)
  : Lemma
    (requires (
      C.qbuf_qual (C.as_qbuf r.b) == C.IMMUTABLE /\
      valid r h /\
      (let i : I.ibuffer LP.byte = C.as_mbuf r.b in
       let m = r.meta in
       B.as_seq h i == m.repr_bytes /\
       i `I.value_is` Ghost.hide m.repr_bytes)))
    (ensures
      valid_if_live r)
  = let i : I.ibuffer LP.byte = C.as_mbuf r.b in
    let aux (h':HS.mem)
        : Lemma
          (requires
            C.live h' r.b /\
            B.as_seq h i `Seq.equal` B.as_seq h' i)
          (ensures
            valid r h')
          [SMTPat (valid r h')]
        = let m = r.meta in
          LP.valid_ext_intro m.parser h (slice_of_repr_ptr r) 0ul h' (slice_of_repr_ptr r) 0ul
    in
    ()

let sub_ptr_stable (#t0 #t1:_) (r0:repr_ptr t0) (r1:repr_ptr t1) (h:HS.mem)
  : Lemma
    (requires
      r0 `sub_ptr` r1 /\
      valid_if_live r1 /\
      valid r1 h /\
      valid r0 h)
    (ensures
      valid_if_live r0 /\
      (let b0 = C.cast r0.b in
       let b1 = C.cast r1.b in
       B.frameOf b0 == B.frameOf b1 /\
      (D.region_lifetime_buf (B.frameOf b0) b1 ==>
       D.region_lifetime_buf (B.frameOf b0) b0)))
    [SMTPat (r0 `sub_ptr` r1);
     SMTPat (valid_if_live r1);
     SMTPat (valid r0 h)]
  = let b0 : I.ibuffer LP.byte = C.cast r0.b in
    let b1 : I.ibuffer LP.byte = C.cast r1.b in
    assert (I.value_is b1 (Ghost.hide r1.meta.repr_bytes));
    assert (Seq.length r1.meta.repr_bytes == B.length b1);
    let aux (i len:U32.t)
      : Lemma
        (requires
          r0.b `C.const_sub_buffer i len` r1.b)
        (ensures
          I.value_is b0 (Ghost.hide r0.meta.repr_bytes))
        [SMTPat (r0.b `C.const_sub_buffer i len` r1.b)]
      = I.sub_ptr_value_is b0 b1 h i len r1.meta.repr_bytes
    in
    D.region_lifetime_sub #_ #_ #_ #(I.immutable_preorder _) (B.frameOf b1) b1 b0;
    valid_if_live_intro r0 h

/// `recall_stable_repr_ptr` Main lemma: if the underlying buffer is live
///    then a stable repr_ptr is valid
let recall_stable_repr_ptr #t (r:stable_repr_ptr t)
  : Stack unit
    (requires fun h ->
      C.live h r.b)
    (ensures fun h0 _ h1 ->
      h0 == h1 /\
      valid r h1)
  = let h1 = get () in
    let i = C.to_ibuffer r.b in
    let aux (h:HS.mem)
      : Lemma
        (requires
          valid r h /\
          B.as_seq h i == B.as_seq h1 i)
        (ensures
          valid r h1)
        [SMTPat (valid r h)]
      = let m = r.meta in
        LP.valid_ext_intro m.parser h (slice_of_repr_ptr r) 0ul h1 (slice_of_repr_ptr r) 0ul
     in
     let es =
       let m = r.meta in
       Ghost.hide m.repr_bytes
     in
     I.recall_value i es

let is_stable_in_region #t (p:repr_ptr t) =
  let r = B.frameOf (C.cast p.b) in
  valid_if_live p /\
  B.frameOf (C.cast p.b) == r /\
  D.region_lifetime_buf r (C.cast p.b)

let stable_region_repr_ptr (r:D.drgn) (t:Type) =
  p:repr_ptr t {
    is_stable_in_region p /\
    B.frameOf (C.cast p.b) == D.rid_of_drgn r
  }

let recall_stable_region_repr_ptr #t (r:D.drgn) (p:stable_region_repr_ptr r t)
  : Stack unit
    (requires fun h ->
      HS.live_region h (D.rid_of_drgn r))
    (ensures fun h0 _ h1 ->
      h0 == h1 /\
      valid p h1)
  = D.recall_liveness_buf r (C.cast p.b);
    recall_stable_repr_ptr p

private
let ralloc_and_blit (r:D.drgn) (src:C.const_buffer LP.byte) (len:U32.t)
  : ST (b:C.const_buffer LP.byte)
    (requires fun h0 ->
      HS.live_region h0 (D.rid_of_drgn r) /\
      U32.v len == C.length src /\
      C.live h0 src)
    (ensures fun h0 b h1 ->
      let c = C.as_qbuf b in
      let s = Seq.slice (C.as_seq h0 src) 0 (U32.v len) in
      let r = D.rid_of_drgn r in
      C.qbuf_qual c == C.IMMUTABLE /\
      B.alloc_post_mem_common (C.to_ibuffer b) h0 h1 s /\
      C.to_ibuffer b `I.value_is` s /\
      D.region_lifetime_buf r (C.cast b) /\
      B.frameOf (C.cast b) == r)
  = let src_buf = C.cast src in
    let b : I.ibuffer LP.byte = D.ralloc_and_blit_buf r src_buf 0ul len in
    let h0 = get() in
    B.witness_p b (I.seq_eq (Ghost.hide (Seq.slice (B.as_seq h0 src_buf) 0 (U32.v len))));
    C.of_ibuffer b


/// `stash`: Main stateful operation
///    Copies a repr_ptr into a fresh stable repr_ptr in the given region
let stash (rgn:D.drgn) #t (r:repr_ptr t) (len:uint_32{len == r.meta.len})
  : ST (stable_region_repr_ptr rgn t)
   (requires fun h ->
     valid r h /\
     HS.live_region h (D.rid_of_drgn rgn))
   (ensures fun h0 r' h1 ->
     B.modifies B.loc_none h0 h1 /\
     valid r' h1 /\
     r.meta == r'.meta)
 = let buf' = ralloc_and_blit rgn r.b len in
   let s = MkSlice buf' len in
   let h = get () in
   let _ =
     let slice = slice_of_const_buffer r.b len in
     let slice' = slice_of_const_buffer buf' len in
     LP.valid_facts r.meta.parser h slice 0ul; //elim valid_pos slice
     LP.valid_facts r.meta.parser h slice' 0ul //intro valid_pos slice'
   in
   let p = Ptr buf' r.meta r.vv r.length in
   valid_if_live_intro p h;
   p

(*** Accessing fields of ptrs ***)

unfold
let field_accessor_post (#t1:Type) (p:repr_ptr t1)
                        (#k2: strong_parser_kind)
                        (#t2:Type)
                        (p2: LP.parser k2 t2)
                        (cl:LP.clens t1 t2) =
   fun h0 (q:repr_ptr_p t2 p2) h1 ->
      cl.LP.clens_cond p.meta.v /\
      B.modifies B.loc_none h0 h1 /\
      valid q h1 /\
      value q == cl.LP.clens_get (value p) /\
      q `sub_ptr` p /\
      region_of q == region_of p /\
      (is_stable_in_region p ==> is_stable_in_region q)

inline_for_extraction
let get_field #t1 (p:repr_ptr t1)
              (#k2: strong_parser_kind)
              (#t2: Type)
              (#p2: LP.parser k2 t2)
              (#cl: LP.clens t1 t2)
              (#g: LP.gaccessor p.meta.parser p2 cl)
              (acc:LP.accessor g)
              (jump:LP.jumper p2)
              (p2': LS.parser32 p2)
 : Stack (repr_ptr_p t2 p2)
     (requires fun h ->
       valid p h /\
       cl.LP.clens_cond p.meta.v)
     (ensures
       field_accessor_post p p2 cl)
  = let b = temp_slice_of_repr_ptr p in
    let pos = acc b 0ul in
    let pos_to = jump b pos in
    let q = mk b pos pos_to p2' in
    assert (q.b `C.const_sub_buffer pos (pos_to - pos)` p.b);
    q


(*** Positional representation types ***)

/// `index b` is the type of valid indexes into `b`
let index (b:const_slice)= i:uint_32{ i <= b.slice_len }

noeq
type repr_pos (t:Type) (b:const_slice) =
  | Pos: start_pos:index b ->
         meta:meta t ->
         vv_pos:t -> //temporary
         length:U32.t { //temporary
                        U32.v start_pos + U32.v meta.len <= U32.v b.slice_len /\
                        vv_pos == meta.v /\
                        length == meta.len } ->
         repr_pos t b

let value_pos #t #b (r:repr_pos t b) : GTot t = r.meta.v

let as_ptr_spec #t #b (p:repr_pos t b)
  : GTot (repr_ptr t)
  = Ptr (C.gsub b.base p.start_pos ((Pos?.meta p).len))
        (Pos?.meta p)
        (Pos?.vv_pos p)
        (Pos?.length p)


/// This is a variant of `sub` that takes an erased `len`
/// Should be able to add this to the buffer model
/// If not, we can use the `offset` function, which is less precise
assume
val sub (c:C.const_buffer 'a) (i:uint_32) (len:Ghost.erased uint_32)
  : Stack (C.const_buffer 'a)
    (requires fun h ->
      C.live h c /\
      U32.v i + U32.v (Ghost.reveal len) <= C.length c)
    (ensures fun h0 c' h1 ->
      let qc = C.as_qbuf c in
      let qc' = C.as_qbuf c' in
      h0 == h1 /\
      c' `C.const_sub_buffer i (Ghost.reveal len)` c)

let const_buffer_of_repr_pos #t #b (r:repr_pos t b)
  : GTot (C.const_buffer LP.byte)
  = C.gsub b.base r.start_pos r.meta.len

/// `repr_pos_p`, the analog of `repr_ptr_p`
let repr_pos_p (t:Type) (b:const_slice) #k (parser:LP.parser k t) =
  r:repr_pos t b {
    r.meta.parser_kind == k /\
    r.meta.parser == parser
  }

(*** Validity ***)
/// `valid`: abstract validity
let repr_pos_valid (#t:Type) (#b:const_slice) (r:repr_pos t b) (h:HS.mem)
  = valid (as_ptr_spec r) h /\
    C.live h b.base

/// `fp r`: The memory footprint of a repr_pos is the
///         sub-slice b.[from, to)
let fp_pos #t (#b:const_slice) (r:repr_pos t b)
  : GTot B.loc
  = fp (as_ptr_spec r)

/// `frame_valid`:
///    A framing principle for `valid r h`
///    It is invariant under footprint-preserving heap updates
let frame_repr_pos_valid #t #b (r:repr_pos t b) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      repr_pos_valid r h0 /\
      B.modifies l h0 h1 /\
      B.loc_disjoint (fp_pos r) l)
    (ensures
      repr_pos_valid r h1)
    [SMTPat (repr_pos_valid r h1);
     SMTPat (B.modifies l h0 h1)]
  = ()

(*** Operations on repr_pos ***)

/// Mostly just by inheriting operations on pointers
let as_ptr #t #b (r:repr_pos t b)
  : Stack (repr_ptr t)
    (requires fun h ->
      repr_pos_valid r h)
    (ensures fun h0 ptr h1 ->
      ptr == as_ptr_spec r /\
      h0 == h1)
  = let b = sub b.base r.start_pos (Ghost.hide r.meta.len) in
    let m = r.meta in
    let v = r.vv_pos in
    let l = r.length in
    Ptr b m v l

let as_repr_pos #t (b:const_slice) (from to:index b) (p:repr_ptr t)
  : Pure (repr_pos t b)
    (requires
      from <= to /\
      Ptr?.b p  == C.gsub b.base from (to - from))
    (ensures fun r ->
      p == as_ptr_spec r)
  = Pos from (Ptr?.meta p) (Ptr?.vv p) (Ptr?.length p)

/// `mk_repr_pos b from to p`:
///    Constructing a `repr_pos` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
inline_for_extraction
let mk_repr_pos (b:LP.slice mut_p mut_p{ LP.(b.len <= validator_max_length) })
                (from to:index (of_slice b))
                (#k:strong_parser_kind) #t (#parser:LP.parser k t)
                (parser32:LS.parser32 parser)
  : Stack (repr_pos_p t (of_slice b) parser)
    (requires fun h ->
      LP.valid_pos parser h b from to)
    (ensures fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      repr_pos_valid r h1 /\
      r.start_pos = from /\
      r.vv_pos == LP.contents parser h1 b from)
  = as_repr_pos (of_slice b) from to (mk b from to parser32)

/// `mk b from to p`:
///    Constructing a `repr_pos` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
inline_for_extraction
let mk_repr_pos_from_const_slice
         (b:const_slice)
         (from to:index b)
         (#k:strong_parser_kind) #t (#parser:LP.parser k t)
         (parser32:LS.parser32 parser)
  : Stack (repr_pos_p t b parser)
    (requires fun h ->
      LP.valid_pos parser h (to_slice b) from to)
    (ensures fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      repr_pos_valid r h1 /\
      r.start_pos = from /\
      r.vv_pos == LP.contents parser h1 (to_slice b) from)
  = as_repr_pos b from to (mk_from_const_slice b from to parser32)

/// A high-level constructor, taking a value instead of a slice.
///
/// Can we remove the `noextract` for the time being? Can we
/// `optimize` it so that vv is assigned x? It will take us a while to
/// lower all message writing.
inline_for_extraction
noextract
let mk_repr_pos_from_serialize
  (b:LP.slice mut_p mut_p{ LP.(b.len <= validator_max_length) })
  (from:index (of_slice b))
  (#k:strong_parser_kind) #t (#parser:LP.parser k t) (#serializer: LP.serializer parser)
  (parser32: LS.parser32 parser) (serializer32: LS.serializer32 serializer)
  (size32: LS.size32 serializer) (x: t)
: Stack (option (repr_pos_p t (of_slice b) parser))
    (requires fun h ->
      LP.live_slice h b)
    (ensures fun h0 r h1 ->
      B.modifies (LP.loc_slice_from b from) h0 h1 /\
      begin match r with
      | None ->
        (* not enough space in output slice *)
        Seq.length (LP.serialize serializer x) > FStar.UInt32.v (b.LP.len - from)
      | Some r ->
        repr_pos_valid r h1 /\
        r.start_pos == from /\
        r.vv_pos == x
      end
    )
= let size = size32 x in
  match (mk_from_serialize b from parser32 serializer32 size32 x) with
  | None -> None
  | Some p -> Some (as_repr_pos (of_slice b) from (from + size) p)

/// Accessors on positional reprs


// unfold
// let field_accessor_post (#t1:Type) (p:repr_ptr t1)
//                         (#k2: strong_parser_kind)
//                         (#t2:Type)
//                         (p2: LP.parser k2 t2)
//                         (cl:LP.clens t1 t2) =
//    fun h0 (q:repr_ptr_p t2 p2) h1 ->
//       cl.LP.clens_cond p.meta.v /\
//       B.modifies B.loc_none h0 h1 /\
//       valid q h1 /\
//       value q == cl.LP.clens_get (value p) /\
//       q `sub_ptr` p /\
//       region_of q == region_of p /\
//       (is_stable_in_region p ==> is_stable_in_region q)

inline_for_extraction
let get_field_pos (#b:const_slice) #t1 (pp:repr_pos t1 b)
                  (#k2: strong_parser_kind)
                  (#t2: Type)
                  (#p2: LP.parser k2 t2)
                  (#cl: LP.clens t1 t2)
                  (#g: LP.gaccessor pp.meta.parser p2 cl)
                  (acc:LP.accessor g)
                  (jump:LP.jumper p2)
                  (p2': LS.parser32 p2)
 : Stack (repr_pos_p t2 b p2)
     (requires fun h ->
       repr_pos_valid pp h /\
       cl.LP.clens_cond pp.meta.v)
     (ensures fun h0 qq h1 ->
       B.modifies B.loc_none h0 h1 /\
       repr_pos_valid qq h1 /\
       value_pos qq == cl.LP.clens_get (value_pos pp))
 = let p = as_ptr pp in
   let bb = temp_slice_of_repr_ptr p in
   let pos = acc bb 0ul in
   let pos_to = jump bb pos in
   let q = mk bb pos pos_to p2' in
   let len = pos_to - pos in
   assert (Ptr?.b q `C.const_sub_buffer pos len` Ptr?.b p);
   as_repr_pos b (pp.start_pos + pos) (pp.start_pos + pos + len) q
