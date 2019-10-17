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
module LowParse.Ptr

module LP = LowParse.Low.Base
module LS = LowParse.SLow.Base
module B = LowStar.Buffer
module HS = FStar.HyperStack
module C = LowStar.ConstBuffer
module U32 = FStar.UInt32
open FStar.Integers
open FStar.HyperStack.ST

(* Summary:

   A pointer-based representation type.

   See https://github.com/mitls/mitls-papers/wiki/The-Memory-Model-of-miTLS#pointer-based-transient-reprs

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

(*** Representation types ***)

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
  meta_ok: squash (LowParse.Spec.Base.parse parser repr_bytes == Some (v, U32.v len))
}

/// `ptr t`: The main type of this module.
///
///   * The const pointer `b` refers to a representation of `t`
///
///   * The representation is described by erased the `meta` field
///
///   * At this stage, we also keep a real high-level value (vv). We
///     plan to gradually access instead its ghost (.meta.v) and
///     eventually get rid of it to lower implicit heap allocations.
noeq
type ptr (t:Type) = {
  b : C.const_buffer LP.byte;
  meta: meta t;
  value: t;
  ptr_ok: squash (U32.v meta.len == C.length b /\
                  value == meta.v)
}

let ptr_p (t:Type) (#k:strong_parser_kind) (parser:LP.parser k t) =
  p:ptr t{ p.meta.parser_kind == k /\ p.meta.parser == parser }

let slice_of_ptr #t (p:ptr t) 
  : GTot (LP.slice (preorder p.b) (preorder p.b))
  = slice_of_const_buffer p.b p.meta.len

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
  LP.valid_pos meta.parser h slice 0ul meta.len /\
  meta.repr_bytes == LP.bytes_of_slice_from_to h slice 0ul meta.len

unfold 
let valid' (#t:Type) (p:ptr t) (h:HS.mem) =
  let slice = slice_of_const_buffer p.b p.meta.len in
  valid_slice slice p.meta h

/// `valid`: abstract validity
abstract
let valid (#t:Type) (p:ptr t) (h:HS.mem)
  = valid' p h

/// `reveal_valid`:
///   An explicit lemma exposes the definition of `valid`
let reveal_valid ()
  : Lemma (forall (t:Type) (p:ptr t) (h:HS.mem).
              {:pattern (valid #t p h)}
           valid #t p h <==> valid' #t p h)
  = ()

/// `fp r`: The memory footprint of a ptr is the underlying pointer
let fp #t (p:ptr t)
  : GTot B.loc
  = C.loc_buffer p.b

/// `frame_valid`:
///    A framing principle for `valid r h`
///    It is invariant under footprint-preserving heap updates
let frame_valid #t (p:ptr t) (l:B.loc) (h0 h1:HS.mem)
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
  = let b = C.cast x.base in
    let len = x.slice_len in
    LP.({
       base = b;
       len = len
    })

let of_slice (x:LP.slice mut_p mut_p {x.LP.len <= LP.validator_max_length} )
  : Tot const_slice
  = let b = C.of_buffer x.LP.base in
    let len = x.LP.len in
    MkSlice b len
    
assume
val of_mbuffer: #p:_ -> #q:_ -> l:UInt32.t -> buf:B.mbuffer LP.byte p q -> Stack (b:FStar.Bytes.bytes{FStar.Bytes.length b = UInt32.v l})
  (requires (fun h0 -> B.live h0 buf))
  (ensures  (fun h0 b h1 -> B.(modifies loc_none h0 h1) /\ b = FStar.Bytes.hide (B.as_seq h0 buf)))

/// `mk b from to p`:
///    Constructing a `ptr` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
#set-options "--z3rlimit 20"
inline_for_extraction
let mk_from_const_slice
         (b:const_slice)
         (from to:uint_32)
         (#k:strong_parser_kind) #t (#parser:LP.parser k t)
         (parser32:LS.parser32 parser)
  : Stack (ptr_p t parser)
    (requires fun h ->
      LP.valid_pos parser h (to_slice b) from to)
    (ensures fun h0 p h1 ->
      B.(modifies loc_none h0 h1) /\
      valid p h1 /\
      p.meta.v == LP.contents parser h1 (to_slice b) from /\
      p.b `C.const_sub_buffer from (to - from)` b.base)
  = let h = get () in
    let slice = to_slice b in
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
      let sub_b_bytes = of_mbuffer (to - from) (C.cast sub_b) in
      let Some (v, _) = parser32 sub_b_bytes in
      v
    in
    let p = {
      b = sub_b;
      meta = meta;
      value = value;
      ptr_ok = ()
    } in
    let h1 = get () in
    let slice' = slice_of_const_buffer sub_b (to - from) in
    LP.valid_facts p.meta.parser h1 slice from; //elim valid_pos slice
    LP.valid_facts p.meta.parser h1 slice' 0ul; //intro valid_pos slice'
    p

/// `mk b from to p`:
///    Constructing a `ptr` from a LowParse slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
inline_for_extraction
let mk (slice:LP.slice mut_p mut_p{ slice.LP.len <= LP.validator_max_length })
       (from to:uint_32)
       (#k:strong_parser_kind) #t (#parser:LP.parser k t)
       (parser32:LS.parser32 parser)
  : Stack (ptr_p t parser)
    (requires fun h ->
      LP.valid_pos parser h slice from to)
    (ensures fun h0 p h1 ->
      B.(modifies loc_none h0 h1) /\
      valid p h1 /\
      p.b `C.const_sub_buffer from (to - from)` (C.of_buffer slice.LP.base) /\
      p.meta.v == LP.contents parser h1 slice from)
  = let c = MkSlice (C.of_buffer slice.LP.base) slice.LP.len in
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
  : Stack (option (ptr_p t parser))
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

/// `to_bytes`: for intermediate purposes only, extract bytes from the repr
let to_bytes #t (p: ptr t) (len:uint_32)
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
  = of_mbuffer len (C.cast p.b)


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

module I = LowStar.ImmutableBuffer

/// `valid_if_live`: A pure predicate on `r:ptr t` that states that
/// so long as the underlying buffer is live in a given state `h`,
/// `p` is valid in that state
let valid_if_live #t (p:ptr t) =
  C.qbuf_qual (C.as_qbuf p.b) == C.IMMUTABLE /\
  (let i : I.ibuffer LP.byte = C.as_mbuf p.b in
   let m = p.meta in
   exists (h:HS.mem).{:pattern valid p h}
      i `I.value_is` Ghost.hide m.repr_bytes /\
      m.repr_bytes == B.as_seq h i /\
      valid p h /\
      (forall h'.
        C.live h' p.b /\
        B.as_seq h i `Seq.equal` B.as_seq h' i ==>
        valid p h'))

/// `stable_ptr t`: A representation that is valid if its buffer is
/// live
let stable_ptr t= p:ptr t { valid_if_live p }

/// `valid_if_live_intro` :
///    An internal lemma to introduce `valid_if_live`

// Note: the next proof is flaky and occasionally enters a triggering
// vortex with the notorious FStar.Seq.Properties.slice_slice
// Removing that from the context makes the proof instantaneous
#push-options "--max_ifuel 1 --initial_ifuel 1 \
                --using_facts_from '* -FStar.Seq.Properties.slice_slice'"
let valid_if_live_intro #t (r:ptr t) (h:HS.mem)
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
          LP.valid_ext_intro m.parser h (slice_of_ptr r) 0ul h' (slice_of_ptr r) 0ul
    in
    ()

/// `recall_stable_ptr` Main lemma: if the underlying buffer is live
///    then a stable ptr is valid
let recall_stable_ptr #t (r:stable_ptr t)
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
        LP.valid_ext_intro m.parser h (slice_of_ptr r) 0ul h1 (slice_of_ptr r) 0ul
     in
     let es =
       let m = r.meta in
       Ghost.hide m.repr_bytes
     in
     I.recall_value i es
     
module D = LowStar.Native.DynamicRegion

(*
 * Unlike other allocation functions in this module,
 *   this function (and other flavors of alloc_and_blit) don't provide the witnessed contents
 *   as the refinement of the return type
 * This is because the contents depend on the input memory (== the contents of src)
 *)
let ralloc_and_blit (r:D.drgn) (src:C.const_buffer LP.byte) (len:U32.t)
  : ST (b:C.const_buffer LP.byte)
    (requires fun h0 ->
      HS.live_region h0 (D.rid_of_drgn r) /\
      U32.v len == C.length src /\
      C.live h0 src)
    (ensures fun h0 b h1 ->
      let c = C.as_qbuf b in
      let s = Seq.slice (C.as_seq h0 src) 0 (U32.v len) in
      C.qbuf_qual c == C.IMMUTABLE /\
      B.alloc_post_mem_common (C.to_ibuffer b) h0 h1 s /\
      C.to_ibuffer b `I.value_is` s /\
      D.region_lifetime_buf r (C.cast b) /\
      B.frameOf (C.cast b) == (D.rid_of_drgn r))
  = let src_buf = C.cast src in
    let b : I.ibuffer LP.byte = D.ralloc_and_blit_buf r src_buf 0ul len in
    let h0 = get() in
    B.witness_p b (I.seq_eq (Ghost.hide (Seq.slice (B.as_seq h0 src_buf) 0 (U32.v len))));
    C.of_ibuffer b


/// `stash`: Main stateful operation
///    Copies a ptr into a fresh stable ptr in the given region
let stash (rgn:D.drgn) #t (r:ptr t) (len:uint_32{len > 0ul /\ len == r.meta.len /\ len < LP.validator_max_length}) 
          #k (#p:LP.parser k t) (q:LS.parser32 p { k == r.meta.parser_kind /\ p == r.meta.parser /\ q == r.meta.parser32 })
  : ST (r':stable_ptr t)
   (requires fun h ->
     valid r h /\
     HS.live_region h (D.rid_of_drgn rgn))
   (ensures fun h0 r' h1 ->
     B.modifies B.loc_none h0 h1 /\
     valid r' h1 /\
     r.meta == r'.meta /\
     D.region_lifetime_buf rgn (C.cast r'.b) /\
     B.frameOf (C.cast r'.b) == (D.rid_of_drgn rgn))
 = let buf' = ralloc_and_blit rgn r.b len in
   let s = MkSlice buf' len in
   let h = get () in
   let _ = 
     let slice = slice_of_const_buffer r.b len in
     let slice' = slice_of_const_buffer buf' len in
     LP.valid_facts r.meta.parser h slice 0ul; //elim valid_pos slice
     LP.valid_facts r.meta.parser h slice' 0ul //intro valid_pos slice'
   in
   let p = {
     b = buf';
     meta = r.meta;
     value = r.value;
     ptr_ok = ()
   } in
   valid_if_live_intro p h;
   p
