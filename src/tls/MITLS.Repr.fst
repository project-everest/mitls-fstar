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
module MITLS.Repr

(* Summary:

   This module provides the "base" type of several types that
   encapsulate the wire-format representations of TLS messages.

   Its main features are:

   1. A type `repr t b`: Given a backing array of bytes `b`
      (represented as a `slice` in the parlance of LowParse), `repr t
      b` stands for a representation of `t`-typed values in `b`.

   2. An abstract predicate `valid r h`, stating that memory state `h`
      contains a valid representation `r`. This predicate comes with a
      framing principle and SMT triggers for it.
*)
module LP = LowParse.Low.Base
module LS = LowParse.SLow.Base
module B = LowStar.Buffer
module HS = FStar.HyperStack
open FStar.Integers
module C = LowStar.ConstBuffer

/// A slice is a const uint_8* and a length.
///
/// It is a layer around LP.slice, effectively guaranteeing that no
/// writes are performed via this pointer.
///
/// It allows us to uniformly represent `repr t b` backed by either
/// mutable or immutable arrays.
noeq
type const_slice =
  | MkSlice:
      base:C.const_buffer LP.byte ->
      len:uint_32 {
        UInt32.v len <= C.length base /\
        len <= LP.validator_max_length
      } ->
      const_slice

[@(deprecated "use const_slice instead")]
let slice = const_slice

(* Some abbreviations *)
let mut_p = LowStar.Buffer.trivial_preorder LP.byte
let immut_p = LowStar.ImmutableBuffer.immutable_preorder LP.byte
let preorder (c:const_slice) = C.qbuf_pre (C.as_qbuf c.base)

let live h (b:const_slice) = LowStar.ConstBuffer.live h b.base
let loc (b:const_slice) = LowStar.ConstBuffer.loc_buffer b.base
let as_seq h (b:const_slice) = LowStar.ConstBuffer.as_seq h b.base

(* conversion between LP.slices and const_slices *)
let of_slice (x:LP.slice mut_p mut_p { LP.(x.len <= LP.validator_max_length) })
  : Tot const_slice
  = MkSlice (C.of_buffer LP.(x.base)) LP.(x.len)

let of_islice (x:LP.slice immut_p immut_p { LP.(x.len <= LP.validator_max_length) })
  : Tot const_slice
  = MkSlice (C.of_ibuffer LP.(x.base)) LP.(x.len)

let to_slice (x:const_slice)
  : Tot (LP.slice (preorder x) (preorder x))
  = let b = C.cast x.base in
    let len = x.len in
    LP.({
       base = b;
       len = len
    })

/// `index b` is the type of valid indexes into `b`
let index (b:const_slice)= i:uint_32{ i <= b.len }

/// `strong_parser_kind`: We restrict our attention to the
/// representation of types whose parsers have the strong-prefix
/// property.
let strong_parser_kind =
    k:LP.parser_kind{
      LP.(k.parser_kind_subkind == Some ParserStrong)
    }


(*** Representation types ***)

/// `repr_meta t`: Each representation is associated with metadata
/// that records both
///  -- the parser that defines the wire-format used
///  -- an erased value represented by the wire format
///  -- the bytes of the wire format
noeq
type repr_meta (t:Type) = {
  parser_kind: strong_parser_kind;
  parser:LP.parser parser_kind t;
  value: t;
  repr_bytes: Seq.seq LP.byte
}

/// `repr t b`: The main type of this module.
///
///   * The slice `b` holds a representation of `t` in
///    `b.[start_pos, end_pos)`
///
///   * The representation is described by erased the `meta` field
noeq
type repr (t:Type) (b:const_slice) = {
  start_pos: index b;
  end_pos: i:index b {start_pos <= i /\ i <= b.len};
  meta: Ghost.erased (repr_meta t)
}


/// `repr_p`
///
/// One of the main ideas of `repr` is to index representation by
/// types rather than parsers that define wire-formats.
///
/// When manipulating reprs, the intention is for clients to be
/// agnostic to the specific wire formats used.
///
/// Nevertheless, at various points, we need to construct
/// representations from wire formats. At those points, the `repr_p`
/// type is useful, since it is a `repr` that is also indexed by a
/// parser.
let repr_p (t:Type) (b:const_slice) #k (parser:LP.parser k t) =
  r:repr t b {
    let meta = Ghost.reveal r.meta in
    meta.parser_kind == k /\
    meta.parser == parser
  }

(*** Validity ***)

/// `valid' r h`:
///   We define validity in two stages:
///
///   First, we provide `valid'`, a transparent definition and then
///   turn it `abstract` by the `valid` predicate just below.
///
///   Validity encapsulates three related LowParse notions:
///
///    1. That the underlying slice contains a valid wire-format
///    (`valid_pos`)
///
///    2. That the ghost value associated with the `repr` is the
///    parsed value of the wire format.
///
///    3. The bytes of the slice are indeed the representation of the
///    ghost value in wire format
let valid' (#t:Type) (#b:const_slice) (r:repr t b) (h:HS.mem)
  = let m = Ghost.reveal r.meta in
    let b = to_slice b in
    LP.valid_pos m.parser h b r.start_pos r.end_pos /\
    m.value == LP.contents m.parser h b r.start_pos /\
    m.repr_bytes == LP.bytes_of_slice_from_to h b r.start_pos r.end_pos


/// `valid`: abstract validity
abstract
let valid (#t:Type) (#b:const_slice) (r:repr t b) (h:HS.mem)
  = valid' r h


/// `reveal_valid`:
///   An explicit lemma exposes the definition of `valid`
let reveal_valid ()
  : Lemma (forall (t:Type) (b:const_slice) (r:repr t b) (h:HS.mem).
              {:pattern (valid #t #b r h)}
           valid #t #b r h <==> valid' #t #b r h)
  = ()

/// `fp r`: The memory footprint of a repr is the
///         sub-slice b.[from, to)
let fp #t (#b:const_slice) (r:repr t b)
  : GTot B.loc
  = LP.loc_slice_from_to (to_slice b) r.start_pos r.end_pos

/// `frame_valid`:
///    A framing principle for `valid r h`
///    It is invariant under footprint-preserving heap updates
let frame_valid #t #b (r:repr t b) (l:B.loc) (h0 h1:HS.mem)
  : Lemma
    (requires
      valid r h0 /\
      B.modifies l h0 h1 /\
      B.loc_disjoint (fp r) l)
    (ensures
      valid r h1)
    [SMTPat (valid r h1);
     SMTPat (B.modifies l h0 h1)]
  = B.modifies_buffer_from_to_elim LP.((to_slice b).base) r.start_pos r.end_pos l h0 h1


/// `value`: A convenience function to access the underlying value
/// represented
let value #t #b (r:repr t b)
  : GTot t
  = (Ghost.reveal r.meta).value

open FStar.HyperStack.ST

/// `to_bytes`: for intermediate purposes only, extract bytes from the repr
let to_bytes #t #b (r: repr t b)
  : Stack FStar.Bytes.bytes
    (requires fun h ->
      valid r h
    )
    (ensures fun h x h' ->
      B.modifies B.loc_none h h' /\
      FStar.Bytes.reveal x == (Ghost.reveal r.meta).repr_bytes /\
      FStar.Bytes.len x == r.end_pos - r.start_pos
    )
  = let len = r.end_pos - r.start_pos in
    let b' = C.sub b.base r.start_pos len in
    (* FIXME: FStar.Bytes does not cater to const buffers,
       but do we really care, this code is transitional anyway *)
    assume (C.qbuf_qual (C.as_qbuf b') == C.MUTABLE);
    FStar.Bytes.of_buffer len (C.cast b')

/// `mk b from to p`:
///    Constructing a `repr` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
let mk (b:LP.slice mut_p mut_p{ LP.(b.len <= validator_max_length) })
       (from to:index (of_slice b))
       (#k:strong_parser_kind) #t (parser:LP.parser k t)
  : Stack (repr_p t (of_slice b) parser)
    (requires fun h ->
      LP.valid_pos parser h b from to)
    (ensures fun h0 r h1 ->
      h0 == h1 /\
      valid r h1 /\
      r.start_pos = from /\
      r.end_pos = to /\
      value r == LP.contents parser h1 b from)
  = let h = get () in
    let m =
      let v = LP.contents parser h b from in
      Ghost.hide ({
        parser_kind = _;
        parser = parser;
        value = v;
        repr_bytes = LP.bytes_of_slice_from_to h b from to
      })
    in
    {
      start_pos = from;
      end_pos = to;
      meta = m
    }

/// `mk b from to p`:
///    Constructing a `repr` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
let mk_from_const_slice
         (b:const_slice)
         (from to:index b)
         (#k:strong_parser_kind) #t (parser:LP.parser k t)
  : Stack (repr_p t b parser)
    (requires fun h ->
      LP.valid_pos parser h (to_slice b) from to)
    (ensures fun h0 r h1 ->
      h0 == h1 /\
      valid r h1 /\
      r.start_pos = from /\
      r.end_pos = to /\
      value r == LP.contents parser h1 (to_slice b) from)
  = let h = get () in
    let b = to_slice b in
    let m =
      let v = LP.contents parser h b from in
      Ghost.hide ({
        parser_kind = _;
        parser = parser;
        value = v;
        repr_bytes = LP.bytes_of_slice_from_to h b from to
      })
    in
    {
      start_pos = from;
      end_pos = to;
      meta = m
    }

let mk_from_serialize
  (b:LP.slice mut_p mut_p{ LP.(b.len <= validator_max_length) })
  (from:index (of_slice b))
  (#k:strong_parser_kind) #t (#parser:LP.parser k t) (#serializer: LP.serializer parser)
  (serializer32: LS.serializer32 serializer) (size32: LS.size32 serializer)
  (x: t)
: Stack (option (repr_p t (of_slice b) parser))
    (requires fun h ->
      LP.live_slice h b)
    (ensures fun h0 r h1 ->
      B.modifies (LP.loc_slice_from b from) h0 h1 /\
      begin match r with
      | None ->
        (* not enough space in output slice *)
        Seq.length (LP.serialize serializer x) > FStar.UInt32.v (b.LP.len - from)
      | Some r ->
        valid r h1 /\
        r.start_pos == from /\
        value r == x
      end
    )
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
    let r = mk b from to parser in
    Some r
  end

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

/// `valid_if_live`: A pure predicate on `r:repr t b` that states that
/// so long as the underlying buffer is live in a given state `h`, that
/// `r` is valid in that state
let valid_if_live #t (#b:const_slice) (r:repr t b) =
  C.qbuf_qual (C.as_qbuf b.base) == C.IMMUTABLE /\
  (let i : I.ibuffer LP.byte = C.as_mbuf b.base in
   let m = Ghost.reveal r.meta in
   exists (h:HS.mem).{:pattern valid r h}
      i `I.value_is` Ghost.hide m.repr_bytes /\
      m.repr_bytes == B.as_seq h i /\
      valid r h /\
      (forall h'.
        C.live h' b.base /\
        B.as_seq h i `Seq.equal` B.as_seq h' i ==>
        valid r h'))

/// `stable_repr t b`: A representation that is valid if its buffer is
/// live
let stable_repr t b = r:repr t b { valid_if_live r }

/// `valid_if_live_intro` :
///    An internal lemma to introduce `valid_if_live`

// Note: the next proof is flaky and occasionally enters a triggering
// vortex with the notorious FStar.Seq.Properties.slice_slice
// Removing that from the context makes the proof instantaneous
#reset-options "--max_fuel 0 --max_ifuel 0 \
                --using_facts_from '* -FStar.Seq.Properties.slice_slice'"
let valid_if_live_intro #t (#b:const_slice) (r:repr t b) (h:HS.mem)
  : Lemma
    (requires (
      C.qbuf_qual (C.as_qbuf b.base) == C.IMMUTABLE /\
      valid r h /\
      (let i : I.ibuffer LP.byte = C.as_mbuf b.base in
       let m = Ghost.reveal r.meta in
       B.as_seq h i == m.repr_bytes /\
       i `I.value_is` Ghost.hide m.repr_bytes)))
    (ensures
      valid_if_live r)
  = let i : I.ibuffer LP.byte = C.as_mbuf b.base in
    let aux (h':HS.mem)
        : Lemma
          (requires
            C.live h' b.base /\
            B.as_seq h i `Seq.equal` B.as_seq h' i)
          (ensures
            valid r h')
          [SMTPat (valid r h')]
        = let m = Ghost.reveal r.meta in
          LP.valid_ext_intro m.parser h (to_slice b) r.start_pos h' (to_slice b) r.start_pos
    in
    ()

/// `recall_stable_repr` Main lemma: if the underlying buffer is live
///    then a stable repr is valid
let recall_stable_repr #t #b (r:stable_repr t b)
  : Stack unit
    (requires fun h ->
      C.live h b.base)
    (ensures fun h0 _ h1 ->
      h0 == h1 /\
      valid r h1)
  = let h1 = get () in
    let i = C.to_ibuffer b.base in
    let aux (h:HS.mem)
      : Lemma
        (requires
          valid r h /\
          B.as_seq h i == B.as_seq h1 i)
        (ensures
          valid r h1)
        [SMTPat (valid r h)]
      = let m = Ghost.reveal r.meta in
        LP.valid_ext_intro m.parser h (to_slice b) r.start_pos h1 (to_slice b) r.start_pos
     in
     let es =
       let m = Ghost.reveal r.meta in
       Ghost.hide m.repr_bytes
     in
     I.recall_value i es

/// `stash`: Main stateful operation
///    Copies a repr into a fresh stable repr
let stash (rgn:HS.rid) #t #b (r:repr t b)
  : ST (s:const_slice &
        r':stable_repr t s)
   (requires fun h ->
     valid r h)
   (ensures fun h0 (|s, r'|) h1 ->
     B.modifies B.loc_none h0 h1 /\
     valid r' h1 /\
     r.meta == r'.meta)
 = let r_len = r.end_pos - r.start_pos in
   let b_sub = C.sub b.base r.start_pos r_len in
   (*
    * AR: Should this be a precondition?
    *)
   assume (is_eternal_region rgn);
   (*
    * AR: Allocation functions in the buffer library require r_len > 0
    *     Should we maintain anyway that in a repr end_pos > start_pos?
    *)
   assume (r_len > 0ul);
   let buf' = I.igcmalloc_and_blit rgn (C.cast b_sub) 0ul r_len in
   let s = MkSlice (C.of_ibuffer buf') r_len in
   let h1 = get () in
   let _ =
     let m = Ghost.reveal r.meta in
     assert (LP.valid_pos m.parser h1 (to_slice b) r.start_pos r.end_pos)    ;
     LP.valid_ext_intro m.parser h1 (to_slice b) r.start_pos h1 (to_slice s) 0ul;
     assert (LP.valid_pos m.parser h1 (to_slice s) 0ul r_len)
   in
   let r' : repr t s = {
     start_pos = 0ul;
     end_pos = r_len;
     meta = r.meta
   }
   in
   assert (valid r' h1);
   valid_if_live_intro r' h1;
   (| s, r' |)
