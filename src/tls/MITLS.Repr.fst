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
include LowParse.Ptr
module Ptr = LowParse.Ptr

/// `index b` is the type of valid indexes into `b`
let index (b:const_slice)= i:uint_32{ i <= b.slice_len }

module U32 = FStar.UInt32
(*** Representation types ***)
noeq
type repr (t:Type) (b:const_slice) = {
  start_pos: index b;
  meta:meta t;
  value: t;
  meta_ok:squash (U32.v start_pos + U32.v meta.len <= U32.v b.slice_len /\
                  value == meta.v)
}

open FStar.HyperStack.ST

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

let const_buffer_of_repr #t #b (r:repr t b)
  : GTot (C.const_buffer LP.byte)
  = C.gsub b.base r.start_pos r.meta.len


/// `repr_p`
///
/// One of the main ideas of `repr` is to index representation by
/// types rather than parsers that define their wire-formats.
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
    r.meta.parser_kind == k /\
    r.meta.parser == parser
  }

(*** Validity ***)
/// we just inherited the validity from pointers
let valid' (#t:Type) (#b:const_slice) (r:repr t b) (h:HS.mem)
  = let b = to_slice (Ptr.MkSlice (const_buffer_of_repr r) r.meta.len) in
    Ptr.valid_slice b r.meta h

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
  = C.loc_buffer (const_buffer_of_repr r)

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
  = ()

(*** Operations on reprs ***)

/// Mostly just by inheriting operations on pointers
let as_ptr #t #b (r:repr t b)
  : Stack (ptr t)
    (requires fun h ->
      LP.live_slice h (to_slice b))
    (ensures fun h0 ptr h1 ->
      ptr.b `C.const_sub_buffer r.start_pos r.meta.len` b.base /\
      ptr.Ptr.meta == r.meta /\
      h0 == h1 /\
      (valid r h1 <==> Ptr.valid ptr h1))
  = let b = sub b.base r.start_pos (Ghost.hide r.meta.len) in
    let m = r.meta in
    let v = r.value in
    let open Ptr in
    let p =
      { b = b;
        meta = m;
        value = v;
        ptr_ok = ()}
    in
    Ptr.reveal_valid ();
    p

let as_repr #t (b:const_slice) (from to:index b) (p:ptr t)
  : Pure (repr t b)
    (requires
      from <= to /\
      p.Ptr.b == C.gsub b.base from (to - from))
    (ensures fun r ->
      (forall h. Ptr.valid p h <==> valid r h))
  = Ptr.reveal_valid();
    {
      start_pos = from;
      meta = p.Ptr.meta;
      value = p.Ptr.value;
      meta_ok = ()
    }



/// `mk b from to p`:
///    Constructing a `repr` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
inline_for_extraction
let mk (b:LP.slice mut_p mut_p{ LP.(b.len <= validator_max_length) })
       (from to:index (of_slice b))
       (#k:strong_parser_kind) #t (#parser:LP.parser k t)
       (parser32:LS.parser32 parser)
  : Stack (repr_p t (of_slice b) parser)
    (requires fun h ->
      LP.valid_pos parser h b from to)
    (ensures fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      valid r h1 /\
      r.start_pos = from /\
      r.value == LP.contents parser h1 b from)
  = as_repr (of_slice b) from to (Ptr.mk b from to parser32)

/// `mk b from to p`:
///    Constructing a `repr` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
inline_for_extraction
let mk_from_const_slice
         (b:const_slice)
         (from to:index b)
         (#k:strong_parser_kind) #t (#parser:LP.parser k t)
         (parser32:LS.parser32 parser)
  : Stack (repr_p t b parser)
    (requires fun h ->
      LP.valid_pos parser h (to_slice b) from to)
    (ensures fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      valid r h1 /\
      r.start_pos = from /\
      r.value == LP.contents parser h1 (to_slice b) from)
  = as_repr b from to (Ptr.mk_from_const_slice b from to parser32)

/// A high-level constructor, taking a value instead of a slice.
///
/// Can we remove the `noextract` for the time being? Can we
/// `optimize` it so that vv is assigned x? It will take us a while to
/// lower all message writing.
inline_for_extraction
noextract
let mk_from_serialize
  (b:LP.slice mut_p mut_p{ LP.(b.len <= validator_max_length) })
  (from:index (of_slice b))
  (#k:strong_parser_kind) #t (#parser:LP.parser k t) (#serializer: LP.serializer parser)
  (parser32: LS.parser32 parser) (serializer32: LS.serializer32 serializer)
  (size32: LS.size32 serializer) (x: t)
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
        r.value == x
      end
    )
= let size = size32 x in
  match (mk_from_serialize b from parser32 serializer32 size32 x) with
  | None -> None
  | Some p -> Some (as_repr (of_slice b) from (from + size) p)
