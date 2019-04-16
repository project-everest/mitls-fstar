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
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
open FStar.Integers

(* For now, we restrict `repr` to only use mutable slices as its
   backing u8 store.

   In the future, we may generalize this to support `const` slices,
   i.e., reprs backed by a slice whose buffer is either mutable or
   immutable.
*)

/// A wrapper around trivial preorders from LowStar.Buffer. The
/// explicit erasure here is because LowParse is working around a
/// known F* issue (#1694). It will eventually be removed.
let trivial_preorder : LP.srel LP.byte =
  Ghost.hide (LowStar.Buffer.trivial_preorder LP.byte)


/// A mutable slice: Eventually, we might just change this one
///   definition to be a const slice, multiplexing over mutable and
///   immutable LP.slices
let slice = LP.slice trivial_preorder trivial_preorder

/// `index b` is the type of valid indexes into `b`
let index (b:slice)= i:uint_32{ i <= LP.(b.len) }

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
noeq
type repr_meta (t:Type) = {
  parser_kind: strong_parser_kind;
  parser:LP.parser parser_kind t;
  value: t;
}

/// `repr t b`: The main type of this module.
///
///   * The slice `b` holds a representation of `t` in
///    `b.[start_pos, end_pos)`
///
///   * The representation is described by erased the `meta` field
noeq
type repr (t:Type) (b:slice) = {
  start_pos: index b;
  end_pos: i:index b {start_pos <= i };
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
let repr_p (t:Type) (b:slice) #k (parser:LP.parser k t) =
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
///   Validity encapsulate two related LowParse notions:
///
///    1. That the underlying slice contains a valid wire-format
///    (`valid_pos`)
///
///    2. That the ghost value associated with the `repr` is the
///    parsed value of the wire format.
///
let valid' (#t:Type) (#b:slice) (r:repr t b) (h:HS.mem)
  = let m = Ghost.reveal r.meta in
    LP.valid_pos m.parser h b r.start_pos r.end_pos /\
    m.value == LP.contents m.parser h b r.start_pos


/// `valid`: abstract validity
abstract
let valid (#t:Type) (#b:slice) (r:repr t b) (h:HS.mem)
  = valid' r h


/// `reveal_valid`:
///   An explicit lemma exposes the definition of `valid`
let reveal_valid ()
  : Lemma (forall (t:Type) (b:slice) (r:repr t b) (h:HS.mem).
              {:pattern (valid #t #b r h)}
           valid #t #b r h <==> valid' #t #b r h)
  = ()

/// `fp r`: The memory footprint of a repr is the
///         sub-slice b.[from, to)
let fp #t (#b:slice) (r:repr t b)
  : GTot B.loc
  = LP.loc_slice_from_to b r.start_pos r.end_pos

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
  = B.modifies_buffer_from_to_elim LP.(b.base) r.start_pos r.end_pos l h0 h1


/// `value`: A convenience function to access the underlying value
/// represented
let value #t #b (r:repr t b)
  : GTot t
  = (Ghost.reveal r.meta).value

open FStar.HyperStack.ST
/// `mk b from to p`:
///    Constructing a `repr` from a sub-slice
///      b.[from, to)
///    known to be valid for a given wire-format parser `p`
let mk (b:slice) (from to:index b)
       (#k:strong_parser_kind) #t (parser:LP.parser k t)
  : Stack (repr_p t b parser)
    (requires fun h ->
      LP.valid_pos parser h b from to)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
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
        value = v
      })
    in
    {
      start_pos = from;
      end_pos = to;
      meta = m
    }
