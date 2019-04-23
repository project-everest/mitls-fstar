module MITLS.Repr.List
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
open FStar.Integers
module R = MITLS.Repr

let list_element_parser_kind =
  pk:R.strong_parser_kind{ LP.(pk.parser_kind_low > 0) }

noeq
type repr_meta (t:Type) = {
  parser_kind: list_element_parser_kind;
  parser:LP.parser parser_kind t; //erased anyway
  value: list t;
}

noeq
type repr #p #q (t:Type) (b:LP.slice p q) = {
  start_pos: R.index b;
  end_pos: i:R.index b {start_pos <= i };
  meta: Ghost.erased (repr_meta t)
}

let value #p #q (#t:Type) (#b:LP.slice p q) (r:repr t b)
  : GTot (list t)
  = (Ghost.reveal r.meta).value

let repr_p #p #q (t:Type) (b:LP.slice p q) #k (parser:LP.parser k t) =
  r:repr t b {
    let meta = Ghost.reveal r.meta in
    meta.parser_kind == k /\
    meta.parser == parser
  }

let valid_pos #t #p #q (b:LP.slice p q)
              #k (parser:LP.parser k t)
              (from to:uint_32)
              (h:HS.mem)
  : prop
  = LP.live_slice h b /\ //consequence of the next clause
    LP.valid_list parser h b from to

let valid' #t #p #q (#b:LP.slice p q) (r:repr t b) (h:HS.mem)
  : prop
  = let m = Ghost.reveal r.meta in
    valid_pos b m.parser r.start_pos r.end_pos h /\
    m.value == LP.contents_list m.parser h b r.start_pos r.end_pos

abstract
let valid #t #p #q (#b:LP.slice p q) (r:repr t b) (h:HS.mem)
  : prop
  = valid' r h

let reveal_valid ()
  : Lemma (forall t p q (b:LP.slice p q) (r:repr t b) (h:HS.mem).
              {:pattern (valid r h)}
           valid r h <==> valid' r h)
  = ()

let fp #t #p #q (#b:LP.slice p q) (r:repr t b) =
  LP.loc_slice_from_to b r.start_pos r.end_pos

let frame_valid #t #p #q (#b:LP.slice p q) (r:repr t b) (l:B.loc) (h0 h1:HS.mem)
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

////////////////////////////////////////////////////////////////////////////////
//Constructor:
//   Typically, promote a parsed slice to a repr
////////////////////////////////////////////////////////////////////////////////
open FStar.HyperStack.ST
let mk #p #q (b:LP.slice p q) (from to:R.index b)
       (#k:list_element_parser_kind) #t (parser:LP.parser k t)
  : Stack (repr_p t b parser)
    (requires valid_pos b parser from to)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      valid r h1)
  = let h = get () in
    let m =
      let v = LP.contents_list parser h b from to in
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

////////////////////////////////////////////////////////////////////////////////
//Constructor:
//   Format a list into a repr
//   Can be applied to a list literal and extracted by unrolling
////////////////////////////////////////////////////////////////////////////////
let format #p #q (b:LP.slice p q)
           #t (l:list t)
           (#k:list_element_parser_kind) (#parser:LP.parser k t) (#s:LP.serializer parser) (wt:LP.leaf_writer_weak s)
   : Stack (repr t b)
     (requires fun h ->
       LP.live_slice h b)
     (ensures fun h0 r h1 ->
       B.modifies (fp r) h0 h1 /\
       valid r h1 /\
       value r == l)
  = admit()

////////////////////////////////////////////////////////////////////////////////
//Copy constructor:
//   Copy a formatted list from one buffer into another
////////////////////////////////////////////////////////////////////////////////
let copy #p #q (#b:LP.slice p q) #t (r:repr t b)
         #p' #q' (out:LP.slice p' q') (from:R.index out)
   : Stack (repr t out)
     (requires fun h ->
       valid r h /\
       UInt32.v from + UInt32.v (r.end_pos - r.start_pos) <= UInt32.v LP.(out.len) /\
       R.rewritable out from (from + (r.end_pos - r.start_pos)) h /\
       LP.live_slice h out)
     (ensures fun h0 r' h1 ->
       B.modifies (fp r) h0 h1 /\
       valid r h1 /\
       value r == value r')
  = admit()


////////////////////////////////////////////////////////////////////////////////
//Accessors
////////////////////////////////////////////////////////////////////////////////
let length #p #q (b:LP.slice p q)
           #t (r:repr t b)
  : Stack uint_32
    (requires
      valid r)
    (ensures fun h0 v h1 ->
      B.modifies B.loc_none h0 h1 /\
      UInt32.v v == List.Tot.length (value r))
  = admit()

/// `index`: returns a representation of a list element
///  at the requested index
let index #p #q (b:LP.slice p q)
          #t (r:repr t b)
          (i:uint_32)
  : Stack (R.repr t b)
    (requires fun h ->
      valid r h /\
      UInt32.v i < List.Tot.length (value r))
    (ensures fun h0 v h1 ->
      B.modifies B.loc_none h0 h1 /\
      Some (R.value v) == List.Tot.nth (value r) (UInt32.v i))
  = admit()

//iterators

////////////////////////////////////////////////////////////////////////////////
//Freezing
////////////////////////////////////////////////////////////////////////////////
type i_repr #p #q (t:Type) (b:LP.slice p q) =
  i:repr t b {
    FStar.HyperStack.ST.witnessed (valid i) //not sure if we can define it so succinctly, but that would be nice
  }

//val freeze : repr -> i_repr
//val recall : i_repr -> r:repr  (ensures valid r)
