module MITLS.Repr
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
open FStar.Integers

let index (b:LP.slice 'p 'q) = i:uint_32{ i <= LP.(b.len) }

assume
val rewritable (#p #q:_) (out:LP.slice p q) (from to:index out) (h:HS.mem) : prop

let strong_parser_kind =
    k:LP.parser_kind{LP.(k.parser_kind_subkind == Some ParserStrong)}

noeq
type repr_meta (t:Type) = {
  parser_kind: strong_parser_kind;
  parser:LP.parser parser_kind t; //erased anyway
  value: t;
}

noeq
type repr #p #q (t:Type) (b:LP.slice p q) = {
  start_pos: index b;
  end_pos: i:index b {start_pos <= i };
  meta: Ghost.erased (repr_meta t)
}


let value #p #q (#t:Type) (#b:LP.slice p q) (r:repr t b) 
  : GTot t
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
    LP.valid_pos parser h b from to

let valid' #t #p #q (#b:LP.slice p q) (r:repr t b) (h:HS.mem)
  : prop
  = let m = Ghost.reveal r.meta in
    valid_pos b m.parser r.start_pos r.end_pos h /\
    m.value == LP.contents m.parser h b r.start_pos

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

open FStar.HyperStack.ST
let mk #p #q (b:LP.slice p q) (from to:index b)
       (#k:strong_parser_kind) #t (parser:LP.parser k t)
  : Stack (repr_p t b parser)
    (requires valid_pos b parser from to)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      valid r h1)
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
