module MITLS.Repr
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
open FStar.Integers

let index (b:LP.slice 'p 'q) = i:uint_32{ i <= LP.(b.len) }

noeq
type repr_meta (t:Type) = {
  parser_kind: (k:LP.parser_kind{LP.(k.parser_kind_subkind == Some ParserStrong)});
  parser:LP.parser parser_kind t; //erased anyway
  value: t;
}

noeq
type repr #p #q (t:Type) (b:LP.slice p q) = {
  start_pos: index b;
  end_pos: i:index b {start_pos <= i };
  meta: Ghost.erased (repr_meta t)
}

let repr_p #p #q (t:Type) (b:LP.slice p q) #k (parser:LP.parser k t) =
  r:repr t b {
    let meta = Ghost.reveal r.meta in
    meta.parser_kind == k /\
    meta.parser == parser
  }

let valid_pos #t #p #q (b:LP.slice p q) #k (parser:LP.parser k t) (from to:uint_32) (h:HS.mem) =
    LP.live_slice h b /\
    LP.valid_pos parser h b from to

let valid #t #p #q (#b:LP.slice p q) (r:repr t b) (h:HS.mem)
  : Type
  = let m = Ghost.reveal r.meta in
    valid_pos b m.parser r.start_pos r.end_pos h /\
    m.value == LP.contents m.parser h b r.start_pos

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
