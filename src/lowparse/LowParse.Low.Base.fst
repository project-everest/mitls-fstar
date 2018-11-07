module LowParse.Low.Base
include LowParse.Spec.Base

module B = LowStar.Buffer
module M = LowStar.ModifiesPat
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module Cast = FStar.Int.Cast
module MA = LowParse.Math

inline_for_extraction
type buffer8 = B.buffer FStar.UInt8.t

noeq
type slice = {
  base: buffer8;
  len: (len: U32.t { len == B.len base } );
}

let live_slice (h: HS.mem) (s: slice) : GTot Type0 = B.live h s.base

abstract
let loc_slice_from (s: slice) (pos: U32.t) : GTot B.loc =
  if U32.v pos <= U32.v s.len
  then B.loc_buffer (B.gsub s.base pos (s.len `U32.sub` pos))
  else B.loc_none

abstract
let loc_includes_union_l_loc_slice_from (l1 l2: B.loc) (s: slice) (pos: U32.t) : Lemma
  (requires (B.loc_includes l1 (loc_slice_from s pos) \/ B.loc_includes l2 (loc_slice_from s pos)))
  (ensures (B.loc_includes (B.loc_union l1 l2) (loc_slice_from s pos)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (loc_slice_from s pos))]
= ()

abstract
let loc_slice_from_includes_r (s: slice) (pos: U32.t) : Lemma
  (B.loc_includes (B.loc_buffer s.base) (loc_slice_from s pos))
  [SMTPat (loc_slice_from s pos)]
= ()

abstract
let loc_slice_from_eq
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (U32.v pos <= U32.v s.len))
  (ensures (loc_slice_from s pos == B.loc_buffer (B.gsub s.base pos (s.len `U32.sub` pos))))
= ()

abstract
let loc_slice_from_includes_l
  (s: slice)
  (pos1 pos2: U32.t)
: Lemma
  (requires (U32.v pos1 <= U32.v pos2))
  (ensures (B.loc_includes (loc_slice_from s pos1) (loc_slice_from s pos2)))
  [SMTPat (B.loc_includes (loc_slice_from s pos1) (loc_slice_from s pos2))]
= ()

let valid'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: GTot Type0
= U32.v pos <= U32.v s.len /\
  live_slice h s /\
  Some? (parse p (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))))

abstract
let valid
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: GTot Type0
= valid' p h s pos

abstract
let valid_equiv
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Lemma
  (valid p h s pos <==> valid' p h s pos)
= ()

abstract
let valid_elim
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos))
  (ensures (valid' p h s pos))
  [SMTPat (valid p h s pos)]
= ()

let contents'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Ghost t
  (requires (valid' p h s pos))
  (ensures (fun _ -> True))
= let Some (v, _) = parse p (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))) in
  v

abstract
let contents
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Ghost t
  (requires (valid p h s pos))
  (ensures (fun _ -> True))
= contents' p h s pos

abstract
let contents_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos))
  (ensures (valid' p h s pos /\ contents p h s pos == contents' p h s pos))
= ()

abstract
let content_length
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
: Ghost nat
  (requires (valid p h sl pos))
  (ensures (fun res ->
    U32.v pos + res <= U32.v sl.len /\
    k.parser_kind_low <= res /\ (
    match k.parser_kind_high with
    | None -> True
    | Some max -> res <= max
  )))
= let Some (_, consumed) = parse p (B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos))) in
  consumed

abstract
let serialized_length
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Ghost nat
  (requires True)
  (ensures (fun res ->
    k.parser_kind_low <= res /\ (
    match k.parser_kind_high with
    | None -> True
    | Some max -> res <= max
  )))
= Seq.length (serialize s x)

abstract
let serialized_length_eq
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Lemma
  (serialized_length s x == Seq.length (serialize s x))
= ()

abstract
let content_length_eq
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
: Lemma
  (requires (valid p h sl pos))
  (ensures (content_length p h sl pos == serialized_length s (contents p h sl pos)))
= let b = B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)) in
  let Some (x, consumed) = parse p b in
  assert (x == contents p h sl pos);
  let ps' = parse p (serialize s x) in
  assert (serializer_correct p s);
  assert (Some? ps');
  assert (injective_precond p b (serialize s x))

abstract
let valid_frame
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (l: B.loc)
  (h': HS.mem)
: Lemma
  (requires (valid p h sl pos /\ B.modifies l h h' /\ B.loc_disjoint (loc_slice_from sl pos) l))
  (ensures (valid p h' sl pos /\ contents p h' sl pos == contents p h sl pos /\ content_length p h' sl pos == content_length p h sl pos))
  [SMTPatOr [
    [SMTPat (valid p h sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (valid p h' sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (contents p h sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (contents p h' sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (content_length p h sl pos); SMTPat (B.modifies l h h')];
    [SMTPat (content_length p h' sl pos); SMTPat (B.modifies l h h')];
  ]]
= ()

unfold 
let valid_pos
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (pos' : U32.t)
= valid p h sl pos /\
  U32.v pos + content_length p h sl pos == U32.v pos'

unfold 
let valid_content_pos
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos: U32.t)
  (x: t)
  (pos' : U32.t)
= valid_pos p h sl pos pos' /\
  contents p h sl pos == x

class validator_cls = {
  validator_max_length: U32.t;
}

inline_for_extraction
let validator [| validator_cls |] (#k: parser_kind) (#t: Type) (p: parser k t) : Tot Type =
  (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> live_slice h sl /\ U32.v pos <= U32.v sl.len /\ U32.v sl.len <= U32.v validator_max_length))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\ (
    if U32.v res <= U32.v validator_max_length
    then
      valid p h sl pos /\
      U32.v pos + content_length p h sl pos == U32.v res
    else
      (~ (valid p h sl pos))
  )))

inline_for_extraction
let jumper
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> valid p h sl pos))
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + content_length p h sl pos == U32.v pos'
  ))

let gaccessor
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (pre: t1 -> GTot Type0)
  (rel: t1 -> t2 -> GTot Type0)
: Tot Type
= (h: HS.mem) ->
  (sl: slice) ->
  (pos: U32.t) ->
  Ghost U32.t
  (requires (valid p1 h sl pos /\ pre (contents p1 h sl pos))) 
  (ensures (fun pos' ->
    valid p2 h sl pos' /\
    U32.v pos <= U32.v pos' /\
    rel (contents p1 h sl pos) (contents p2 h sl pos')
  ))

inline_for_extraction
let accessor
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (pre: t1 -> GTot Type0)
  (rel: t1 -> t2 -> GTot Type0)
  (g: gaccessor p1 p2 pre rel)
: Tot Type
= (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> valid p1 h sl pos /\ pre (contents p1 h sl pos))) 
  (ensures (fun h pos' h' ->
    B.modifies B.loc_none h h' /\
    pos' == g h sl pos
  ))

inline_for_extraction
let leaf_reader
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
: Tot Type
= (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack t
  (requires (fun h -> valid p h sl pos))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == contents p h sl pos
  ))

inline_for_extraction
let max_uint32 : U32.t = 4294967295ul

let max_uint32_correct
  (x: U32.t)
: Lemma
  (U32.v x <= U32.v max_uint32)
= ()

inline_for_extraction
let leaf_writer_weak
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> live_slice h sl /\ U32.v pos <= U32.v sl.len /\ U32.v sl.len < U32.v max_uint32))
  (ensures (fun h pos' h' ->
    B.modifies (loc_slice_from sl pos) h h' /\ (
    if pos' = max_uint32
    then U32.v pos + serialized_length s x > U32.v sl.len
    else valid_content_pos p h' sl pos x pos'
  )))

abstract
let loc_slice_from_to
  (sl: slice)
  (pos pos' : U32.t)
: GTot B.loc
= if U32.v pos' > U32.v sl.len
  then loc_slice_from sl pos
  else if U32.v pos > U32.v pos'
  then B.loc_none
  else B.loc_buffer (B.gsub sl.base pos (pos' `U32.sub` pos))

abstract
let loc_includes_union_l_loc_slice_from_to (l1 l2: B.loc) (s: slice) (pos pos' : U32.t) : Lemma
  (requires (B.loc_includes l1 (loc_slice_from_to s pos pos') \/ B.loc_includes l2 (loc_slice_from_to s pos pos')))
  (ensures (B.loc_includes (B.loc_union l1 l2) (loc_slice_from_to s pos pos')))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (loc_slice_from_to s pos pos'))]
= ()

abstract
let loc_slice_from_to_includes_r
  (sl: slice)
  (pos pos' : U32.t)
: Lemma
  (B.loc_includes (loc_slice_from sl pos) (loc_slice_from_to sl pos pos'))
  [SMTPat (loc_slice_from_to sl pos pos')]
= ()

abstract
let loc_slice_from_to_eq
  (sl: slice)
  (pos pos' : U32.t)
: Lemma
  (requires (U32.v pos <= U32.v pos' /\ U32.v pos' <= U32.v sl.len))
  (ensures (loc_slice_from_to sl pos pos' == B.loc_buffer (B.gsub sl.base pos (pos' `U32.sub` pos))))
= ()

abstract
let loc_slice_from_to_includes_l
  (sl: slice)
  (posl posr posl' posr' : U32.t)
: Lemma
  (requires (U32.v posl <= U32.v posl' /\ U32.v posr' <= U32.v posr))
  (ensures (loc_slice_from_to sl posl posr `B.loc_includes` loc_slice_from_to sl posl' posr'))
  [SMTPat (loc_slice_from_to sl posl posr `B.loc_includes` loc_slice_from_to sl posl' posr')]
= ()

abstract
let loc_slice_from_to_disjoint
  (sl: slice)
  (posl1 posr1 posl2 posr2 : U32.t)
: Lemma
  (requires (U32.v posr1 <= U32.v posl2))
  (ensures (B.loc_disjoint (loc_slice_from_to sl posl1 posr1) (loc_slice_from_to sl posl2 posr2)))
  [SMTPat (B.loc_disjoint (loc_slice_from_to sl posl1 posr1) (loc_slice_from_to sl posl2 posr2))]
= ()

abstract
let loc_slice_from_loc_slice_from_to_disjoint
  (sl: slice)
  (pos1 pos2 pos' : U32.t)
: Lemma
  (requires (U32.v pos2 <= U32.v pos'))
  (ensures (B.loc_disjoint (loc_slice_from_to sl pos1 pos2) (loc_slice_from sl pos')))
  [SMTPat (B.loc_disjoint (loc_slice_from_to sl pos1 pos2) (loc_slice_from sl pos'))]
= ()

inline_for_extraction
let leaf_writer_strong
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (x: t) ->
  (sl: slice) ->
  (pos: U32.t) ->
  HST.Stack U32.t
  (requires (fun h -> live_slice h sl /\ U32.v pos + serialized_length s x <= U32.v sl.len))
  (ensures (fun h pos' h' ->
    B.modifies (loc_slice_from_to sl pos pos') h h' /\
    valid_content_pos p h' sl pos x pos'
  ))

#set-options "--z3rlimit 16"

inline_for_extraction
let copy_strong
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: slice) // FIXME: length is useless here
  (spos spos' : U32.t)
  (dst: slice)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h src spos spos' /\ (
    let clen = content_length p h src spos in
    U32.v dpos + clen <= U32.v dst.len /\
    live_slice h dst /\
    B.loc_disjoint (loc_slice_from_to src spos spos') (loc_slice_from_to dst dpos (dpos `U32.add` (U32.uint_to_t clen)))
  )))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from_to dst dpos dpos') h h' /\
    valid_content_pos p h' dst dpos (contents p h src spos) dpos'
  ))
= let h0 = HST.get () in
  let len = spos' `U32.sub` spos in
  let src' = B.sub src.base spos len in
  let dst' = B.sub dst.base dpos len in
  B.blit src' 0ul dst' 0ul len;
  let h = HST.get () in
  [@inline_let] let dpos' = dpos `U32.add` len in
  assert (
    B.modifies (loc_slice_from_to dst dpos dpos') h0 h
  );
  assert (no_lookahead_on p (B.as_seq h0 (B.gsub src.base spos (src.len `U32.sub` spos))) (B.as_seq h (B.gsub dst.base dpos (dst.len `U32.sub` dpos))));
  assert (no_lookahead_on_postcond p (B.as_seq h0 (B.gsub src.base spos (src.len `U32.sub` spos))) (B.as_seq h (B.gsub dst.base dpos (dst.len `U32.sub` dpos))));
  assert (injective_precond p (B.as_seq h0 (B.gsub src.base spos (src.len `U32.sub` spos))) (B.as_seq h (B.gsub dst.base dpos (dst.len `U32.sub` dpos))));  
  dpos'

#reset-options

inline_for_extraction
let copy_weak_with_length
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (src: slice) // FIXME: length is useless here
  (spos spos' : U32.t)
  (dst: slice)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid_pos p h src spos spos' /\
    live_slice h dst /\
    U32.v dpos <= U32.v dst.len /\
    U32.v dst.len < U32.v max_uint32 /\
    B.loc_disjoint (loc_slice_from_to src spos spos') (loc_slice_from dst dpos)
  ))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from dst dpos) h h' /\ (
    if dpos' = max_uint32
    then
      U32.v dpos + content_length p h src spos > U32.v dst.len
    else
      valid_content_pos p h' dst dpos (contents p h src spos) dpos'
  )))
= if (dst.len `U32.sub` dpos) `U32.lt` (spos' `U32.sub` spos)
  then max_uint32
  else copy_strong p src spos spos' dst dpos

inline_for_extraction
let copy_weak
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (jmp: jumper p)
  (src: slice)
  (spos : U32.t)
  (dst: slice)
  (dpos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    valid p h src spos /\
    live_slice h dst /\
    U32.v dpos <= U32.v dst.len /\
    U32.v dst.len < U32.v max_uint32 /\
    B.loc_disjoint (loc_slice_from src spos) (loc_slice_from dst dpos)
  ))
  (ensures (fun h dpos' h' ->
    B.modifies (loc_slice_from dst dpos) h h' /\ (
    if dpos' = max_uint32
    then
      U32.v dpos + content_length p h src spos > U32.v dst.len
    else
      valid_content_pos p h' dst dpos (contents p h src spos) dpos'
  )))
= let spos' = jmp src spos in
  copy_weak_with_length p src spos spos' dst dpos


(* Case where we do not have the strong prefix property (e.g. lists): we need an extra length *)

let valid_exact'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0
= U32.v pos <= U32.v pos' /\
  U32.v pos' <= U32.v s.len /\
  live_slice h s /\ (
  let len' = pos' `U32.sub` pos in
  match parse p (B.as_seq h (B.gsub s.base pos len')) with
  | None -> False
  | Some (_, consumed) -> (consumed <: nat) == U32.v len'
  )

abstract
let valid_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0
= valid_exact' p h s pos pos'

abstract
let valid_exact_elim
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos'))
  (ensures (valid_exact' p h s pos pos'))
  [SMTPat (valid_exact p h s pos pos')]
= ()

abstract
let valid_exact_equiv
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (valid_exact p h s pos pos' <==> valid_exact' p h s pos pos')
= ()

let contents_exact'
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost t
  (requires (valid_exact' p h s pos pos'))
  (ensures (fun _ -> True))
= let (Some (v, _)) = parse p (B.as_seq h (B.gsub s.base pos (pos' `U32.sub` pos))) in
  v

abstract
let contents_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost t
  (requires (valid_exact p h s pos pos'))
  (ensures (fun _ -> True))
= contents_exact' p h s pos pos'

abstract
let contents_exact_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos'))
  (ensures (valid_exact' p h s pos pos' /\ contents_exact p h s pos pos' == contents_exact' p h s pos pos'))
= ()

abstract
let valid_exact_frame
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (valid_exact p h s pos pos' /\ B.modifies l h h' /\ B.loc_disjoint l (loc_slice_from_to s pos pos')))
  (ensures (valid_exact p h' s pos pos' /\ contents_exact p h' s pos pos' == contents_exact p h s pos pos'))
  [SMTPatOr [
    [SMTPat (valid_exact p h s pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (valid_exact p h' s pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (contents_exact p h s pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (contents_exact p h' s pos pos'); SMTPat (B.modifies l h h')];
  ]]
= ()

abstract
let valid_valid_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (valid p h s pos /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    let npos' = U32.v pos + content_length p h s pos in
    npos' <= U32.v s.len /\ (
    let pos' = U32.uint_to_t npos' in
    valid_exact p h s pos pos' /\
    contents_exact p h s pos pos' == contents p h s pos
  )))
= let npos' = U32.v pos + content_length p h s pos in
  assert (npos' <= U32.v s.len);
  let pos' = U32.uint_to_t npos' in
  assert (no_lookahead_on p (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))) (B.as_seq h (B.gsub s.base pos (pos' `U32.sub` pos))));
  assert (injective_precond p (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))) (B.as_seq h (B.gsub s.base pos (pos' `U32.sub` pos))));
  assert (injective_postcond p (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))) (B.as_seq h (B.gsub s.base pos (pos' `U32.sub` pos))))

abstract
let valid_pos_valid_exact
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_pos p h s pos pos' /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_exact p h s pos pos' /\
    contents_exact p h s pos pos' == contents p h s pos
  ))
= valid_valid_exact p h s pos

abstract
let valid_exact_valid
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s: slice)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_exact p h s pos pos' /\ k.parser_kind_subkind == Some ParserStrong))
  (ensures (
    valid_content_pos p h s pos (contents_exact p h s pos pos') pos'
  ))
= assert (no_lookahead_on p (B.as_seq h (B.gsub s.base pos (pos' `U32.sub`pos))) (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))));
  assert (injective_precond p (B.as_seq h (B.gsub s.base pos (pos' `U32.sub` pos))) (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))));
  assert (injective_postcond p (B.as_seq h (B.gsub s.base pos (pos' `U32.sub` pos))) (B.as_seq h (B.gsub s.base pos (s.len `U32.sub` pos))))

abstract
let valid_exact_ext_intro
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s1: slice)
  (pos1: U32.t)
  (pos1' : U32.t)
  (s2: slice)
  (pos2: U32.t)
  (pos2' : U32.t)
: Lemma
  (requires (
    valid_exact p h s1 pos1 pos1' /\
    live_slice h s2 /\
    U32.v pos1' - U32.v pos1 == U32.v pos2' - U32.v pos2 /\
    U32.v pos2' <= U32.v s2.len /\
    B.as_seq h (B.gsub s1.base pos1 (pos1' `U32.sub` pos1)) `Seq.equal` B.as_seq h (B.gsub s2.base pos2 (pos2' `U32.sub` pos2))
  ))
  (ensures (
    valid_exact p h s2 pos2 pos2' /\
    contents_exact p h s2 pos2 pos2' == contents_exact p h s1 pos1 pos1'
  ))
= ()

abstract
let valid_exact_ext_elim
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (h: HS.mem)
  (s1: slice)
  (pos1: U32.t)
  (pos1' : U32.t)
  (s2: slice)
  (pos2: U32.t)
  (pos2' : U32.t)
: Lemma
  (requires (
    valid_exact p h s1 pos1 pos1' /\
    valid_exact p h s2 pos2 pos2' /\
    contents_exact p h s1 pos1 pos1' == contents_exact p h s2 pos2 pos2'
  ))
  (ensures (
    U32.v pos2' - U32.v pos2 == U32.v pos1' - U32.v pos1 /\
    B.as_seq h (B.gsub s1.base pos1 (pos1' `U32.sub` pos1)) == B.as_seq h (B.gsub s2.base pos2 (pos2' `U32.sub` pos2))
  ))
= assert (injective_precond p (B.as_seq h (B.gsub s1.base pos1 (pos1' `U32.sub` pos1))) (B.as_seq h (B.gsub s2.base pos2 (pos2' `U32.sub` pos2))));
  assert (injective_postcond p (B.as_seq h (B.gsub s1.base pos1 (pos1' `U32.sub` pos1))) (B.as_seq h (B.gsub s2.base pos2 (pos2' `U32.sub` pos2))))

(*
let int32_to_uint32_pos
  (x: I32.t)
: Lemma
  (requires (I32.v x >= 0))
  (ensures (U32.v (Cast.int32_to_uint32 x) == I32.v x))
  [SMTPat (U32.v (Cast.int32_to_uint32 x))]
= MA.modulo_lemma (I32.v x) (pow2 32)

let uint32_to_int32_bounded
  (x: U32.t)
: Lemma
  (requires (U32.v x < 2147483648))
  (ensures (I32.v (Cast.uint32_to_int32 x) == U32.v x))
  [SMTPat (I32.v (Cast.uint32_to_int32 x))]
= MA.modulo_lemma (U32.v x) (pow2 32)

inline_for_extraction
type pointer (t: Type) = (b: B.buffer t { B.length b == 1 } )

let is_slice (h: HS.mem) (#t: Type) (b: B.buffer t) (len: I32.t) : GTot Type0 =
  B.live h b /\
  B.length b == I32.v len

unfold
let gsub
  (#t: Type)
  (b: B.buffer t)
  (i: U32.t)
  (len: U32.t)
: Ghost (B.buffer t)
  (requires (U32.v i + U32.v len <= B.length b))
  (ensures (fun b' -> B.length b' == U32.v len))
= B.gsub b i len

let is_tail_of (#t: Type) (b' b : B.buffer t) : GTot Type0 =
  B.length b' <= B.length b /\
  b' == gsub b (U32.uint_to_t (B.length b - B.length b')) (U32.uint_to_t (B.length b'))

let tail_ptr (h h' : HS.mem) (#t: Type) (p: pointer (B.buffer t)) : GTot Type0 =
  B.live h p /\
  B.live h' p /\ (
    let b = B.get h p 0 in
    let b' = B.get h' p 0 in
    B.live h b /\
    B.live h' b /\
    b' `is_tail_of` b
  )

let parse_from_slice
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (b: buffer8)
  (sz: I32.t)
: Ghost (option (t * nat))
  (requires (is_slice h b sz))
  (ensures (fun y ->
    match y with
    | None -> parse p (B.as_seq h b) == None
    | Some (x, len) -> len <= B.length b /\ parse p (B.as_seq h b) == Some (x, len)
  ))
= match parse p (B.as_seq h b) with
  | Some (x, len) -> Some (x, len)
  | _ -> None

(* A validator, if succeeds, returns the remaining length; otherwise returns a negative number. *)

let validator32_postcond
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
  (sz: I32.t)
  (h: HS.mem)
  (res: Int32.t)
  (h' : HS.mem)
: GTot Type0
= is_slice h input sz /\
  M.modifies M.loc_none h h' /\ (
    let pv = parse_from_slice p h input sz in
    if I32.v res >= 0
    then
      Some? pv /\ (
        let Some (_, consumed) = pv in
        I32.v res == I32.v sz - consumed
      )
    else
      None? pv
  )

[@unifier_hint_injective]
inline_for_extraction
let validator32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) ->
  (sz: I32.t) ->
  HST.Stack I32.t
  (requires (fun h ->
    is_slice h input sz
  ))
  (ensures (fun h res h' ->
    validator32_postcond p input sz h res h'
  ))

inline_for_extraction
let validate32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (input: buffer8)
  (sz: I32.t)
: HST.Stack bool
  (requires (fun h ->
    is_slice h input sz
  ))
  (ensures (fun h res h' ->
    is_slice h input sz /\
    M.modifies M.loc_none h h' /\ (
    let pv = parse_from_slice p h input sz in
    res == Some? pv
 )))
= let res = v input sz in
  not (res `I32.lt` 0l)

inline_for_extraction
let ghost_parse_from_validator32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (input: buffer8)
  (sz: I32.t)
: HST.Stack (option (Ghost.erased t))
  (requires (fun h ->
    is_slice h input sz
  ))
  (ensures (fun h res h' ->
    is_slice h input sz /\
    M.modifies M.loc_none h h'  /\
    res == (match parse_from_slice p h input sz with
    | Some (x, _) -> Some (Ghost.hide x)
    | _ ->  None
  )))
= let h = HST.get () in
  if validate32 v input sz
  then begin
    let f () : GTot t =
      let (Some (x, _)) = parse_from_slice p h input sz in
      x
    in
    Some (Ghost.elift1 f (Ghost.hide ()))
  end
  else None

inline_for_extraction
let ghost_parse32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
: HST.Stack (Ghost.erased t)
  (requires (fun h -> B.live h input /\ Some? (parse p (B.as_seq h input))))
  (ensures (fun h res h' -> h == h' /\ (let (Some (x, _)) = parse p (B.as_seq h input) in res == Ghost.hide x)))
= let h = HST.get () in
  let f () : GTot t =
    let (Some (x, _)) = parse p (B.as_seq h input) in
    x
  in
  Ghost.elift1 f (Ghost.hide ())

inline_for_extraction
let parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) ->
  HST.Stack t
  (requires (fun h ->
    B.live h input /\
    Some? (parse p (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    M.modifies M.loc_none h h' /\
    B.live h' input /\ (
    let ps = parse p (B.as_seq h input) in
    let (Some (res', _)) = ps in
    res == res'
  )))

inline_for_extraction
let validator_nochk32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) ->
  HST.Stack U32.t
  (requires (fun h ->
    B.live h input /\
    Some? (parse p (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    M.modifies M.loc_none h h' /\
    B.live h' input /\
    U32.v res <= B.length input /\ (
    let (Some (x, res')) = parse p (B.as_seq h input) in
    U32.v res == res'
  )))

inline_for_extraction
let accessor
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (rel: (t1 -> t2 -> GTot Type0))
: Tot Type
= (input: buffer8) ->
  HST.Stack buffer8
  (requires (fun h ->
    B.live h input /\
    Some? (parse p1 (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    M.modifies (M.loc_none) h h' /\
    B.live h' input /\
    B.includes input res /\ (
    let Some (x1, _) = parse p1 (B.as_seq h input) in
    let ps2 = parse p2 (B.as_seq h res) in
    Some? ps2 /\ (
    let Some (x2, _) = ps2 in
    rel x1 x2
  ))))

inline_for_extraction
let read_from_buffer
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#rel: (t1 -> t2 -> GTot Type0))
  (a12: accessor p1 p2 rel)
  (p2' : parser32 p2)
  (input: buffer8)
: HST.Stack t2
  (requires (fun h ->
    B.live h input /\
    Some? (parse p1 (B.as_seq h input))
  ))
  (ensures (fun h y h' ->
    M.modifies M.loc_none h h' /\ (
    let (Some (x, _)) = parse p1 (B.as_seq h input) in
    rel x y
  )))
= p2' (a12 input)

inline_for_extraction
let serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (b: buffer8) ->
  (lo: U32.t) ->
  (v: t) ->
  HST.Stack unit
  (requires (fun h -> B.live h b /\ U32.v lo + Seq.length (serialize s v) <= B.length b))
  (ensures (fun h _ h' ->
    let len = U32.uint_to_t (Seq.length (serialize s v)) in
    M.modifies (loc_jbuffer b lo (U32.add lo len)) h h' /\
    B.live h' b /\
    exactly_contains_valid_data h' p b lo v (U32.add lo len)
  ))

inline_for_extraction
let serializer32_fail
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (b: buffer8) ->
  (len: I32.t { I32.v len == B.length b } ) ->
  (lo: I32.t) ->
  (v: t) ->
  HST.Stack I32.t
  (requires (fun h -> B.live h b /\ I32.v lo <= I32.v len))
  (ensures (fun h hi h' ->
    B.live h' b /\
    contains_valid_serialized_data_or_fail h' s b lo v hi /\
    M.modifies (loc_ibuffer b lo hi) h h'
  ))


(* Stateful serializers for constant-size parsers *)

inline_for_extraction
let serializer32_fail_of_serializer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (psz: I32.t { k.parser_kind_high == Some k.parser_kind_low /\ k.parser_kind_low == I32.v psz } ) 
: Tot (serializer32_fail s)
= fun out (len: I32.t { I32.v len == B.length out } ) lo v ->
  let h = HST.get () in
  if lo `I32.lt` 0l
  then begin
    let res = lo in
    let h' = HST.get () in
    assert (contains_valid_serialized_data_or_fail h' s out lo v res);
    res
  end
  else begin
    assert (I32.v lo >= 0);
    assert (I32.v len >= 0);
    assert (I32.v lo <= I32.v len);
    assert (Seq.length (serialize s v) == I32.v psz);
    if (len `I32.sub` lo) `I32.lt` psz
    then begin
      let res = I32.int_to_t (-1) in
      let h' = HST.get () in
      assert (contains_valid_serialized_data_or_fail h' s out lo v res);
      assert (B.modifies (B.loc_buffer (B.gsub out (Cast.int32_to_uint32 lo) (B.len out `U32.sub` Cast.int32_to_uint32 lo))) h h');
      res
    end else begin
      assert (Seq.length (serialize s v) == I32.v psz);
      assert (I32.v lo + Seq.length (serialize s v) <= I32.v len);
      assert (U32.v (Cast.int32_to_uint32 lo) == I32.v lo);
      assert (U32.v (Cast.int32_to_uint32 lo) + Seq.length (serialize s v) <= I32.v len);
      assert (U32.v (Cast.int32_to_uint32 lo) + Seq.length (serialize s v) <= B.length out);
      s32 out (Cast.int32_to_uint32 lo) v;
      let h = HST.get () in
      exactly_contains_valid_data_contains_valid_serialized_data_or_fail h s out (Cast.int32_to_uint32 lo) v (Cast.int32_to_uint32 (lo `I32.add` psz));
      lo `I32.add` psz
    end
  end
  
(* Low-level serialization *)

assume
val valid (h: HS.mem) (b: LL.buffer8) (off: U32.t) (#k: parser_kind) (#t: Type) (p: parser k t) : GTot Type0

assume
val contents (h: HS.mem) (b: LL.buffer8) (off: U32.t) (#k: parser_kind) (#t: Type) (
