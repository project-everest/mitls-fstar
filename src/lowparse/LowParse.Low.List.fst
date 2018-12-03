module LowParse.Low.List

include LowParse.Spec.List
include LowParse.Low.Base

module B = LowStar.Buffer
module U32 = FStar.UInt32
module CL = C.Loops
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module G = FStar.Ghost

let valid_exact_list_nil
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
: Lemma
  (requires (U32.v pos <= U32.v sl.len /\ live_slice h sl))
  (ensures (
    valid_exact (parse_list p) h sl pos pos /\
    contents_exact (parse_list p) h sl pos pos == []
  ))
= parse_list_eq p (B.as_seq h (B.gsub sl.base pos 0ul));
  valid_exact_equiv (parse_list p) h sl pos pos;
  contents_exact_eq (parse_list p) h sl pos pos

let valid_exact_list_cons
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    valid p h sl pos /\
    valid_exact (parse_list p) h sl (get_valid_pos p h sl pos) pos'
  ))
  (ensures (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    valid p h sl pos /\
    valid_exact (parse_list p) h sl (get_valid_pos p h sl pos) pos' /\
    valid_exact (parse_list p) h sl pos pos' /\
    contents_exact (parse_list p) h sl pos pos' == contents p h sl pos :: contents_exact (parse_list p) h sl (get_valid_pos p h sl pos) pos'
  ))
= let sq = B.as_seq h (B.gsub sl.base pos (pos' `U32.sub` pos)) in
  parse_list_eq' p sq;
  let pos1 = get_valid_pos p h sl pos in
  valid_exact_equiv (parse_list p) h sl pos pos';
  valid_facts p h sl pos;
  let sq0 = B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)) in
  assert (no_lookahead_on p sq0 sq);
  assert (injective_postcond p sq0 sq);
  valid_exact_equiv (parse_list p) h sl pos1 pos';  
  contents_exact_eq (parse_list p) h sl pos pos';
  contents_exact_eq (parse_list p) h sl pos1 pos'

abstract
let rec valid_list_valid_exact_list
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    valid_list p h sl pos pos'
  ))
  (ensures (
    valid_exact (parse_list p) h sl pos pos' /\
    contents_exact (parse_list p) h sl pos pos' == contents_list p h sl pos pos'
  ))
  (decreases (U32.v pos' - U32.v pos))
= valid_list_equiv p h sl pos pos';
  contents_list_eq p h sl pos pos' ;
  if pos = pos'
  then valid_exact_list_nil p h sl pos
  else begin
    let pos1 = get_valid_pos p h sl pos in
    valid_list_valid_exact_list p h sl pos1 pos';
    valid_exact_list_cons p h sl pos pos'
  end

let valid_exact_list_cons_recip
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    pos <> pos' /\
    valid_exact (parse_list p) h sl pos pos'
  ))
  (ensures (
    k.parser_kind_subkind == Some ParserStrong /\
    pos <> pos' /\
    valid_exact (parse_list p) h sl pos pos' /\
    valid p h sl pos /\ (
    let pos1 = get_valid_pos p h sl pos in
    valid_exact (parse_list p) h sl pos1 pos' /\
    contents_exact (parse_list p) h sl pos pos' == contents p h sl pos :: contents_exact (parse_list p) h sl pos1 pos'
  )))
= let sq = B.as_seq h (B.gsub sl.base pos (pos' `U32.sub` pos)) in
  parse_list_eq p sq;
  valid_exact_equiv (parse_list p) h sl pos pos';
  valid_facts p h sl pos;
  let sq0 = B.as_seq h (B.gsub sl.base pos (sl.len `U32.sub` pos)) in
  assert (no_lookahead_on p sq sq0);
  assert (injective_postcond p sq sq0);
  let pos1 = get_valid_pos p h sl pos in
  valid_exact_equiv (parse_list p) h sl pos1 pos';  
  contents_exact_eq (parse_list p) h sl pos pos';
  contents_exact_eq (parse_list p) h sl pos1 pos'

abstract
let rec valid_exact_list_valid_list
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos : U32.t)
  (pos' : U32.t)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    valid_exact (parse_list p) h sl pos pos'
  ))
  (ensures (
    valid_list p h sl pos pos' /\
    contents_exact (parse_list p) h sl pos pos' == contents_list p h sl pos pos'
  ))
  (decreases (U32.v pos' - U32.v pos))
= valid_list_equiv p h sl pos pos';
  if pos = pos'
  then
    valid_exact_list_nil p h sl pos
  else begin
    valid_exact_list_cons_recip p h sl pos pos';
    let pos1 = get_valid_pos p h sl pos in
    valid_exact_list_valid_list p h sl pos1 pos'
  end;
  contents_list_eq p h sl pos pos'

module L = FStar.List.Tot

abstract
let rec valid_exact_list_append
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (sl: slice)
  (pos1 pos2 pos3 : U32.t)
: Lemma
  (requires (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    valid_exact (parse_list p) h sl pos1 pos2 /\
    valid_exact (parse_list p) h sl pos2 pos3
  ))
  (ensures (
    valid_exact (parse_list p) h sl pos1 pos3 /\
    contents_exact (parse_list p) h sl pos1 pos3 == contents_exact (parse_list p) h sl pos1 pos2 `L.append` contents_exact (parse_list p) h sl pos2 pos3
  ))
  (decreases (U32.v pos2 - U32.v pos1))
= if pos1 = pos2
  then
    valid_exact_list_nil p h sl pos1
  else begin
    valid_exact_list_cons_recip p h sl pos1 pos2;
    let pos15 = get_valid_pos p h sl pos1 in
    valid_exact_list_append p h sl pos15 pos2 pos3;
    valid_exact_list_cons p h sl pos1 pos3
  end


let validate_list_inv
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (g0 g1: G.erased HS.mem)
  (sl: slice)
  (pos0: U32.t)
  (bpos: B.pointer U32.t)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= let h0 = G.reveal g0 in
  let h1 = G.reveal g1 in
  B.disjoint sl.base bpos /\
  k.parser_kind_subkind == Some ParserStrong /\
  k.parser_kind_low > 0 /\
  U32.v pos0 <= U32.v sl.len /\
  U32.v sl.len <= U32.v validator_max_length /\
  live_slice h0 sl /\
  B.live h1 bpos /\
  B.modifies B.loc_none h0 h1 /\
  B.modifies (B.loc_buffer bpos) h1 h /\ (
  let pos1 = Seq.index (B.as_seq h bpos) 0 in
  if
    U32.v pos1 > U32.v validator_max_length
  then
    stop == true /\
    (~ (valid_exact (parse_list p) h0 sl pos0 sl.len))
  else
    U32.v pos0 <= U32.v pos1 /\
    U32.v pos1 <= U32.v sl.len /\
    (valid_exact (parse_list p) h0 sl pos0 sl.len <==> valid_exact (parse_list p) h0 sl pos1 sl.len) /\
    (stop == true ==> pos1 == sl.len)
  )

inline_for_extraction
let validate_list_body
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
  (g0 g1: G.erased HS.mem)
  (sl: slice)
  (pos0: U32.t)
  (bpos: B.pointer U32.t)
: HST.Stack bool
  (requires (fun h -> validate_list_inv p g0 g1 sl pos0 bpos h false))
  (ensures (fun h res h' ->
    validate_list_inv p g0 g1 sl pos0 bpos h false /\
    validate_list_inv p g0 g1 sl pos0 bpos h' res
  ))
= let pos1 = B.index bpos 0ul in
  assert (U32.v pos1 <= U32.v sl.len);
  if pos1 = sl.len
  then true
  else begin
    Classical.move_requires (valid_exact_list_cons p (G.reveal g0) sl pos1) sl.len;
    Classical.move_requires (valid_exact_list_cons_recip p (G.reveal g0) sl pos1) sl.len;
    let pos1 = v sl pos1 in
    B.upd bpos 0ul pos1;
    pos1 `U32.gt` validator_max_length
  end

inline_for_extraction
let validate_list'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
  (sl: slice)
  (pos: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0 /\
    U32.v pos <= U32.v sl.len /\
    U32.v sl.len <= U32.v validator_max_length /\
    live_slice h sl
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    (* we could return a boolean, but we would like to return the last
       validation error code if it fails. (alas, we cannot capture
       that fact in the spec.) *)
    (U32.v res <= U32.v validator_max_length <==> valid_exact (parse_list p) h sl pos sl.len)
  ))
= let h0 = HST.get () in
  let g0 = G.hide h0 in
  HST.push_frame ();
  let h02 = HST.get () in
  B.fresh_frame_modifies h0 h02;
  let bpos = B.alloca pos 1ul in
  let h1 = HST.get () in
  let g1 = G.hide h1 in
  C.Loops.do_while (validate_list_inv p g0 g1 sl pos bpos) (fun _ -> validate_list_body v g0 g1 sl pos bpos);
  valid_exact_list_nil p h0 sl sl.len;
  let posf = B.index bpos 0ul in
  HST.pop_frame ();
  posf

inline_for_extraction
let validate_list
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator p)
  (u: squash (
    k.parser_kind_subkind == Some ParserStrong /\
    k.parser_kind_low > 0
  ))
: Tot (validator (parse_list p))
= fun
  (sl: slice)
  (pos: U32.t) ->
  let h = HST.get () in
  valid_valid_exact_consumes_all (parse_list p) h sl pos;
  let error = validate_list' v sl pos in 
  if error `U32.lte` validator_max_length
  then sl.len
  else error

(* fold_left on lists *)

#push-options "--z3rlimit 16"

inline_for_extraction
let list_fold_left_gen
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (j: jumper p)
  (sl: slice)
  (pos pos' : U32.t)
  (h0: HS.mem)
  (l: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal l) (loc_slice_from_to sl pos pos') } )
  (inv: (HS.mem -> list t -> list t -> U32.t -> GTot Type0))
  (inv_frame: (h: HS.mem) -> (l1: list t) -> (l2: list t) -> (pos1: U32.t) -> (h' : HS.mem) -> Lemma (requires (
    B.modifies (B.loc_unused_in h0) h h' /\
    inv h l1 l2 pos1
  )) (ensures (inv h' l1 l2 pos1)))
  (body: (
    (pos1: U32.t) ->
    (pos2: U32.t) ->
    HST.Stack unit
    (requires (fun h ->
      valid_exact (parse_list p) h sl pos pos1 /\
      valid_pos p h sl pos1 pos2 /\
      valid_exact (parse_list p) h sl pos2 pos' /\
      inv h (contents_exact (parse_list p) h sl pos pos1) (contents p h sl pos1 :: contents_exact (parse_list p) h sl pos2 pos') pos1
    ))
    (ensures (fun h _ h' ->
      B.modifies (Ghost.reveal l) h h' /\
      inv h' (contents_exact (parse_list p) h sl pos pos1 `L.append` [contents p h sl pos1]) (contents_exact (parse_list p) h sl pos2 pos') pos2
    ))
  ))
: HST.Stack unit
  (requires (fun h ->
    h == h0 /\
    valid_exact (parse_list p) h sl pos pos' /\
    inv h [] (contents_exact (parse_list p) h sl pos pos') pos
  ))
  (ensures (fun h _ h' ->
    B.modifies (Ghost.reveal l) h h' /\
    inv h' (contents_exact (parse_list p) h sl pos pos') [] pos'
  ))
= HST.push_frame ();
  let h1 = HST.get () in
  B.fresh_frame_modifies h0 h1;
  let bpos : B.pointer U32.t = B.alloca pos 1ul in
  let h2 = HST.get () in
  let test_pre (h: HS.mem) : GTot Type0 =
    B.live h bpos /\ (
    let pos1 = Seq.index (B.as_seq h bpos) 0 in
    valid_exact (parse_list p) h0 sl pos pos1 /\
    valid_exact (parse_list p) h0 sl pos1 pos' /\
    B.modifies (Ghost.reveal l `B.loc_union` B.loc_buffer bpos) h2 h /\
    inv h (contents_exact (parse_list p) h0 sl pos pos1) (contents_exact (parse_list p) h0 sl pos1 pos') pos1
  )
  in
  let test_post (cond: bool) (h: HS.mem) : GTot Type0 =
    test_pre h /\
    cond == (U32.v (Seq.index (B.as_seq h bpos) 0) < U32.v pos')
  in
  valid_exact_list_nil p h0 sl pos;
  inv_frame h0 [] (contents_exact (parse_list p) h0 sl pos pos') pos h1;
  inv_frame h1 [] (contents_exact (parse_list p) h0 sl pos pos') pos h2;
  C.Loops.while
    #test_pre
    #test_post
    (fun (_: unit) -> B.index bpos 0ul `U32.lt` pos' <: HST.Stack bool (requires (fun h -> test_pre h)) (ensures (fun h x h1 -> test_post x h1)))
    (fun _ ->
      let h51 = HST.get () in
      let pos1 = B.index bpos 0ul in
      valid_exact_list_cons_recip p h0 sl pos1 pos';
      assert (B.modifies (Ghost.reveal l `B.loc_union` B.loc_buffer bpos) h0 h51);
      assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos1 pos'));
      assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos pos1));
      valid_exact_list_cons_recip p h51 sl pos1 pos';
      let pos2 = j sl pos1 in
      let h52 = HST.get () in
      inv_frame h51 (contents_exact (parse_list p) h0 sl pos pos1) (contents_exact (parse_list p) h1 sl pos1 pos') pos1 h52;
      body pos1 pos2;
      let h53 = HST.get () in
      assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos1 pos2));
      assert (B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos2 pos'));
      valid_exact_list_nil p h0 sl pos2;
      valid_pos_frame_strong p h0 sl pos1 pos2 (Ghost.reveal l `B.loc_union` B.loc_buffer bpos) h53;
      valid_exact_list_cons p h0 sl pos1 pos2;
      valid_exact_list_append p h0 sl pos pos1 pos2;
      B.upd bpos 0ul pos2;
      let h54 = HST.get () in
      inv_frame h53 (contents_exact (parse_list p) h0 sl pos pos2) (contents_exact (parse_list p) h0 sl pos2 pos') pos2 h54
    )
    ;
  valid_exact_list_nil p h0 sl pos';
  let h3 = HST.get () in
  HST.pop_frame ();
  let h4 = HST.get () in
  B.popped_modifies h3 h4;
  B.loc_regions_unused_in h0 (Set.singleton (HS.get_tip h3));  
  inv_frame h3 (contents_exact (parse_list p) h0 sl pos pos') [] pos' h4;
  B.loc_includes_union_l (B.loc_all_regions_from false (HS.get_tip h1)) (Ghost.reveal l) (Ghost.reveal l);
  B.modifies_fresh_frame_popped h0 h1 (Ghost.reveal l) h3 h4

#pop-options

inline_for_extraction
let list_fold_left
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (j: jumper p)
  (sl: slice)
  (pos pos' : U32.t)
  (h0: HS.mem)
  (l: Ghost.erased B.loc { B.loc_disjoint (Ghost.reveal l) (loc_slice_from_to sl pos pos') } )
  (inv: (HS.mem -> list t -> list t -> U32.t -> GTot Type0))
  (inv_frame: (h: HS.mem) -> (l1: list t) -> (l2: list t) -> (pos1: U32.t) -> (h' : HS.mem) -> Lemma (requires (
    B.modifies (B.loc_unused_in h0) h h' /\
    inv h l1 l2 pos1
  )) (ensures (inv h' l1 l2 pos1)))
  (body: (
    (pos1: U32.t) ->
    (pos2: U32.t) ->
    (l1: Ghost.erased (list t)) ->
    (x: Ghost.erased t) ->
    (l2: Ghost.erased (list t)) ->
    HST.Stack unit
    (requires (fun h ->
      valid_exact (parse_list p) h sl pos pos' /\
      valid_content_pos p h sl pos1 (G.reveal x) pos2 /\
      U32.v pos <= U32.v pos1 /\ U32.v pos2 <= U32.v pos' /\
      B.loc_includes (loc_slice_from_to sl pos pos') (loc_slice_from_to sl pos1 pos2) /\
      inv h (Ghost.reveal l1) (Ghost.reveal x :: Ghost.reveal l2) pos1 /\
      contents_exact (parse_list p) h sl pos pos' == Ghost.reveal l1 `L.append` (Ghost.reveal x :: Ghost.reveal l2)
    ))
    (ensures (fun h _ h' ->
      B.modifies (Ghost.reveal l) h h' /\
      inv h' (Ghost.reveal l1 `L.append` [contents p h sl pos1]) (Ghost.reveal l2) pos2
    ))
  ))
: HST.Stack unit
  (requires (fun h ->
    h == h0 /\
    valid_exact (parse_list p) h sl pos pos' /\
    inv h [] (contents_exact (parse_list p) h sl pos pos') pos
  ))
  (ensures (fun h _ h' ->
    B.modifies (Ghost.reveal l) h h' /\
    inv h' (contents_exact (parse_list p) h sl pos pos') [] pos'
  ))
= list_fold_left_gen
    p
    j
    sl
    pos pos'
    h0
    l
    inv
    inv_frame
    (fun pos1 pos2 ->
      let h = HST.get () in
      valid_exact_list_cons p h sl pos1 pos';
      valid_exact_list_append p h sl pos pos1 pos';
      body
        pos1
        pos2
        (Ghost.hide (contents_exact (parse_list p) h sl pos pos1))
        (Ghost.hide (contents p h sl pos1))
        (Ghost.hide (contents_exact (parse_list p) h sl pos2 pos'))
    )

let list_length_append (#t: Type) (l1 l2: list t) : Lemma (L.length (l1 `L.append` l2) == L.length l1 + L.length l2) = L.append_length l1 l2

inline_for_extraction
let list_length
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (j: jumper p)
  (sl: slice)
  (pos pos' : U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    valid_exact (parse_list p) h sl pos pos'
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v res == L.length (contents_exact (parse_list p) h sl pos pos')
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  B.fresh_frame_modifies h0 h1;
  let blen : B.pointer U32.t = B.alloca 0ul 1ul in
  let h2 = HST.get () in
  list_fold_left
    p
    j
    sl
    pos
    pos'
    h2
    (Ghost.hide (B.loc_buffer blen))
    (fun h l1 l2 pos1 ->
      B.modifies (B.loc_buffer blen) h2 h /\
      B.live h blen /\ (
      let len = U32.v (Seq.index (B.as_seq h blen) 0) in
      len <= U32.v pos1 /\ // necessary to prove that length computations do not overflow
      len == L.length l1
    ))
    (fun h l1 l2 pos1 h' ->
      B.modifies_only_not_unused_in (B.loc_buffer blen) h2 h';
      B.loc_unused_in_not_unused_in_disjoint h2
    )
    (fun pos1 pos2 l1 x l2 ->
      B.upd blen 0ul (B.index blen 0ul `U32.add` 1ul);
      Classical.forall_intro_2 (list_length_append #t)
    )
    ;
  let len = B.index blen 0ul in
  HST.pop_frame ();
  len

abstract
let rec list_filter_append
  (#t: Type)
  (f: (t -> Tot bool))
  (l1 l2: list t)
: Lemma
  (L.filter f (l1 `L.append` l2) == L.filter f l1 `L.append` L.filter f l2)
= match l1 with
  | [] -> ()
  | a :: q ->
    list_filter_append f q l2

#push-options "--z3rlimit 16"

inline_for_extraction
let list_filter
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { k.parser_kind_subkind == Some ParserStrong /\ k.parser_kind_low > 0 } )
  (j: jumper p)
  (f: (t -> Tot bool))
  (f' : (
    (sl: slice) ->
    (pos: U32.t) ->
    (x: Ghost.erased t) ->
    HST.Stack bool
    (requires (fun h -> valid_content p h sl pos (G.reveal x)))
    (ensures (fun h res h' -> B.modifies B.loc_none h h' /\ res == f (G.reveal x)))
  ))
  (sl: slice)
  (pos pos' : U32.t)
  (sl_out : slice)
  (pos_out : U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    U32.v pos_out + U32.v pos' - U32.v pos <= U32.v sl_out.len /\
    valid_exact (parse_list p) h sl pos pos' /\
    B.loc_disjoint (loc_slice_from_to sl pos pos') (loc_slice_from_to sl_out pos_out (pos_out `U32.add` (pos' `U32.sub` pos))) /\
    live_slice h sl_out
  ))
  (ensures (fun h pos_out' h' ->
    B.modifies (loc_slice_from_to sl_out pos_out pos_out') h h' /\
    U32.v pos_out' - U32.v pos_out <= U32.v pos' - U32.v pos /\
    valid_exact (parse_list p) h' sl_out pos_out pos_out' /\
    contents_exact (parse_list p) h' sl_out pos_out pos_out' == L.filter f (contents_exact (parse_list p) h sl pos pos')
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  B.fresh_frame_modifies h0 h1;
  let bpos_out' : B.pointer U32.t = B.alloca pos_out 1ul in
  let h2 = HST.get () in
  let inv (h: HS.mem) (l1 l2: list t) (pos1: U32.t) : GTot Type0 =
    B.live h bpos_out' /\ (
      let pos_out' = Seq.index (B.as_seq h bpos_out') 0 in
      B.modifies (B.loc_buffer bpos_out' `B.loc_union` loc_slice_from_to sl_out pos_out pos_out') h2 h /\
      valid_exact (parse_list p) h sl_out pos_out pos_out' /\
      contents_exact (parse_list p) h sl_out pos_out pos_out' == L.filter f l1 /\
      U32.v pos_out' - U32.v pos1 <= U32.v pos_out - U32.v pos // necessary to prove that length computations do not overflow
    )
  in
  valid_exact_list_nil p h2 sl_out pos_out;
  list_fold_left
    p
    j
    sl
    pos
    pos'
    h2
    (Ghost.hide (B.loc_buffer bpos_out' `B.loc_union` loc_slice_from_to sl_out pos_out (pos_out `U32.add` (pos' `U32.sub` pos))))
    inv
    (fun h l1 l2 pos1 h' ->
      let pos_out' = Seq.index (B.as_seq h bpos_out') 0 in
      B.modifies_only_not_unused_in (B.loc_buffer bpos_out' `B.loc_union` loc_slice_from_to sl_out pos_out pos_out') h2 h';
      B.loc_unused_in_not_unused_in_disjoint h2
    )
    (fun pos1 pos2 l1 x l2 ->
      let pos_out1 = B.index bpos_out' 0ul in
      list_filter_append f (G.reveal l1) [G.reveal x];
      if f' sl pos1 x
      then begin
        assert (B.loc_includes (loc_slice_from_to sl_out pos_out (pos_out `U32.add` (pos' `U32.sub` pos))) (loc_slice_from_to sl_out pos_out1 (pos_out1 `U32.add` (pos2 `U32.sub` pos1))));
        let pos_out2 = copy_strong p sl pos1 pos2 sl_out pos_out1 in
        B.upd bpos_out' 0ul pos_out2;
        let h' = HST.get () in
        valid_exact_list_nil p h' sl_out pos_out2;
        valid_exact_list_cons p h' sl_out pos_out1 pos_out2;
        valid_exact_list_append p h' sl_out pos_out pos_out1 pos_out2
      end else
        L.append_l_nil (L.filter f (G.reveal l1))
    )
    ;
  let pos_out' = B.index bpos_out' 0ul in
  HST.pop_frame ();
  pos_out'

#pop-options

(*
#reset-options "--z3rlimit 128 --max_fuel 16 --max_ifuel 16 --z3cliopt smt.arith.nl=false"

inline_for_extraction
val list_is_nil
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
  (len: I32.t)
: HST.Stack bool
  (requires (fun h ->
    is_slice h input len /\
    Some? (parse (parse_list p) (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    h == h' /\ (
    let Some (v, _) = parse (parse_list p) (B.as_seq h input) in
    res == true <==> v == []
  )))

let list_is_nil #k #t p input len =
  len = 0l

/// TODO: generalize accessors with conditions

inline_for_extraction
let list_head
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
: HST.Stack buffer8
  (requires (fun h ->
    B.live h input /\ (
    let ps = parse (parse_list p) (B.as_seq h input) in
    Some? ps /\ (
    let Some (v, _) = ps in
    Cons? v
  ))))
  (ensures (fun h res h' ->
    M.modifies (M.loc_none) h h' /\
    B.live h' input /\
    B.includes input res /\ (
    let Some ((v::_), _) = parse (parse_list p) (B.as_seq h input) in
    let ps = parse p (B.as_seq h res) in
    Some? ps /\ (
    let (Some (v', _)) = ps in
    v' == v
  ))))
= input

inline_for_extraction
let list_tail
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator_nochk32 p)
  (input: buffer8)
: HST.Stack buffer8
  (requires (fun h ->
    B.live h input /\ (
    let ps = parse (parse_list p) (B.as_seq h input) in
    Some? ps /\ (
    let Some (v, _) = ps in
    Cons? v
  ))))
  (ensures (fun h res h' ->
    M.modifies (M.loc_none) h h' /\
    B.live h' input /\ (
    let Some ((_::v), _) = parse (parse_list p) (B.as_seq h input) in
    let ps = parse (parse_list p) (B.as_seq h res) in
    Some? ps /\ (
    let (Some (v', _)) = ps in
    v == v'
  ))))
= B.offset input (v input)
