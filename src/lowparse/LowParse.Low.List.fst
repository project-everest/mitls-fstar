module LowParse.Low.List
include LowParse.Spec.List
include LowParse.Low.Combinators

module B = LowStar.Buffer
module U32 = FStar.UInt32
module CL = C.Loops
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module G = FStar.Ghost
module M = LowStar.Modifies
module I32 = FStar.Int32
module Cast = FStar.Int.Cast

unfold
let validate32_list_inv'
  [| validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
  (len: I32.t)
  (read_so_far: pointer I32.t)
  (h0: G.erased HS.mem)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= k.parser_kind_low > 0 /\
  is_slice (G.reveal h0) input len /\
  B.disjoint input read_so_far /\
  M.loc_disjoint (M.loc_buffer read_so_far) (validator32_error_loc ()) /\
  M.loc_disjoint (M.loc_buffer input) (validator32_error_loc ()) /\
//  M.loc_disjoint (M.loc_union (M.loc_buffer read_so_far) (M.loc_buffer input)) (validator32_error_loc ()) /\
  M.modifies (M.loc_union (validator32_error_loc ()) (M.loc_buffer read_so_far)) (G.reveal h0) h /\
  validator32_error_inv (Ghost.reveal h0) /\
  validator32_error_inv h /\
  is_slice h input len /\
  B.live h read_so_far /\
  (
    let v_read_so_far = B.get h read_so_far 0 in
    let ps0 = parse (parse_list p) (B.as_seq (G.reveal h0) input) in
    if stop
    then
      validator32_postcond'  (parse_list p) input len (G.reveal h0) v_read_so_far (G.reveal h0)
    else
      I32.v v_read_so_far >= 0 /\
      I32.v v_read_so_far <= I32.v len /\ (
      let ps1 = parse (parse_list p) (B.as_seq (G.reveal h0) (gsub input (Cast.int32_to_uint32 v_read_so_far) (U32.uint_to_t (I32.v len - I32.v v_read_so_far)))) in
      Some? ps0 == Some? ps1 /\
      True
        ))

unfold
let validate32_list_inv
  [| validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
  (len: I32.t)
  (read_so_far: pointer I32.t)
  (h0: G.erased HS.mem)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= validate32_list_inv' p input len read_so_far h0 h stop

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false"

inline_for_extraction
let validate32_list_body_case1
  [| cls: validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (input: buffer8)
  (len: I32.t)
  (read_so_far: pointer I32.t)
  (h0: G.erased HS.mem)
  (u: unit)
: HST.Stack bool
  (requires (fun h ->
    validate32_list_inv p input len read_so_far h0 h false /\ (
    let v_read_so_far = Seq.index (B.as_seq h read_so_far) 0 in
    v_read_so_far = len
  )))
  (ensures (fun h stop h' ->
    validate32_list_inv p input len read_so_far h0 h false /\
    validate32_list_inv p input len read_so_far h0 h' stop
  ))
= B.upd read_so_far 0ul 0l;
  let h' = HST.get () in
  assert (validator32_error_inv h');
  // assert (validator32_error_inv h' ==> validate32_list_inv p input len read_so_far h0 h' true);
  true

inline_for_extraction
let validate32_list_body
  [| cls: validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (input: buffer8)
  (len: I32.t)
  (read_so_far: pointer I32.t)
  (h0: G.erased HS.mem)
  (u: unit)
: HST.Stack bool
  (requires (fun h -> validate32_list_inv p input len read_so_far h0 h false))
  (ensures (fun h stop h' ->
    validate32_list_inv p input len read_so_far h0 h false /\
    validate32_list_inv p input len read_so_far h0 h' stop
  ))
= let h = HST.get () in
  let f () : Lemma (validate32_list_inv p input len read_so_far h0 h false) = () in
  let v_read_so_far = B.index read_so_far 0ul in
  if v_read_so_far = len
  then begin
    validate32_list_body_case1 #cls v input len read_so_far h0 u
  end
  else begin
    let h1 = HST.get () in
    let res = v (B.offset input (Cast.int32_to_uint32 v_read_so_far)) (len `I32.sub` v_read_so_far) in
 (* now we require that the element parser consumes at least one byte *)
    if res `I32.lt` 0l // || res = len `I32.sub` v_read_so_far
    then begin
      B.upd read_so_far 0ul res; // (-1l);
      f ();
      let h' = HST.get () in
      true
    end else begin
      let read_so_far' = len `I32.sub` res in
      B.upd read_so_far 0ul read_so_far';
      assert (
        let b0 = gsub input (Cast.int32_to_uint32 v_read_so_far) (U32.uint_to_t (I32.v len - I32.v v_read_so_far)) in
        let b1 = gsub input (Cast.int32_to_uint32 read_so_far') (U32.uint_to_t (I32.v len - I32.v read_so_far')) in
        let b1' = gsub b0 (U32.uint_to_t (I32.v read_so_far' - I32.v v_read_so_far)) (Cast.int32_to_uint32 res) in
        b1 == b1' /\
        Some? (parse (parse_list p) (B.as_seq (G.reveal h0) input)) == Some? (parse (parse_list p) (B.as_seq (G.reveal h0) b0)) /\
        Some? (parse (parse_list p) (B.as_seq (G.reveal h0) b0)) ==
          Some? (parse (parse_list p) (B.as_seq (G.reveal h0) b1)) /\
        True
      );
      let h' = HST.get () in
      assert (Some? (parse (parse_list p) (B.as_seq (G.reveal h0) input)) == Some? (parse (parse_list p) (B.as_seq (G.reveal h0) (gsub input (Cast.int32_to_uint32 read_so_far') (U32.uint_to_t (I32.v len - I32.v read_so_far'))))));
      assert (validate32_list_inv p input len read_so_far h0 h' false);
      f ();
      false
    end
  end

#reset-options "--z3rlimit 32"

inline_for_extraction
let validate32_list
  [| cls: validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 #cls p { k.parser_kind_low > 0 } )
: Tot (validator32 (parse_list p))
= fun input len ->
  let h_0 = HST.get () in
  HST.push_frame ();
  let h_ = HST.get () in
  M.not_live_region_loc_not_unused_in_disjoint h_0 (HS.get_tip h_);
  validator32_error_inv_frame' h_0 h_ M.loc_none;
  let read_so_far = B.alloca 0l 1ul in
  let h = HST.get () in
  let h0 = G.hide h in
  C.Loops.do_while
    (validate32_list_inv p input len read_so_far h0)
    (validate32_list_body v input len read_so_far h0)
  ;
  let res = B.index read_so_far 0ul in
  let h'1 = HST.get () in
  HST.pop_frame ();
  let h'  = HST.get () in
  validator32_error_inv_frame' h'1 h' (M.loc_region_only false (HS.get_tip h'1));
  res

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
