module LowParse.Low.List
include LowParse.Spec.List
include LowParse.Low.Combinators

module B = FStar.Buffer
module U32 = FStar.UInt32
module CL = C.Loops
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module G = FStar.Ghost
module M = FStar.Modifies

let validate32_list_inv
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: pointer buffer8)
  (len: pointer U32.t)
  (h0: G.erased HS.mem)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= is_slice_ptr (G.reveal h0) input len /\
  M.modifies (loc_slice input len) (G.reveal h0) h /\
  B.live h input /\
  B.live h len /\ (
    let len' = B.get h len 0 in
    let ps0 = parse (parse_list p) (B.as_seq (G.reveal h0) (B.get (G.reveal h0) input 0)) in
    if stop
    then
      if U32.v len' = 4294967295
      then None? ps0
      else validator32_postcond (parse_list p) input len (G.reveal h0) true h
    else
      U32.v len' <> 4294967295 /\
      is_slice_ptr h input len /\
      tail_ptr (G.reveal h0) h input /\
      Some? ps0 == Some? (parse (parse_list p) (B.as_seq h (B.get h input 0)))
  )

#reset-options "--z3rlimit 64"

inline_for_extraction
let validate32_list_body
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (v: validator32 p)
  (input: pointer buffer8)
  (len: pointer U32.t)
  (h0: G.erased HS.mem)
  ()
: HST.Stack bool
  (requires (fun h -> validate32_list_inv p input len h0 h false))
  (ensures (fun _ stop h' -> validate32_list_inv p input len h0 h' stop))
= let len' = B.index len 0ul in
  if len' = 0ul
  then true
  else if v input len
  then
    if B.index len 0ul = len'
    then begin
      B.upd len 0ul 4294967295ul;
      true
    end
    else false
  else begin
    B.upd len 0ul 4294967295ul;
    true
  end

inline_for_extraction
let validate32_list'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (v: validator32 p)
  (input: pointer buffer8)
  (len: pointer U32.t)
: HST.Stack bool
  (requires (fun h -> is_slice_ptr h input len /\ U32.v (B.get h len 0) <> 4294967295))
  (ensures (fun h res h' ->
    validator32_postcond (parse_list p) input len h res h'
  ))
= let h = HST.get () in
  let h0 = G.hide h in
  let len0 = B.index len 0ul in
  let input0 = B.index input 0ul in
  C.Loops.do_while
    (validate32_list_inv p input len h0)
    (fun () -> validate32_list_body p v input len h0 ())
  ;
  let len2 = B.index len 0ul in
  len2 <> 4294967295ul

#reset-options "--z3rlimit 128 --max_fuel 16 --max_ifuel 16 --z3cliopt smt.arith.nl=false"

inline_for_extraction
let validate32_list
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (v: validator32 p)
: Tot (validator32 (parse_list p))
= fun
  (input: pointer buffer8)
  (len: pointer U32.t)
  ->
  let len0 = B.index len 0ul in
  if len0 = 0ul
  then true
  else if v input len
  then
    let len1 = B.index len 0ul in
    if len0 = len1
    then false
    else validate32_list' p v input len
  else false

inline_for_extraction
val list_is_nil
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: pointer buffer8)
  (len: pointer U32.t)
: HST.Stack bool
  (requires (fun h ->
    is_slice_ptr h input len /\
    Some? (parse (parse_list p) (B.as_seq h (B.get h input 0)))
  ))
  (ensures (fun h res h' ->
    h == h' /\ (
    let Some (v, _) = parse (parse_list p) (B.as_seq h (B.get h input 0)) in
    res == true <==> v == []
  )))

let list_is_nil #k #t p input len =
  B.index len 0ul = 0ul

inline_for_extraction
val list_head
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator_nochk32 p)
  (input: pointer buffer8)
  (len: pointer U32.t)
: HST.Stack unit
  (requires (fun h ->
    is_slice_ptr h input len /\ (
    let ps = parse_from_slice_ptr (parse_list p) h input len in
    Some? ps /\ (
    let Some (v, _) = ps in
    Cons? v
  ))))
  (ensures (fun h _ h' ->
    M.modifies (loc_slice input len) h h' /\
    includes_slice_ptr h h' input len /\ (
    let Some ((v::_), _) = parse_from_slice_ptr (parse_list p) h input len in
    exactly_parse_from_slice_ptr p h' input len == Some v
  )))

let list_head #k #t #p v input len =
  truncate32 v input len

inline_for_extraction
val list_tail
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (v: validator_nochk32 p)
  (input: pointer buffer8)
  (len: pointer U32.t)
: HST.Stack unit
  (requires (fun h ->
    is_slice_ptr h input len /\ (
    let ps = parse_from_slice_ptr (parse_list p) h input len in
    Some? ps /\ (
    let Some (v, _) = ps in
    Cons? v
  ))))
  (ensures (fun h _ h' ->
    M.modifies (loc_slice input len) h h' /\
    includes_slice_ptr h h' input len /\ (
    let Some ((_::v), _) = parse_from_slice_ptr (parse_list p) h input len in
    exactly_parse_from_slice_ptr (parse_list p) h' input len == Some v
  )))

let list_tail #k #t p v input len =
  v input len
