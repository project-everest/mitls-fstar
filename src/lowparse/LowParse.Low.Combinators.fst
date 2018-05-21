module LowParse.Low.Combinators
include LowParse.Low.Base
include LowParse.Spec.Combinators

module B = FStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

#reset-options "--z3rlimit 128 --max_fuel 32 --max_ifuel 32 --z3cliopt smt.arith.nl=false"

inline_for_extraction
let validate32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (p1' : validator32 p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (p2' : validator32 p2)
: Tot (validator32 (nondep_then p1 p2))
= fun (input: pointer buffer8) (len: pointer U32.t) ->
  let h = HST.get () in
  if p1' input len
  then begin
    let h1 = HST.get () in
    let res = p2' input len in
    let h' = HST.get () in
    res
  end else false

inline_for_extraction
let validate_nochk32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (p1' : validator_nochk32 p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (p2' : validator_nochk32 p2)
: Tot (validator_nochk32 (nondep_then p1 p2))
= fun (input: pointer buffer8) (len: pointer U32.t) ->
  p1' input len;
  p2' input len

inline_for_extraction
let validate32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (p1' : validator32 p1)
  (u: unit {
    synth_injective f2
  })
: Tot (validator32 (parse_synth p1 f2))
= fun (input: pointer buffer8) (len: pointer U32.t) ->
  p1' input len

inline_for_extraction
let validate_nochk32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (p1' : validator_nochk32 p1)
  (u: unit {
    synth_injective f2
  })
: Tot (validator_nochk32 (parse_synth p1 f2))
= fun (input: pointer buffer8) (len: pointer U32.t) ->
  p1' input len

inline_for_extraction
let validate32_total_constant_size
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: U32.t)
  (u: unit {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz /\
    k.parser_kind_metadata.parser_kind_metadata_total = true
  })
: Tot (validator32 p)
= fun (input: pointer buffer8) (len: pointer U32.t) ->
  let len0 = B.index len 0ul in
  if U32.lt len0 sz
  then false
  else begin
    advance_slice_ptr input len sz;
    true
  end

inline_for_extraction
let validate_nochk32_constant_size
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: U32.t)
  (u: unit {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == U32.v sz
  })
: Tot (validator_nochk32 p)
= fun (input: pointer buffer8) (len: pointer U32.t) ->
  advance_slice_ptr input len sz

inline_for_extraction
val validate_nochk_truncate32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (v: validator_nochk32 p)
  (input: pointer buffer8)
  (sz: pointer U32.t)
: HST.Stack unit
  (requires (fun h ->
    is_slice_ptr h input sz /\
    Some? (parse p (B.as_seq h (B.get h input 0)))
  ))
  (ensures (fun h _ h' ->
    B.modifies_2 input sz h h' /\
    is_slice_ptr h' input sz /\ (
    let sq = B.as_seq h (B.get h input 0) in
    let (Some (res, consumed)) = parse p sq in
    U32.v (B.get h' sz 0) == consumed /\
    B.get h' input 0 == B.sub (B.get h input 0) 0ul (U32.uint_to_t consumed) /\ (
    let sq' = B.as_seq h' (B.get h' input 0) in
    sq' == Seq.slice sq 0 consumed /\ (
    let psq' = parse p sq' in
    Some? psq' /\ (
    let (Some (res', consumed')) = psq' in
    res == res' /\
    (consumed' <: nat) == (consumed <: nat)
  ))))))

let validate_nochk_truncate32 #k #t p v input sz =
  let h = HST.get () in
  let input0 = B.index input 0ul in
  let sz0 = B.index sz 0ul in
  v input sz ;
  let sz1 = B.index sz 0ul in
  let len' = U32.sub sz0 sz1 in
  let input' = B.sub input0 0ul len' in
  B.upd input 0ul input';
  B.upd sz 0ul len';
  let h' = HST.get () in
  let f () : Lemma (
    let (Some (res, consumed)) = parse p (B.as_seq h (B.get h input 0)) in
    let ps' = parse p (B.as_seq h' (B.get h' input 0)) in
    Some? ps' /\ (
    let (Some (res', consumed')) = ps' in
    res == res' /\ (consumed <: nat) == (consumed' <: nat)
  )) =
    assert (no_lookahead_weak_on p (B.as_seq h (B.get h input 0)) (B.as_seq h' (B.get h' input 0)))
  in
  f ()

inline_for_extraction
val nondep_then_fst
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (p1' : validator_nochk32 p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (input: pointer buffer8)
  (sz: pointer U32.t)
: HST.Stack unit
  (requires (fun h ->
    is_slice_ptr h input sz /\
    Some? (parse (p1 `nondep_then` p2) (B.as_seq h (B.get h input 0)))
  ))
  (ensures (fun h _ h' ->
    B.modifies_2 input sz h h' /\
    is_slice_ptr h' input sz /\ (
    let (Some (res1, consumed1)) = parse p1 (B.as_seq h (B.get h input 0)) in
    U32.v (B.get h' sz 0) == consumed1 /\
    B.get h' input 0 == B.sub (B.get h input 0) 0ul (U32.uint_to_t consumed1) /\ (
    let ps1' = parse p1 (B.as_seq h' (B.get h' input 0)) in
    Some? ps1' /\ (
    let (Some (res1', consumed1')) = parse p1 (B.as_seq h' (B.get h' input 0)) in
    res1 == res1' /\
    (consumed1 <: nat) == (consumed1' <: nat)
  )))))

let nondep_then_fst #k1 #t1 #p1 p1' #k2 #t2 p2 input sz =
  validate_nochk_truncate32 p1 p1' input sz

inline_for_extraction
val nondep_then_snd
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (p1' : validator_nochk32 p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (p2' : validator_nochk32 p2)
  (input: pointer buffer8)
  (sz: pointer U32.t)
: HST.Stack unit
  (requires (fun h ->
    is_slice_ptr h input sz /\
    Some? (parse (p1 `nondep_then` p2) (B.as_seq h (B.get h input 0)))
  ))
  (ensures (fun h _ h' ->
    B.modifies_2 input sz h h' /\
    is_slice_ptr h' input sz /\ (
    let sq = B.as_seq h (B.get h input 0) in
    let (Some (_, consumed1)) = parse p1 sq in
    let (Some (res2, consumed2)) = parse p2 (Seq.slice sq consumed1 (Seq.length sq)) in
    U32.v (B.get h' sz 0) == consumed2 /\
    B.get h' input 0 == B.sub (B.get h input 0) (U32.uint_to_t consumed1) (U32.uint_to_t consumed2) /\ (
    let ps2' = parse p2 (B.as_seq h' (B.get h' input 0)) in
    Some? ps2' /\ (
    let (Some (res2', consumed2')) = parse p2 (B.as_seq h' (B.get h' input 0)) in
    res2 == res2' /\
    (consumed2 <: nat) == (consumed2' <: nat)
  )))))

let nondep_then_snd #k1 #t1 #p1 p1' #k2 #t2 #p2 p2' input sz =
  p1' input sz;
  validate_nochk_truncate32 p2 p2' input sz

inline_for_extraction
let make_total_constant_size_parser32
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (t)))
  (u: unit {
    make_total_constant_size_parser_precond sz t f
  })
  (f' : ((s: buffer8) -> HST.Stack t
    (requires (fun h -> B.live h s /\ B.length s == sz))
    (ensures (fun h res h' ->
      h == h' /\
      res == f (B.as_seq h s)
  ))))
: Tot (parser32 (make_total_constant_size_parser sz t f))
= fun (input: pointer buffer8) (len: pointer U32.t) ->
  let b0 = B.index input 0ul in
  let b = B.sub b0 0ul sz' in
  let res = f' b in
  advance_slice_ptr input len sz';
  res
