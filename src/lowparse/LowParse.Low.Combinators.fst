module LowParse.Low.Combinators
include LowParse.Low.Base
include LowParse.Spec.Combinators

module B = FStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

#reset-options "--z3rlimit 256 --max_fuel 32 --max_ifuel 32 --z3cliopt smt.arith.nl=false"

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
  if p1' input len
  then begin
    let res = p2' input len in
    res
  end else false

#reset-options "--z3rlimit 128 --max_fuel 32 --max_ifuel 32 --z3cliopt smt.arith.nl=false"

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

module M = FStar.Modifies

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
    Some? (parse_from_slice_ptr (nondep_then p1 p2) h input sz)
  ))
  (ensures (fun h _ h' ->
    M.modifies (loc_slice input sz) h h' /\
    includes_slice_ptr h h' input sz /\ (
    let (Some ((x, _), _)) = parse_from_slice_ptr (nondep_then p1 p2) h input sz in
    exactly_parse_from_slice_ptr p1 h' input sz == Some x
  )))

let nondep_then_fst #k1 #t1 #p1 p1' #k2 #t2 p2 input sz =
  truncate32 p1' input sz

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
    Some? (parse_from_slice_ptr (nondep_then p1 p2) h input sz)
  ))
  (ensures (fun h _ h' ->
    M.modifies (loc_slice input sz) h h' /\
    includes_slice_ptr h h' input sz /\ (
    let (Some ((_, x), _)) = parse_from_slice_ptr (nondep_then p1 p2) h input sz in
    exactly_parse_from_slice_ptr p2 h' input sz == Some x
  )))

let nondep_then_snd #k1 #t1 #p1 p1' #k2 #t2 #p2 p2' input sz =
  p1' input sz;
  truncate32 p2' input sz

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
