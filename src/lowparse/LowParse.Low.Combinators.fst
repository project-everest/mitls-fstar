module LowParse.Low.Combinators
include LowParse.Low.Base
include LowParse.Spec.Combinators

module B = FStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module Cast = FStar.Int.Cast
module M = LowParse.Math

let int32_to_uint32_pos
  (x: I32.t)
: Lemma
  (requires (I32.v x >= 0))
  (ensures (U32.v (Cast.int32_to_uint32 x) == I32.v x))
  [SMTPat (U32.v (Cast.int32_to_uint32 x))]
= M.modulo_lemma (I32.v x) (pow2 32)

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
= fun (input: buffer8) (len: I32.t) ->
  let h = HST.get () in
  let x1 = p1' input len in
  if x1 `I32.lt` 0l
  then x1 // TODO: more coding on error
  else
    p2' (B.offset input (Cast.int32_to_uint32 (len `I32.sub` x1))) x1

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
= fun (input: buffer8) ->
  let off1 = p1' input in
  let off2 = p2' (B.offset input off1) in
  U32.add off1 off2

inline_for_extraction
let validate32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser k t1)
  (p1' : validator32 p1)
  (f2: t1 -> GTot t2)
  (u: unit {
    synth_injective f2
  })
: Tot (validator32 (parse_synth p1 f2))
= fun (input: buffer8) (len: I32.t) ->
  p1' input len

inline_for_extraction
let validate_nochk32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser k t1)
  (p1' : validator_nochk32 p1)
  (f2: t1 -> GTot t2)
  (u: unit {
    synth_injective f2
  })
: Tot (validator_nochk32 (parse_synth p1 f2))
= fun (input: buffer8) ->
  p1' input

inline_for_extraction
let validate32_total_constant_size
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: I32.t)
  (u: unit {
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_low == I32.v sz /\
    k.parser_kind_metadata.parser_kind_metadata_total = true
  })
: Tot (validator32 p)
= fun (input: buffer8) (len: I32.t) ->
  if I32.lt len sz
  then -1l
  else
    let h = HST.get () in // TODO: WHY WHY WHY?
    len `I32.sub` sz

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
= fun (input: buffer8) ->
  let h = HST.get () in // TODO: WHY WHY WHY?
  sz

inline_for_extraction
let accessor_weaken
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#rel: (t1 -> t2 -> GTot Type0))
  (a: accessor p1 p2 rel)
  (rel': (t1 -> t2 -> GTot Type0))
  (u: unit { forall x1 x2 . rel x1 x2 ==> rel' x1 x2 } )
: Tot (accessor p1 p2 rel')
= fun input -> a input

let rel_compose (#t1 #t2 #t3: Type) (r12: t1 -> t2 -> GTot Type0) (r23: t2 -> t3 -> GTot Type0) (x1: t1) (x3: t3) : GTot Type0 =
  exists x2 . r12 x1 x2 /\ r23 x2 x3

inline_for_extraction
let accessor_compose
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#k3: parser_kind)
  (#t3: Type)
  (#p3: parser k3 t3)
  (#rel12: (t1 -> t2 -> GTot Type0))
  (#rel23: (t2 -> t3 -> GTot Type0))
  (a12: accessor p1 p2 rel12)
  (a23: accessor p2 p3 rel23)
: Tot (accessor p1 p3 (rel12 `rel_compose` rel23))
= fun input ->
    a23 (a12 input)

inline_for_extraction
let accessor_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f: t1 -> GTot t2)
  (u: unit {  synth_injective f } )
: Tot (accessor (parse_synth p1 f) p1 (fun x y -> f y == x))
= fun input ->
  let h = HST.get () in
  [@inline_let]
  let _ = assert (Some? (parse p1 (B.as_seq h input))) in
  input

inline_for_extraction
val nondep_then_fst
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
: Tot (accessor (p1 `nondep_then` p2) p1 (fun x y -> y == fst x))

let nondep_then_fst #k1 #t1 p1 #k2 #t2 p2 input =
  let h = HST.get () in
  [@inline_let]
  let _ = assert (Some? (parse p1 (B.as_seq h input))) in
  input

inline_for_extraction
val nondep_then_snd
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (p1' : validator_nochk32 p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
: Tot (accessor (p1 `nondep_then` p2) p2 (fun x y -> y == snd x))

let nondep_then_snd #k1 #t1 #p1 p1' #k2 #t2 p2 input =
  B.offset input (p1' input)

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
= fun (input: buffer8) ->
  f' (B.sub input 0ul sz')
