module LowParse.Low.Combinators
include LowParse.Low.Base
include LowParse.Spec.Combinators

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module Cast = FStar.Int.Cast

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false"

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

#reset-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false"

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

#reset-options

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
  let h = HST.get () in // FIXME: WHY WHY WHY?
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
  let h = HST.get () in // FIXME: WHY WHY WHY?
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

inline_for_extraction
let validate32_filter
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v32: validator32 p)
  (p32: parser32 p)
  (f: (t -> GTot bool))
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Tot (validator32 (parse_filter p f))
= fun input len ->
  let res = v32 input len in
  if res `I32.lt` 0l
  then res
  else
    let va = p32 input in
    if f' va
    then res
    else -1l

module MO = LowStar.Modifies

inline_for_extraction
let parse32_filter'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (f: (t -> GTot bool))
  (input: buffer8)
: HST.Stack (x: t { f x == true } )
  (requires (fun h -> B.live h input /\ Some? (parse (parse_filter p f) (B.as_seq h input))))
  (ensures (fun h res h' ->
    MO.modifies MO.loc_none h h' /\
    B.live h' input /\ (
    let z = parse p (B.as_seq h input) in
    Some? z /\ (
    let (Some (v, _)) = z in
    f res == true /\
    v == res
  ))))
= p32 input

inline_for_extraction
let parse32_filter
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (f: (t -> GTot bool))
: Tot (parser32 (parse_filter p f))
= fun input ->
  parse32_filter' p32 f input

inline_for_extraction
let validate32_and_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (v1: validator32 p1)
  (p1': parser32 p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: (t1 -> parser k2 t2))
  (v2: ((x1: t1) -> validator32 (p2 x1)))
  (u: unit {
    and_then_cases_injective p2
  })
: Tot (validator32 (p1 `and_then` p2))
= fun input len ->
  let res = v1 input len in
  if res `I32.lt` 0l
  then res
  else
    let va = p1' input in
    v2 va (B.offset input (Cast.int32_to_uint32 (len `I32.sub` res))) res

#set-options "--z3rlimit 32"

inline_for_extraction
let validate32_filter_and_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (v1: validator32 p1)
  (p1': parser32 p1)
  (f: (t1 -> GTot bool))
  (f' : ((x: t1) -> Tot (y: bool { y == f x } )))
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: ((x: t1 { f x == true} ) -> parser k2 t2))
  (v2: ((x1: t1 { f x1 == true } ) -> validator32 (p2 x1)))
  (u: unit {
    and_then_cases_injective p2
  })
: Tot (validator32 (parse_filter p1 f `and_then` p2))
= fun input len ->
  let res = v1 input len in
  if res `I32.lt` 0l
  then res
  else
    let va = p1' input in
    if f' va
    then
      v2 va (B.offset input (Cast.int32_to_uint32 (len `I32.sub` res))) res
    else -1l

// #reset-options

let exactly_contains_valid_data_nondep_then
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (b: buffer8)
  (lo: U32.t)
  (x1: t1)
  (mi: U32.t)
  (x2: t2)
  (hi: U32.t)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    exactly_contains_valid_data h p1 b lo x1 mi /\
    exactly_contains_valid_data h p2 b mi x2 hi
  ))
  (ensures (
    exactly_contains_valid_data h (p1 `nondep_then` p2) b lo (x1, x2) hi
  ))
  [SMTPat (exactly_contains_valid_data h p1 b lo x1 mi);
   SMTPat (exactly_contains_valid_data h p2 b mi x2 hi);]
= assert (no_lookahead_on p1 (B.as_seq h (B.gsub b lo (U32.sub mi lo))) (B.as_seq h (B.gsub b lo (U32.sub hi lo))));
  assert (injective_precond p1 (B.as_seq h (B.gsub b lo (U32.sub mi lo))) (B.as_seq h (B.gsub b lo (U32.sub hi lo))))

let seq_append_slice
  (#t: Type)
  (s: Seq.seq t)
  (l1 l2 l3: nat)
: Lemma
  (requires (l1 <= l2 /\ l2 <= l3 /\ l3 <= Seq.length s))
  (ensures (Seq.append (Seq.slice s l1 l2) (Seq.slice s l2 l3) == Seq.slice s l1 l3))
= assert (Seq.append (Seq.slice s l1 l2) (Seq.slice s l2 l3) `Seq.equal` Seq.slice s l1 l3)

let contains_valid_serialized_data_or_fail_nondep_then
  (h: HS.mem)
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (b: buffer8)
  (lo: I32.t)
  (x1: t1)
  (mi: I32.t)
  (x2: t2)
  (hi: I32.t)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    contains_valid_serialized_data_or_fail h s1 b lo x1 mi /\
    contains_valid_serialized_data_or_fail h s2 b mi x2 hi
  ))
  (ensures (
    contains_valid_serialized_data_or_fail h (serialize_nondep_then _ s1 () _ s2) b lo (x1, x2) hi
  ))
  [SMTPat (contains_valid_serialized_data_or_fail h s1 b lo x1 mi);
   SMTPat (contains_valid_serialized_data_or_fail h s2 b mi x2 hi);]
= if I32.v lo < 0
  then ()
  else if I32.v mi < 0
  then ()
  else if I32.v hi < 0
  then ()
  else
    seq_append_slice (B.as_seq h b) (I32.v lo) (I32.v mi) (I32.v hi)
