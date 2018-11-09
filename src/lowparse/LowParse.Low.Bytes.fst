module LowParse.Low.Bytes
include LowParse.Spec.Bytes
include LowParse.Low.Combinators
include LowParse.Low.VLData
include LowParse.Low.Int

module U32 = FStar.UInt32
module HS = FStar.HyperStack
module B = LowStar.Buffer
module BY = LowParse.Bytes32
module HST = FStar.HyperStack.ST
module U8 = FStar.UInt8

inline_for_extraction
let validate_flbytes
  [| validator_cls |]
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz /\ sz <= U32.v validator_max_length } )
: Tot (validator (parse_flbytes sz))
= validate_total_constant_size (parse_flbytes sz) sz32 ()

inline_for_extraction
let jump_flbytes
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (jumper (parse_flbytes sz))
= jump_constant_size (parse_flbytes sz) sz32 ()

let valid_flbytes_intro
  (h: HS.mem)
  (sz: nat { sz < 4294967296 } )
  (s: slice)
  (pos: U32.t)
: Lemma
  (requires (U32.v pos + sz <= U32.v s.len /\ live_slice h s))
  (ensures (
    valid_content_pos (parse_flbytes sz) h s pos (BY.hide (B.as_seq h (B.gsub s.base pos (U32.uint_to_t sz)))) (pos `U32.add` U32.uint_to_t sz)
  ))
= valid_facts (parse_flbytes sz) h s pos

let clens_flbytes_slice
  (sz: nat)
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= sz } )
: Tot (clens #(BY.lbytes sz) (fun _ -> True) (BY.lbytes (U32.v to - U32.v from)))
= {
  clens_get = (fun (x: BY.lbytes sz) -> (BY.slice x from to <: BY.lbytes (U32.v to - U32.v from)));
}

let gaccessor_flbytes_slice
  (sz: nat { sz < 4294967296 } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= sz } )
: Tot (gaccessor (parse_flbytes sz) (parse_flbytes (U32.v to - U32.v from)) (clens_flbytes_slice sz from to))
= fun (input: bytes) -> (
  begin
    if Seq.length input < sz
    then (0, 0) // dummy
    else (U32.v from, U32.v to - U32.v from)
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_flbytes sz) (parse_flbytes (U32.v to - U32.v from)) (clens_flbytes_slice sz from to) input res )))

inline_for_extraction
let accessor_flbytes_slice
  (sz: nat { sz < 4294967296 } )
  (from: U32.t)
  (to: U32.t {U32.v from <= U32.v to /\ U32.v to <= sz } )
: Tot (accessor (gaccessor_flbytes_slice sz from to))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_flbytes_slice sz from to) input pos in
  pos `U32.add` from

let clens_flbytes_get
  (sz: nat)
  (i: U32.t { U32.v i < sz } )
: Tot (clens #(BY.lbytes sz) (fun _ -> True) byte)
= {
  clens_get = (fun (x: BY.lbytes sz) -> (BY.get x i <: byte));
}

let gaccessor_flbytes_get
  (sz: nat { sz < 4294967296 } )
  (i: U32.t { U32.v i < sz } )
: Tot (gaccessor (parse_flbytes sz) (parse_u8) (clens_flbytes_get sz i))
= fun (input: bytes) -> (
  begin
    let res =
      if Seq.length input <= U32.v i
      then (0, 0) // dummy
      else (U32.v i, 1)
    in
    let g () : Lemma
      (requires (gaccessor_pre (parse_flbytes sz) parse_u8 (clens_flbytes_get sz i) input))
      (ensures (gaccessor_post (parse_flbytes sz) parse_u8 (clens_flbytes_get sz i) input res))
    = assert (res == (U32.v i, 1));
      parse_u8_spec (Seq.slice input (U32.v i) (U32.v i + 1))
    in
    Classical.move_requires g ();
    res
  end <: Ghost (nat & nat) (requires True) (ensures (fun res -> gaccessor_post' (parse_flbytes sz) parse_u8 (clens_flbytes_get sz i) input res )))

inline_for_extraction
let accessor_flbytes_get
  (sz: nat { sz < 4294967296 } )
  (i: U32.t { U32.v i < sz } )
: Tot (accessor (gaccessor_flbytes_get sz i))
= fun input pos ->
  let h = HST.get () in
  [@inline_let] let _ = slice_access_eq h (gaccessor_flbytes_get sz i) input pos in
  pos `U32.add` i

(*

module M = LowStar.Modifies

inline_for_extraction
let read_byte
  (sz: nat { sz < 4294967296 } )
  (i: U32.t)
  (input: buffer8)
: HST.Stack byte
  (requires (fun h -> B.live h input /\ Some? (parse (parse_flbytes sz) (B.as_seq h input)) /\ U32.v i < sz))
  (ensures (fun h res h' ->
    h' == h /\
    U32.v i < B.length input /\ (
    let (Some (v, consumed)) = parse (parse_flbytes sz) (B.as_seq h input) in
    (consumed <: nat) == sz /\
    res == BY.get v i
  )))
= B.index input i

#set-options "--z3rlimit 16"

inline_for_extraction
let slice_bytes
  (sz: nat { sz < 4294967296 } )
  (i: U32.t)
  (sz' : U32.t { U32.v i + U32.v sz' <= sz } )
: Tot (accessor (parse_flbytes sz) (parse_flbytes (U32.v sz')) (fun x y -> y == BY.slice x i (U32.add i sz')))
= fun input ->
  B.sub input i sz'

inline_for_extraction
let validate32_all_bytes
: validator32 (parse_all_bytes)
= fun input len ->
    let h = HST.get () in
    0l

inline_for_extraction
let validate32_bounded_vlbytes'
  (min: nat)
  (min32: U32.t)
  (max: nat { min <= max /\ max > 0 /\ max < 2147483648 })
  (max32: U32.t)
  (sz32: I32.t)
  (u: squash (
    U32.v min32 == min /\ U32.v max32 == max /\
    I32.v sz32 == log256' max
  ))
: Tot (validator32 (parse_bounded_vlbytes' min max))
= validate32_bounded_vldata_strong min min32 max max32 (serialize_all_bytes) validate32_all_bytes sz32 ()

inline_for_extraction
let validate32_bounded_vlbytes
  (min: nat)
  (min32: U32.t)
  (max: nat { min <= max /\ max > 0 /\ max < 2147483648 } )
  (max32: U32.t)
  (sz32: I32.t)
  (u: squash (
    U32.v min32 == min /\ U32.v max32 == max /\
    I32.v sz32 == log256' max
  ))
: Tot (validator32 (parse_bounded_vlbytes min max))
= validate32_synth
    (validate32_bounded_vlbytes' min min32 max max32 sz32 ())
    (synth_bounded_vlbytes min max)
    ()
