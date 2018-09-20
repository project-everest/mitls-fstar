module LowParse.Low.Bytes
include LowParse.Spec.Bytes
include LowParse.Low.Combinators
include LowParse.Low.VLData

module I32 = FStar.Int32

class error_flbytes_cls = {
  error_flbytes_not_enough_input: error_code;
}

inline_for_extraction
let validate32_flbytes
  [| error_flbytes_cls |]
  (sz: nat)
  (sz32: I32.t { I32.v sz32 == sz } )
: Tot (validator32 (parse_flbytes sz))
= [@inline_let]
  let _ = { error_total_constant_size_not_enough_input = error_flbytes_not_enough_input } in
  validate32_total_constant_size (parse_flbytes sz) sz32 ()

module U32 = FStar.UInt32

inline_for_extraction
let validate_nochk32_flbytes
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator_nochk32 (parse_flbytes sz))
= validate_nochk32_constant_size (parse_flbytes sz) sz32 ()

module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies
module BY = LowParse.Bytes32

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
  [| error_vldata_cls |]
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
  [| error_vldata_cls |]
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
