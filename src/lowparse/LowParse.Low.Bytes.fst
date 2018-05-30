module LowParse.Low.Bytes
include LowParse.Spec.Bytes
include LowParse.Low.Combinators

module I32 = FStar.Int32

inline_for_extraction
let validate32_flbytes
  (sz: nat)
  (sz32: I32.t { I32.v sz32 == sz } )
: Tot (validator32 (parse_flbytes sz))
= validate32_total_constant_size (parse_flbytes sz) sz32 ()

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

#reset-options

