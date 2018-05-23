module LowParseExample3
include LowParseExample3.Aux

module B = FStar.Buffer
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module Cast = FStar.Int.Cast

#reset-options "--z3rlimit 16"

let dummy
  (input: buffer8)
  (len: U32.t)
: HST.Stack bool
  (requires (fun h -> is_slice h input len))
  (ensures (fun _ _ _ -> True))
= HST.push_frame ();
  let input' = B.create input 1ul in
  let len' = B.create len 1ul in
  let res =
    if validate32_t input' len'
    then
      let x1 : U16.t = read_from_slice access_a parse32_u16 input len in
      let x2 : U32.t = read_from_slice access_b parse32_u32 input len in
      let x3 : U16.t = read_from_slice access_c parse32_u16 input len in
      (Cast.uint16_to_uint32 x1) `U32.lt` x2 && x2 `U32.lt` (Cast.uint16_to_uint32 x3)
    else false
  in
  HST.pop_frame ();
  res

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  HST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  C.EXIT_SUCCESS
