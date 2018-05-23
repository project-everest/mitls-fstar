module LowParseExample3
include LowParseExample3.Aux

module B = FStar.Buffer
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module Cast = FStar.Int.Cast

#reset-options "--z3rlimit 32"

let dummy
  (input: buffer8)
  (len: U32.t)
  (which: U32.t)
: HST.Stack U32.t
  (requires (fun h -> is_slice h input len))
  (ensures (fun _ _ _ -> True))
= HST.push_frame ();
  let input' = B.create input 1ul in
  let len' = B.create len 1ul in
  let res =
    if validate32_t input' len'
    then
      if which = 42ul
      then
        let x : U16.t = read_from_buffer access_a parse32_u16 input in
        Cast.uint16_to_uint32 x
      else if which = 1729ul
      then
        read_from_buffer access_b parse32_u32 input
      else
        let x : U16.t = read_from_buffer access_c parse32_u16 input in
        Cast.uint16_to_uint32 x
    else 0ul
  in
  HST.pop_frame ();
  res

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  HST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  C.EXIT_SUCCESS
