module LowParseExample4
include LowParseExample4.Aux

module LPC = LowParse.Spec.Combinators
module LPI = LowParse.Low.Int
module LP = LowParse.Low.Base

module U32 = FStar.UInt32
module U16 = FStar.UInt16
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

#set-options "--z3rlimit 32"

let main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
   HST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
=
  fun _ _ ->
  HST.push_frame ();
  let b : LP.buffer8 = B.alloca 0uy 8ul in
//  assert (B.len b == 8ul);
  LPI.serialize32_u16 b 0ul 18us;
  LPI.serialize32_u16 b 2ul 42us;
  LPI.serialize32_u32 b 4ul 1729ul;
  let h = HST.get () in
  admit ();
  assert (LP.exactly_contains_valid_data h parse_t b 0ul ({ inner = ({ left = 18us; right = 42us; }); last = 1729ul;}) 8ul);
  HST.pop_frame ();
  C.EXIT_SUCCESS
