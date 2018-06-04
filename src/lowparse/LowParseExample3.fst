module LowParseExample3
include LowParseExample3.Aux

open FStar.HyperStack.ST
open LowParse.TestLib.Low

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module Cast = FStar.Int.Cast
module I32 = FStar.Int32

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --using_facts_from '* -LowParse.Low.VLData'"

(*
let dummy
  (input: buffer8)
  (len: I32.t)
  (which: U32.t)
: HST.Stack U32.t
  (requires (fun h -> is_slice h input len))
  (ensures (fun _ _ _ -> True))
= HST.push_frame ();
  let res =
    if validate32 validate32_t input len
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
*)

#reset-options "--using_facts_from '* -LowParse'"

(** Test parser 'f' and formatter 'm' *)
let test_f_m : testbuffer_t = fun input inputlen ->
(* BUGBUG:  Complete this when low-level formatting is ready
  let result = f input in
  match result with
  | Some (v, offset) -> (
    let formattedresult = m v in
    Some (formattedresult, offset)
  )
  | _ -> None
*)
  None

#reset-options "--z3cliopt smt.arith.nl=false --using_facts_from '* -LowParse +LowParse.Low.Base'"

(** Run all unit tests, by calling test_buffer and test_file_buffer
    multiple times, with different parser+formatter pairs and 
    input data *)
let test (_:unit): Stack unit (requires (fun _ -> true)) (ensures (fun _ _ _ -> true)) =
  push_frame();
  let testbuffer:buffer8 = B.alloca_of_list [ 0x01uy; 0x02uy; 0x55uy; 0xaauy; 0x34uy; 0x45uy; 0xbauy; 0xabuy ] in
  test_buffer test_f_m "Example3 expect fail" testbuffer 8l;
(*  
  test_file_buffer test_f_m "Example3_pass.bin";
  test_file_buffer test_f_m "Example3_fail.bin";  
*)
  pop_frame()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  HST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  test ();
  pop_frame ();
  C.EXIT_SUCCESS
