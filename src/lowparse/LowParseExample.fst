module LowParseExample

open FStar.HyperStack.ST
open FStar.Bytes

let f (input: FStar.Bytes.bytes) : Tot (option (LowParseExample.Aux.t * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t input

let g (input: FStar.Bytes.bytes) : Tot (option (LowParse.SLow.array LowParseExample.Aux.t 18 * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t_array input

let j (input: FStar.Bytes.bytes) : Tot (option (LowParse.SLow.vlarray LowParseExample.Aux.t 5 7 * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t_vlarray input

let m (x: LowParseExample.Aux.t) : Tot FStar.Bytes.bytes =
  LowParseExample.Aux.serialize32_t x

let s (x: LowParse.SLow.array LowParseExample.Aux.t 18) : Tot FStar.Bytes.bytes =
  LowParseExample.Aux.serialize32_t_array x

#reset-options "--using_facts_from '* -LowParse'"
let test (_:unit): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  let test1 = "01020304" in
  let testbytes = bytes_of_hex test1 in
  let result = f testbytes in 
  pop_frame()

// BUGBUG: HACK for Kremlin kremlib issue
// Dummy function, to call some FStar.Bytes functions.  This
// causes Kremlin to emit type declarations that are needed bytes
// krembytes.h.
let dummy (_:unit): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  assume false;
  push_frame();
  let p = twobytes (0uy, 1uy) in
  let p = split p 1ul in
  let p = iutf8_opt (utf8_encode "Napoléon") in
  pop_frame()

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
  test ();
  pop_frame ();
  C.EXIT_SUCCESS
