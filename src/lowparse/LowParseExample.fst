module LowParseExample

open FStar.HyperStack.ST
open FStar.Bytes
open FStar.HyperStack.IO
open FStar.Printf

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

(** The type of a unit test.  It takes an input buffer, parses it,
    and returns a newly formatted buffer.  Or it returns None if
    there is a fail to parse. *)
type test_t = (input:FStar.Bytes.bytes) -> Stack (option (FStar.Bytes.bytes * FStar.UInt32.t)) (fun _ -> true) (fun _ _ _ -> true)

(** Test parser 'f' and formatter 'm' *)
let test_f_m (input:FStar.Bytes.bytes): Stack (option (FStar.Bytes.bytes * FStar.UInt32.t)) (fun _ -> true) (fun _ _ _ -> true) =
  let result = f input in
  match result with
  | Some (v, offset) -> (
    let formattedresult = m v in
    Some (formattedresult, offset)
  )
  | _ -> None

(** Test one parser+formatter pair *)
let test_one (t:test_t) (filename:string) (input:FStar.Bytes.bytes): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  print_string (sprintf "==== Testing %s ====\n" filename);
  let result = t input in
  (match result with
  | Some (formattedresult, offset) -> (
    if FStar.UInt32.gt offset (len input) then (
      print_string "Invalid length return - it is longer than the input buffer!"
    ) else (  
      let inputslice = FStar.Bytes.slice input 0ul offset in
      if formattedresult = inputslice then
        print_string "Formatted data matches original input data\n"
      else (
        print_string "FAIL:  formatted data does not match original input data\n"
      )
    )
    )
  | _ -> print_string "Failed to parse\n"
  ); 
  print_string (sprintf "==== Finished %s ====\n" filename);
  pop_frame()
  
(** Run all unit tests, by calling test_one multiple times, with
    different parser+formatter pairs and input data *)
let test (_:unit): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  let test1 = "120102" in
  let testbytes = bytes_of_hex test1 in
  test_one test_f_m "test.bin" testbytes;

  let test1 = "110102" in
  let testbytes = bytes_of_hex test1 in
  test_one test_f_m "test_expect_fail.bin" testbytes;
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
