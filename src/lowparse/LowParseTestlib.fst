module LowParseTestlib

open FStar.HyperStack.ST
open FStar.Bytes
open FStar.HyperStack.IO
open FStar.Printf
open LowParse.Low.Base

module B = FStar.Buffer
module U32 = FStar.UInt32

#reset-options "--using_facts_from '* -LowParse'"
#reset-options "--z3cliopt smt.arith.nl=false"

(** The type of a unit test.  It takes an input Bytes, parses it,
    and returns a newly formatted Bytes.  Or it returns None if
    there is a fail to parse. *)
type test_t = (input:FStar.Bytes.bytes) -> Stack (option (FStar.Bytes.bytes * U32.t)) (fun _ -> true) (fun _ _ _ -> true)

(** The type of a unit test.  It takes an input buffer8, parses it,
    and returns a newly formatted buffer8.  Or it returns None if
    there is a fail to parse. *)
type testbuffer_t = (input:buffer8) -> (inputlen:U32.t) -> Stack (option (buffer8 * U32.t)) 
  (requires(fun h -> is_slice h input inputlen ))
  (ensures(fun h0 y h1 ->
    match y with
    | None -> true
    | Some (r,o) -> is_slice h1 r o ))

assume val load_file: (filename:string) -> Tot FStar.Bytes.bytes
assume val load_file_buffer: (filename:string) -> Tot (buffer8 * U32.t)

(** Test one parser+formatter pair against an in-memory buffer of Bytes *)
let test_bytes (t:test_t) (testname:string) (input:FStar.Bytes.bytes): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  print_string (sprintf "==== Testing Bytes %s ====\n" testname);
  let result = t input in
  (match result with
  | Some (formattedresult, offset) -> (
    if U32.gt offset (len input) then (
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
  print_string (sprintf "==== Finished %s ====\n" testname);
  pop_frame()

(** Test one parser+formatter pair against a string of hex bytes, as Bytes *)
let test_string (t:test_t) (testname:string) (inputstring:string): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  let input = bytes_of_hex inputstring in
  test_bytes t testname input;
  pop_frame()
  
(** Test one parser+formatter pair against a disk file, as Bytes *)
let test_file (t:test_t) (filename:string): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  let input = load_file filename in
  test_bytes t filename input;
  pop_frame()

(** Test one parser+formatter pair against an in-memory buffer of UInt8.t *)
let test_buffer (t:testbuffer_t) (testname:string) (input:buffer8) (inputlen:U32.t)
: Stack unit 
(requires (fun h -> is_slice h input inputlen))
(ensures (fun _ _ _ -> true)) =
  push_frame();
  print_string (sprintf "==== Testing buffer %s ====\n" testname);
  let result = t input inputlen in
  (match result with
  | Some (formattedresult, offset) -> (
    if U32.lte offset inputlen then (
      if B.eqb input formattedresult offset then
        print_string "Formatted data matches original input data\n"
      else (
        print_string "FAIL:  formatted data does not match original input data\n"
      )
    ) else (  
      print_string "Invalid length return - it is longer than the input buffer!"
    ))
  | _ -> print_string "Failed to parse\n"
  ); 
  print_string (sprintf "==== Finished %s ====\n" testname);
  pop_frame()

(** Test one parser+formatter pair against a disk file, using buffer *)
let test_file_buffer (t:testbuffer_t) (filename:string): Stack unit (fun _ -> true) (fun _ _ _ -> true) =
  push_frame();
  let input, inputlen = load_file_buffer filename in
  (*test_buffer t filename input inputlen;*)
  pop_frame()
