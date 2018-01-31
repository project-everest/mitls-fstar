module Test.Main

open FStar.HyperStack.ST
open FStar.HyperStack.IO

inline_for_extraction
let check s (f: unit -> St C.exit_code): St unit =
  match f () with
  | C.EXIT_SUCCESS ->
      C.(fflush stdout; fflush stderr);
      print_string "✔ ";
      print_string s;
      print_string "\n"
  | C.EXIT_FAILURE ->
      C.(fflush stdout; fflush stderr);
      print_string "✘ ";
      print_string s;
      print_string "\n";
      C.exit 255l

let rec iter xs: St unit =
  match xs with
  | [] -> ()
  | x :: xs ->
      let s = fst x in
      let f = snd x in
      check s f; iter xs

// Curve25519.h wants this, but externally visible... make it a cross-module call.
let dummy (): St UInt64.t =
  let dummy = FStar.Int.Cast.Full.uint64_to_uint128 0UL in
  FStar.Int.Cast.Full.uint128_to_uint64 dummy

let main (): St C.exit_code =
  ignore (FStar.Test.dummy ());
  ignore (dummy ());
  iter [
    "RSA", RSA.main;
    "TLSConstants", TLSConstants.main;
    "StAE", StAE.main;
    "CommonDH", CommonDH.main;
    "Handshake", Handshake.main;
    (* ADD NEW TESTS HERE *)
  ];
  C.EXIT_SUCCESS
