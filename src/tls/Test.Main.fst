module Test.Main

open FStar.HyperStack.ST
open FStar.HyperStack.IO

inline_for_extraction
let check s (f: unit -> St C.exit_code): St unit =
  match f () with
  | C.EXIT_SUCCESS ->
      print_string "✔ ";
      print_string s;
      print_string "\n"
  | C.EXIT_FAILURE ->
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
let dummy (): St (UInt128.t -> UInt64.t) =
  FStar.Int.Cast.Full.uint128_to_uint64

let main (): St C.exit_code =
  ignore (FStar.Test.dummy ());
  ignore (dummy ());
  iter [
    "TLSConstants", TLSConstants.main;
    "CommonDH", CommonDH.main;
    "Handshake", Handshake.main;
    "StAE", StAE.main;
    (* ADD NEW TESTS HERE *)
  ];
  C.EXIT_SUCCESS
