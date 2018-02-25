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
  | (s,f) :: xs -> check s f; iter xs

let handshake () =
  Handshake.main "CAFile.pem" "server-ecdsa.crt" "server-ecdsa.key" ()

let main (): St C.exit_code =
  ignore (FStar.Test.dummy ());
  if CoreCrypto.init () = 0 then
    begin
    print_string "✘ RNG initialization\n";
    C.EXIT_FAILURE
    end
  else
    begin
    print_string "✔ RNG initialization\n";
    iter [
      "BufferBytes", BufferBytes.main;
      "TLSConstants", TLSConstants.main;
      "StAE", StAE.main;
      "CommonDH", CommonDH.main;
      "Handshake", handshake;
      (* ADD NEW TESTS HERE *)
    ];
    C.EXIT_SUCCESS
    end
