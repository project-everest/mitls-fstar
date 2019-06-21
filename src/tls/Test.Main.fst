module Test.Main

open FStar.HyperStack.ST
open FStar.HyperStack.IO

module NW = Negotiation.Writers // for extraction purposes only
module PBinders = ParsersAux.Binders // for verification purposes only

#set-options "--admit_smt_queries true"

inline_for_extraction
let check s (f: unit -> St C.exit_code): St unit =
  match f () with
  | C.EXIT_SUCCESS ->
      C.(ignore (fflush stdout); ignore (fflush stderr));
      print_string "✔ ";
      print_string s;
      print_string "\n"
  | C.EXIT_FAILURE ->
      C.(ignore (fflush stdout); ignore (fflush stderr));
      print_string "✘ ";
      print_string s;
      print_string "\n";
      C.exit 255l

let rec iter (xs:list (string * (unit -> St C.exit_code))) : St unit =
  match xs with
  | [] -> ()
  | (s,f) :: xs -> check s f; iter xs

let handshake () =
  Test.Handshake.main "CAFile.pem" "server-ecdsa.crt" "server-ecdsa.key" ()

let iv () = 
  IV.test(); 
  C.EXIT_SUCCESS

let main (): St C.exit_code =
  MITLS.Init.mitls_init ();
  if Random.init () = 0ul then
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
      "AEAD", AEAD.main;
      "StAE", StAE.main;
      "CommonDH", CommonDH.main;
      "Parsers", Parsers.main;
      "Handshake", handshake;
      "IV", iv;
      "Rekey", KDF.Rekey.test_rekey;
      (* ADD NEW TESTS HERE *)
    ];
    C.EXIT_SUCCESS
    end
