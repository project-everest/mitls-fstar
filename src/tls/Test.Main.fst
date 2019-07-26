module Test.Main

open FStar.HyperStack.ST
open FStar.HyperStack.IO

module NW = Negotiation.Writers // for extraction purposes only
module PBinders = ParsersAux.Binders // for verification purposes only

#set-options "--admit_smt_queries true"

type tf = unit -> St C.exit_code

inline_for_extraction
let check s (f: tf): St unit =
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

noextract inline_for_extraction 
let b2c b : St C.exit_code = if b then C.EXIT_SUCCESS else C.EXIT_FAILURE

let rec iter (xs:list (string * tf)) : St unit =
  match xs with
  | [] -> ()
  | (s,f) :: xs -> check s f; iter xs

let handshake () =
  Test.Handshake.main "CAFile.pem" "server-ecdsa.crt" "server-ecdsa.key" ()

let iv () = 
  IV.test(); 
  C.EXIT_SUCCESS

let rng_initialization() = b2c (Random.init() <> 0ul)
let cookie () =  b2c (TLS.Cookie.test())

let main (): St C.exit_code =
  MITLS.Init.mitls_init ();
  iter [
    "RNG initialization", rng_initialization;
    "BufferBytes", BufferBytes.main;
    "TLSConstants", TLSConstants.main;
    "AEAD", AEAD.main;
    "StAE", StAE.main;
    "CommonDH", CommonDH.main;
    "Parsers", Parsers.main;
    "Handshake", handshake;
    "IV", iv;
    "Cookie", cookie;
    "Rekey", KDF.Rekey.test_rekey;
    (* ADD NEW TESTS HERE *)
  ];
  C.EXIT_SUCCESS
