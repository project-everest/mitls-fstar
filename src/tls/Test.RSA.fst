module Test.RSA

open FStar.HyperStack.ST
open FStar.HyperStack.IO

open FStar.Bytes
open CoreCrypto

let prefix = "Test.RSA"
let print_string s = print_string (prefix ^ ": " ^ s ^ ".\n")

(* Deprecated
val test: rsa_key -> St bool
let test pk = 
  let data = Bytes.bytes_of_hex "54859b342c49ea2a" in
  let encrypted = rsa_encrypt (RSAKey.repr_of_rsapkey pk) Pad_PKCS1 data in
  let decrypted = rsa_decrypt (RSAKey.repr_of_rsapkey pk) Pad_PKCS1 encrypted in
  match decrypted with
  | None ->
    begin
    print_string ("ERROR: decryption failed without producing a plaintext");
    false
    end
  | Some data' ->
    if data' = data then true
    else
      begin
      print_string ("ERROR: the decrypted data doesn't match the encrypted data");
      print_string ("Modulus:    " ^ (Bytes.hex_of_bytes pk.rsa_mod));
      print_string ("Exponent:   " ^ (Bytes.hex_of_bytes pk.rsa_pub_exp));
      print_string ("Plaintext:  " ^ (Bytes.hex_of_bytes data));    
      print_string ("Ciphertext: " ^ (Bytes.hex_of_bytes encrypted));    
      print_string ("Decryption: " ^ (Bytes.hex_of_bytes data'));
      false
      end
*)

// Called from Test.Main
let main () = C.EXIT_SUCCESS
(*
  let pk1: rsa_key = {
    rsa_mod = Bytes.bytes_of_hex "00aa36abce88acfdff55523c7fc4523f90efa00df3774a259f2e62b4c5d99cb5adb300a0285e5301930e0c70fb6876939ce616ce624a11e0086d341ebcaca0a1f5";
    rsa_pub_exp = Bytes.bytes_of_hex "11";
    rsa_prv_exp = Some (Bytes.bytes_of_hex "0a033748626487695f5f30bc38b98b44c2cd2dff434098cd20d8a138d090bf64797c3fa7a2cdcb3cd1e0bdba2654b4f9df8e8ae59d733d9f33b301624afd1d51")
  } in
  let pk2 = rsa_gen_key 1024 in
  let tpk1 = test pk1  in
  let tpk2 = test pk2  in
  if tpk1 && tpk2 then C.EXIT_SUCCESS else C.EXIT_FAILURE
*)
  


