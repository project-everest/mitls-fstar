module Test.TLSConstants

open FStar.Error
open FStar.HyperStack.ST

open TLSError
open TLSConstants

#set-options "--admit_smt_queries true"

let test_signatureSchemeListBytes ()
  : Stack (option (either (FStar.Bytes.bytes * string * string)
                          (FStar.Bytes.bytes * FStar.Bytes.bytes)))
          (requires (fun _ -> True))
          (ensures (fun _ _ _ -> True)) =
  let algs = [
    RSA_PKCS1_SHA256
  ; RSA_PKCS1_SHA384
  ; RSA_PKCS1_SHA512
  // ECDSA algorithms
  ; ECDSA_SECP256R1_SHA256
  ; ECDSA_SECP384R1_SHA384
  ; ECDSA_SECP521R1_SHA512
  // RSASSA-PSS algorithms
  ; RSA_PSS_SHA256
  ; RSA_PSS_SHA384
  ; RSA_PSS_SHA512
  // Legacy algorithms
  ; RSA_PKCS1_SHA1
  ; RSA_PKCS1_MD5SHA1 // Only used internally, with codepoint 0xFFFF (PRIVATE_USE)
  ; ECDSA_SHA1
  // Reserved Code Points
  ; DSA_SHA1
  ; DSA_SHA256
  ; DSA_SHA384
  ; DSA_SHA512 ] in
  let bytes = signatureSchemeListBytes algs in
  match parseSignatureSchemeList bytes with
  | Correct algs' ->
    let bytes' = signatureSchemeListBytes algs' in
    if bytes = bytes'
    then None //all ok
    else Some (Inr (bytes, bytes')) //failed to round trip
  | Error (ad, msg) ->
    Some (Inl (bytes, string_of_ad ad, msg)) //failed to parse back

let print s = FStar.HyperStack.IO.print_string s

// called from Test.Main
let main () : St C.exit_code =
  match test_signatureSchemeListBytes() with
  | None ->
    C.EXIT_SUCCESS

  | Some (Inr (b0, b1)) ->
    print (Printf.sprintf "Failed to round trip: %s <> %s\n"
                           (Bytes.hex_of_bytes b0)
                           (Bytes.hex_of_bytes b1));
    C.EXIT_FAILURE

  | Some (Inl (b, ad, msg)) ->
    print (Printf.sprintf "Failed to round trip: %s, ad=%s, msg=%s\n"
                           (Bytes.hex_of_bytes b)
                           ad
                           msg);
    C.EXIT_FAILURE
