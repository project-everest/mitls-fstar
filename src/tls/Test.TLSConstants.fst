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
   Rsa_pkcs1_md5
  ; Rsa_pkcs1_sha1
  ; Ecdsa_md5
  ; Ecdsa_sha1
  ; Rsa_pkcs1_sha256
  ; Rsa_pkcs1_sha384
  ; Rsa_pkcs1_sha512
  ; Ecdsa_secp256r1_sha256
  ; Ecdsa_secp384r1_sha384
  ; Ecdsa_secp521r1_sha512
  ;Rsa_pss_rsae_sha256
  ; Rsa_pss_rsae_sha384
  ; Rsa_pss_rsae_sha512
  ; Ed25519
  ; Ed448
  ; Rsa_pss_pss_sha256
  ; Rsa_pss_pss_sha384
  ; Rsa_pss_pss_sha512
  ; Unknown_signatureScheme 0xFFFFus
  ] in
  let bytes = signatureSchemeListBytes algs in
  match parseSignatureSchemeList bytes with
  | Correct algs' ->
    let bytes' = signatureSchemeListBytes algs' in
    if bytes = bytes'
    then None //all ok
    else Some (Inr (bytes, bytes')) //failed to round trip
  | Error (ad, msg) ->
    Some (Inl (bytes, string_of_alert ad, msg)) //failed to parse back

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
