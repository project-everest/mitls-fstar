module Test.TLSConstants
open FStar.Error
open TLSError
open TLSConstants

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
