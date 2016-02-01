(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
(* STATUS : JK : assumed two arrays because, has to be fixed *)

#light "off"

module TLSPRF

(* Low-level (bytes -> byte) PRF implementations for TLS *)

open Platform.Bytes
open TLSConstants
open TLSInfo
open HMAC
open CoreCrypto

(* SSL3 *)

let ssl_prf_int secret label seed =
  let allData = utf8 label @| secret @| seed in
  let step1 = hash SHA1 allData in
  let allData = secret @| step1 in
  hash MD5 allData

let ssl_prf secret seed nb =
  let gen_label (i:int) = String.make (i+1) (Char.char_of_int (Char.int_of_char 'A' + i)) in 
  let rec apply_prf res n =
    if n > nb then
      let r,_ = split res nb in r
    else
        let step1 = ssl_prf_int secret (gen_label (n/16)) seed in
        apply_prf (res @| step1) (n+16)
  in
  apply_prf empty_bytes  0

(*
let ssl_sender_client = abytes [|0x43uy; 0x4Cuy; 0x4Euy; 0x54uy|]
let ssl_sender_server = abytes [|0x53uy; 0x52uy; 0x56uy; 0x52uy|]
 *)
(* JK : Temporary fix *)
assume val ssl_sender_client: bytes
assume val ssl_sender_server: bytes

let ssl_verifyData ms role data =
  let ssl_sender =
    match role with
    | Client -> ssl_sender_client
    | Server -> ssl_sender_server
  in
  let mm = data @| ssl_sender @| ms in
  let inner_md5  = hash MD5 (mm @| ssl_pad1_md5) in
  let outer_md5  = hash MD5 (ms @| ssl_pad2_md5 @| inner_md5) in
  let inner_sha1 = hash SHA1 (mm @| ssl_pad1_sha1) in
  let outer_sha1 = hash SHA1 (ms @| ssl_pad2_sha1 @| inner_sha1) in
  outer_md5 @| outer_sha1

let ssl_verifyCertificate hashAlg ms log  =
  let (pad1,pad2) =
      match hashAlg with
      | SHA1 -> (ssl_pad1_sha1, ssl_pad2_sha1)
      | MD5 -> (ssl_pad1_md5,  ssl_pad2_md5)
      | _ -> Platform.Error.unexpected "[ssl_certificate_verify] invoked on a wrong hash algorithm"
  in
  let forStep1 = log @| ms @| pad1 in
  let step1 = hash hashAlg forStep1 in
  let forStep2 = ms @| pad2 @| step1 in
  hash hashAlg forStep2

(* TLS 1.0 and 1.1 *)

let rec p_hash_int alg secret seed len it aPrev acc =
  let aCur = tls_mac alg secret aPrev in
  let pCur = tls_mac alg secret (aCur @| seed) in
  if it = 1 then
    let hs = macSize alg in
    let r = len % hs in
    let (pCur,_) = split pCur r in
    acc @| pCur
  else
    p_hash_int alg secret seed len (it-1) aCur (acc @| pCur)

let p_hash alg secret seed len =
  let hs = macSize alg in
  let it = (len/hs)+1 in
  p_hash_int alg secret seed len it seed empty_bytes

let tls_prf secret label seed len =
  let l_s = length secret in
  let l_s1 = (l_s+1)/2 in
  let secret1,secret2 = split secret l_s1 in
  let newseed = label @| seed in
  let hmd5  = p_hash (HMAC(MD5)) secret1 newseed len in
  let hsha1 = p_hash (HMAC(SHA1)) secret2 newseed len in
  xor len hmd5 hsha1 

let tls_finished_label : role -> bytes =
  let tls_client_label = utf8 "client finished" in
  let tls_server_label = utf8 "server finished" in
  function
  | Client -> tls_client_label
  | Server -> tls_server_label

let tls_verifyData ms role data =
  let md5hash  = hash MD5 data in
  let sha1hash = hash SHA1 data in
  tls_prf ms (tls_finished_label role) (md5hash @| sha1hash) 12

(* TLS 1.2 *)

let tls12prf cs ms label data len =
  let prfMacAlg = prfMacAlg_of_ciphersuite cs in
  p_hash prfMacAlg ms (label @| data) len

let tls12prf' macAlg ms label data len =
  p_hash macAlg ms (label @| data) len

let tls12VerifyData cs ms role data =
  let verifyDataHashAlg = verifyDataHashAlg_of_ciphersuite cs in
  let verifyDataLen = verifyDataLen_of_ciphersuite cs in
  let hashed = hash verifyDataHashAlg data in
  tls12prf cs ms (tls_finished_label role) hashed verifyDataLen

(* Internal agile implementation of PRF *)

let verifyData (pv,cs) (secret:bytes) (role:role) (data:bytes) =
  match pv with
    | SSL_3p0           -> ssl_verifyData     secret role data
    | TLS_1p0 | TLS_1p1 -> tls_verifyData     secret role data
    | TLS_1p2           -> tls12VerifyData cs secret role data

let prf (pv,cs) secret (label:bytes) data len =
  match pv with
  | SSL_3p0           -> ssl_prf     secret       data len
  | TLS_1p0 | TLS_1p1 -> tls_prf     secret label data len
  | TLS_1p2           -> tls12prf cs secret label data len

let prf' a secret data len =
    match a with
    | PRF_TLS_1p2 label macAlg -> tls12prf' macAlg secret label data len  // typically SHA256 but may depend on CS
    | PRF_TLS_1p01(label)       -> tls_prf          secret label data len  // MD5 xor SHA1
    | PRF_SSL3_nested           -> ssl_prf          secret       data len  // MD5(SHA1(...)) for extraction and keygen
    | _ -> Platform.Error.unexpected "[prf'] unreachable pattern match"

//let extract a secret data len = prf a secret extract_label data len

let extract a secret data len = prf' a secret data len

let kdf     a secret data len = prf' a secret data len
