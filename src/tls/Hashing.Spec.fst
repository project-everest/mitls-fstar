(** hash algorithms and providers

 * provides bytes-friendly API before idealization
 * no dependency on TLS: could go to EverCrypt or SecureAPI.

*)
module Hashing.Spec

include EverCrypt.Hash 

open FStar.Integers
open FStar.Bytes 
type tag (a:alg) = Bytes.lbytes32 (tagLen a)
type anyTag = lbytes (Integers.v maxTagLen)

let macable a = b:bytes {length b + blockLength a < pow2 32}
// 32-bit implementation restriction 

// HMAC specification
// in contrast with RFC 2104 (which take any key length),
// in TLS, the HMAC key has the same length as the hash [TLS1.3, 4.4.3]

type hkey (a:alg) = b:bytes{
  length b > 0 /\ // FIXME(adl) this should be in keysized
  EverCrypt.HMAC.keysized a (length b)}

val hmac: 
  a:alg -> 
  k:hkey a -> 
  text:macable a -> 
  GTot (t:tag a{
    let text = Bytes.reveal text in 
    Seq.length text + blockLength a <= maxLength a /\
    Bytes.reveal t = EverCrypt.HMAC.hmac a (Bytes.reveal k) text})

let hmac a k text = 
  let k = Bytes.reveal k in 
  let text = Bytes.reveal text in 
  assert_norm (Seq.length text + blockLength a <= maxLength a);
  let t: EverCrypt.Hash.tag a = EverCrypt.HMAC.hmac a k text in
  Bytes.hide t

//18-08-31 review
// The hash of the empty string, used in KS
#set-options "--admit_smt_queries true" //17-05-08 TODO size of bytes constants.
let emptyHash : a:alg -> Tot (tag a) =
  function
  | MD5 -> bytes_of_hex "d41d8cd98f00b204e9800998ecf8427e"
  | SHA1 -> bytes_of_hex "da39a3ee5e6b4b0d3255bfef95601890afd80709"
  | SHA224 -> bytes_of_hex "2bc9476102bb288234c415a2b01f828ea62ac5b3e42f"
  | SHA256 -> bytes_of_hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  | SHA384 -> bytes_of_hex "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"
  | SHA512 -> bytes_of_hex "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
#reset-options

// A "placeholder" hash whose bytes are all 0, used for key-derivation in Handshake.Secret
let zeroHash (a:alg): Tot (tag a) = Bytes.create (tagLen a) 0uy


// TLS-specific hash and MAC algorithms (review) 
type tls_alg = 
  | NULL
  | MD5SHA1
  | Hash of alg

val tls_tagLen: h:tls_alg{h<>NULL} -> Tot UInt32.t
let tls_tagLen = function
  | Hash a  -> tagLen a
  | MD5SHA1 -> tagLen MD5 + tagLen SHA1

type tls_macAlg = EverCrypt.HMAC.ha

(* for reference, a bytes spec of HMAC:
let hmac a key message = EverCrypt.Hash. 
  let xkey = key @| create U32.(blockLen a -^ tagLen a) 0x0z  in
  let outer_key_pad = xor (blockLen a) xkey (create (blockLen a) 0x5cz) in
  let inner_key_pad = xor (blockLen a) xkey (create (blockLen a) 0x36z) in
  assume (FStar.UInt.fits (length inner_key_pad + length message) 32);
  hash a (outer_key_pad @| hash a (inner_key_pad @| message))
*)
