(** hash algorithms and providers

 * provides bytes-friendly API before idealization
 * no dependency on TLS: could go to EverCrypt or SecureAPI.

*)
module Hashing.Spec

include EverCrypt.Hash
include Spec.Hash.Definitions

open FStar.Integers
open FStar.Bytes

open Declassify

let alg = a:alg { is_md a }

let hash_len (a:alg)
  : n:UInt32.t{UInt32.v n == hash_length a}
  =
  match a with
  | MD5 -> assert_norm(hash_length MD5 == 16); 16ul
  | SHA1 -> assert_norm(hash_length SHA1 == 20); 20ul
  | SHA2_224 -> assert_norm(hash_length SHA2_224 == 28); 28ul
  | SHA2_256 -> assert_norm(hash_length SHA2_256 == 32); 32ul
  | SHA2_384 -> assert_norm(hash_length SHA2_384 == 48); 48ul
  | SHA2_512 -> assert_norm(hash_length SHA2_512 == 64); 64ul

type tag (a:alg) = Bytes.lbytes (hash_length a)

let max_hash_length = 64
let max_hash_len = 64ul
type anyTag = lbytes max_hash_length

let max_block_length = 128
let max_block_len = 128ul

private let lemma_tagLen (a:alg)
  : Lemma (hash_length a <= max_hash_length)
  [SMTPat (hash_length a)]
  = ()

private let lemma_blockLength (a:alg)
  : Lemma (block_length a <= max_block_length)
  [SMTPat (block_length a)]
  = ()

let macable a = b:bytes {length b + block_length a < pow2 32}
let macable_any = b:bytes{length b + max_block_length < pow2 32}

// 32-bit implementation restriction

// Adapting EverCrypt's HMAC specification to TLS. In contrast with
// RFC 2104 (which take any key length), in TLS, the HMAC key has the
// same length as the hash [TLS1.3, 4.4.3]

type hkey (a:alg) = b:bytes{
  // 18-09-12 this usage restriction is dubious, but always met in
  // miTLS; it avoids a null-pointer case in the wrapper below.
  length b > 0 /\
  Spec.Agile.HMAC.keysized a (length b)}

val hmac:
  a:alg ->
  k:hkey a ->
  text:macable a ->
  GTot (t:tag a{
    let text = Bytes.reveal text in
    Seq.length text + block_length a <= max_input_length a /\
    Bytes.reveal t = Spec.Agile.HMAC.hmac a (Bytes.reveal k) text})

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
let hmac a k text =
  let k = Bytes.reveal k in
  let text = Bytes.reveal text in
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert (Seq.length text + block_length a <= max_input_length a);
  let t: bytes_hash a = Spec.Agile.HMAC.hmac a k text in
  Bytes.hide t

//18-08-31 review
// The hash of the empty string, used in KS
#set-options "--admit_smt_queries true" //17-05-08 TODO size of bytes constants.
let emptyHash : a:alg -> Tot (tag a) =
  function
  | MD5 -> bytes_of_hex "d41d8cd98f00b204e9800998ecf8427e"
  | SHA1 -> bytes_of_hex "da39a3ee5e6b4b0d3255bfef95601890afd80709"
  | SHA2_224 -> bytes_of_hex "2bc9476102bb288234c415a2b01f828ea62ac5b3e42f"
  | SHA2_256 -> bytes_of_hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  | SHA2_384 -> bytes_of_hex "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"
  | SHA2_512 -> bytes_of_hex "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
#reset-options

// A "placeholder" hash whose bytes are all 0, used for key-derivation in Handshake.Secret
let zeroHash (a:alg): Tot (tag a) = Bytes.create (Hacl.Hash.Definitions.hash_len a) 0uy


// TLS-specific hash and MAC algorithms (review)
type tls_alg =
  | NULL
  | MD5SHA1
  | Hash of alg

val tls_tagLen: h:tls_alg{h<>NULL} -> Tot UInt32.t
let tls_tagLen = function
  | Hash a  -> Hacl.Hash.Definitions.hash_len a
  | MD5SHA1 -> Hacl.Hash.Definitions.hash_len MD5 + Hacl.Hash.Definitions.hash_len SHA1

type tls_macAlg = a:EverCrypt.HMAC.supported_alg{Spec.Hash.Definitions.is_md a}

(* for reference, a bytes spec of HMAC:
let hmac a key message = EverCrypt.Hash.
  let xkey = key @| create U32.(block_len a -^ hash_len a) 0x0z  in
  let outer_key_pad = xor (block_len a) xkey (create (block_len a) 0x5cz) in
  let inner_key_pad = xor (block_len a) xkey (create (block_len a) 0x36z) in
  assume (FStar.UInt.fits (length inner_key_pad + length message) 32);
  hash a (outer_key_pad @| hash a (inner_key_pad @| message))
*)
