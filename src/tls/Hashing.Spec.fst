(** hash algorithms and providers *)
module Hashing.Spec

open Platform.Bytes

type alg = // CoreCrypto.hash_alg
  | MD5
  | SHA1
  | SHA224
  | SHA256
  | SHA384
  | SHA512
//  | SHAKE128 of (n:nat{n >= 8})
//  | SHAKE256 of (n:nat{n >= 16})
// see e.g. https://en.wikipedia.org/wiki/SHA-1 for a global comparison and lengths

let string_of_alg = function
  | MD5 -> "MD5"
  | SHA1 -> "SHA1"
  | SHA224 -> "SHA224"
  | SHA256 -> "SHA256"
  | SHA384 -> "SHA384"
  | SHA512 -> "SHA512"

// length of the input blocks, in bytes (used for specifying the outer hash loop)
let blockLen = function
  | MD5 | SHA1 | SHA224 | SHA256 -> 64
  | SHA384 | SHA512 -> 128
//  | SHAKE128 _ -> 168 | SHAKE256 _ -> 136

// length of the resulting tag, in bytes (replicating CoreCrypto.hashSize)
let tagLen (a:alg) : Tot (n:nat{n <= 64}) =
  match a with
  | MD5    -> 16
  | SHA1   -> 20
  | SHA224 -> 28 // truncated SHA256
  | SHA256 -> 32
  | SHA384 -> 48 // truncated SHA512
  | SHA512 -> 64
//  | SHAKE128 d -> d
//  | SHAKE256 d -> d
type tag (a:alg) = lbytes (tagLen a)

// The hash of the empty string, used in KS
#set-options "--lax" //17-05-08 TODO size of bytes constants.
let emptyHash : a:alg -> Tot (tag a) =
  function
  | MD5 -> bytes_of_hex "d41d8cd98f00b204e9800998ecf8427e"
  | SHA1 -> bytes_of_hex "da39a3ee5e6b4b0d3255bfef95601890afd80709"
  | SHA224 -> bytes_of_hex "2bc9476102bb288234c415a2b01f828ea62ac5b3e42f"
  | SHA256 -> bytes_of_hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  | SHA384 -> bytes_of_hex "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b"
  | SHA512 -> bytes_of_hex "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
#reset-options

// A "placeholder" hash whose bytes are all 0 (used in KS)
let zeroHash (a:alg) : Tot (tag a) =
  createBytes (tagLen a) 0uy

let maxTagLen = 64
type anyTag = lbytes maxTagLen
let lemma_maxLen (a:alg): Lemma (tagLen a <= maxTagLen) = ()

// internal hash state for incremental computation
// with initial value and core algorithm, accumulating an extra block into the current state

assume type acc (a:alg)
assume val acc0: a:alg -> Tot (acc a)
assume val compress: #a:alg -> acc a -> lbytes (blockLen a) -> Tot (acc a)
assume val truncate: #a:alg -> acc a -> Tot (tag a) // just keeping the first tagLen bytes
(*
let acc0 = function
  | MD5 ->  [0x67452301; 0xefcdab89; 0x98badcfe; 0x10325476] // A, B, C, D
  | SHA1 -> [0x67452301; 0xefcdab89; 0x98badcfe; 0x10325476; 0xc3d2e1f0] // h0--h4
  | SHA224 -> [0xc1059ed8; 0x367cd507; 0x3070dd17; 0xf70e5939; 0xffc00b31; 0x68581511; 0x64f98fa7; 0xbefa4fa4] // second 32 bits of the fractional parts of the square roots of the 9th through 16th primes 23..53
  | SHA256 -> [0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19] // first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19
  | SHA384 -> [0xcbbb9d5dc1059ed8; 0x629a292a367cd507; 0x9159015a3070dd17; 0x152fecd8f70e5939; 0x67332667ffc00b31; 0x8eb44a8768581511; 0xdb0c2e0d64f98fa7; 0x47b5481dbefa4fa4]
  | SHA512 -> [0x6a09e667f3bcc908; 0xbb67ae8584caa73b; 0x3c6ef372fe94f82b; 0xa54ff53a5f1d36f1; 0x510e527fade682d1; 0x9b05688c2b3e6c1f; 0x1f83d9abfb41bd6b; 0x5be0cd19137e2179]
*)

val hash2: #a:alg -> acc a -> b:bytes { length b % blockLen a = 0 } -> Tot (acc a) (decreases (length b))
let rec hash2 #a v b =
  if length b = 0 then v
  else
    let c,b = split b (blockLen a) in
    hash2 (compress v c) b

// for convenience, we treat inputs as sequences of bytes, not bits.
// but note what's encoded in the suffix is the length in bits.

let suffixLen (a:alg) (len:nat) : n:nat {(n + len) % blockLen a = 0} =
  let lenlen = match a with | SHA384 | SHA512 -> 8 | _ -> 4 in
  let required = len + 1 + lenlen in // minimal length after padding and encoding the length
  let zeros = // minimal extra padding for block alignment
    if required % blockLen a = 0 then 0 else blockLen a - (required % blockLen a) in
    //was, harder to prove: required + blockLen a - ((required - 1) % blockLen a + 1) in
  1 + zeros + lenlen

// injective encoding for variable-length inputs
// we add either 8 or 16 bytes of length and 1+ bytes of padding
assume val suffix: a:alg -> len:nat -> Tot (c:lbytes (suffixLen a len))

// computed in one step (specification)
val hash: a:alg -> bytes -> Tot (lbytes (tagLen a))
let hash a b =
  let padded = b @| suffix a (length b) in
  let v = hash2 (acc0 a) padded in
  truncate v


// HMAC specification
// in contrast with RFC 2104 (which take any key length),
// in TLS, the HMAC key has the same length as the hash [TLS1.3, 4.4.3]
type hkey (a:alg) = tag a

val hmac: a:alg -> k:hkey a -> message:bytes -> Tot (tag a)

private let xor #l a b = xor l a b

let hmac a key message =
  let xkey = key @| createBytes (blockLen a - tagLen a) 0x0z  in
  let outer_key_pad = xor xkey (createBytes (blockLen a) 0x5cz) in
  let inner_key_pad = xor xkey (createBytes (blockLen a) 0x36z) in
  hash a (outer_key_pad @| hash a (inner_key_pad @| message))
