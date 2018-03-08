(** hash algorithms and providers *)
module Hashing.Spec

open FStar.UInt32
open FStar.Bytes

type lbytes32 n = lbytes (UInt32.v n)

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

type alg13  = a:alg {a=SHA256 \/ a=SHA384 \/ a=SHA512}

let string_of_alg = function
  | MD5    -> "MD5"
  | SHA1   -> "SHA1"
  | SHA224 -> "SHA224"
  | SHA256 -> "SHA256"
  | SHA384 -> "SHA384"
  | SHA512 -> "SHA512"

// length of the input blocks, in bytes (used for specifying the outer hash loop)
let blockLen = function
  | MD5 | SHA1 | SHA224 | SHA256 ->  64ul
  | SHA384 | SHA512              -> 128ul
//| SHAKE128 _ -> 168 | SHAKE256 _ -> 136
let blockLength a = v (blockLen a)

// length of the resulting tag, in bytes
let maxTagLen = 64ul
let tagLen (a:alg) : Tot (n:UInt32.t {n <=^ maxTagLen}) =
  match a with
  | MD5    -> 16ul
  | SHA1   -> 20ul
  | SHA224 -> 28ul // truncated SHA256
  | SHA256 -> 32ul
  | SHA384 -> 48ul // truncated SHA512
  | SHA512 -> 64ul
let tagLength a = v (tagLen a)
//  | SHAKE128 d -> d
//  | SHAKE256 d -> d
type tag (a:alg) = lbytes32 (tagLen a)
type anyTag = lbytes32 maxTagLen
let lemma_maxLen (a:alg): Lemma (tagLen a <=^ maxTagLen) = ()

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

// A "placeholder" hash whose bytes are all 0, used for key-derivation in Handshake.Secret
let zeroHash (a:alg): Tot (tag a) = Bytes.create (tagLen a) 0uy


// internal hash state for incremental computation
// with initial value and core algorithm, accumulating an extra block into the current state

// cwinter: keeping implementation so as not to break extraction.
// assume type acc (a:alg)
// assume val acc0: a:alg -> Tot (acc a)
// assume val compress: #a:alg -> acc a -> lbytes32 (blockLen a) -> Tot (acc a)
// assume val truncate: #a:alg -> acc a -> Tot (tag a) // just keeping the first tagLen bytes

//18-02-26 TODO reconcile with fake abstract implementation in quic2c, which was:

//NS, JR: A very dubious change here, replacing an assumed type and functions on it
//        Otherwise, this doesn't compile at all

abstract
let acc (a:alg) = bytes

abstract
let acc0 (a:alg) : acc a = empty_bytes

abstract
let compress (#a:alg) (_:acc a) (l:lbytes32 (blockLen a)) = l //??

module U32 = FStar.UInt32 

module U32 = FStar.UInt32 

abstract
let truncate (#a:alg) (ac:acc a): Tot (lbytes32 (tagLen a)) =
  let l = tagLen a in
  assume (U32.(Bytes.len ac <=^ tagLen a));
  assume (U32.(l <=^ Bytes.len ac));
  let r = Bytes.slice ac 0ul l in
  assume (U32.(len r =^ l));
  r //?? just keeping the first tagLen bytes

(*
let acc0 = function
  | MD5 ->  [0x67452301; 0xefcdab89; 0x98badcfe; 0x10325476] // A, B, C, D
  | SHA1 -> [0x67452301; 0xefcdab89; 0x98badcfe; 0x10325476; 0xc3d2e1f0] // h0--h4
  | SHA224 -> [0xc1059ed8; 0x367cd507; 0x3070dd17; 0xf70e5939; 0xffc00b31; 0x68581511; 0x64f98fa7; 0xbefa4fa4] // second 32 bits of the fractional parts of the square roots of the 9th through 16th primes 23..53
  | SHA256 -> [0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19] // first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19
  | SHA384 -> [0xcbbb9d5dc1059ed8; 0x629a292a367cd507; 0x9159015a3070dd17; 0x152fecd8f70e5939; 0x67332667ffc00b31; 0x8eb44a8768581511; 0xdb0c2e0d64f98fa7; 0x47b5481dbefa4fa4]
  | SHA512 -> [0x6a09e667f3bcc908; 0xbb67ae8584caa73b; 0x3c6ef372fe94f82b; 0xa54ff53a5f1d36f1; 0x510e527fade682d1; 0x9b05688c2b3e6c1f; 0x1f83d9abfb41bd6b; 0x5be0cd19137e2179]
*)

val hash2: #a:alg -> acc a -> b:bytes {length b % blockLength a = 0} -> Tot (acc a) (decreases (length b))
let rec hash2 #a v b =
  if len b = 0ul then v
  else
    let bl = blockLen a in
    assume (U32.(0ul <=^ bl && bl <^ len b));
    let c,b = split b bl in
    hash2 (compress v c) b

(** maximal input lengths for hashing and hmac, overly limited by our UInt32 of bytes lengths *)
let maxLength a: nat = pow2 32 - blockLength a - 9
let hashable a = b: bytes {length b <= maxLength a}
let macable a = b: bytes {length b + blockLength a <= maxLength a}

// for convenience, we treat inputs as sequences of bytes, not bits.
// but note what's encoded in the suffix is the length in bits.
private 
let suffixLength (a:alg) (len:UInt32.t {v len <= maxLength a}): n:nat {(n + v len) % blockLength a = 0 /\ n <= blockLength a + 9} =
  let blocklen = v (blockLen a) in 
  let lenlen = match a with | SHA384 | SHA512 -> 8 | _ -> 4 in
  let required = v len + 1 + lenlen in // minimal length after padding and encoding the length
  let zeros = // minimal extra padding for block alignment
    if required % blocklen = 0 
    then 0
    else blocklen - (required % blocklen) in
    //was, harder to prove: required + blockLen a - ((required - 1) % blockLen a + 1) in
  1 + zeros + lenlen

// injective encoding for variable-length inputs
// we add either 8 or 16 bytes of length and 1+ bytes of padding
private 
assume val suffix: a:alg -> len:UInt32.t {v len <= maxLength a} -> Tot (lbytes (suffixLength a len))

// 18-02-26 on quic2c, was:
// let suffix (a:alg) (len:nat): Tot (c:lbytes (suffixLen a len)) =
//   //TODO: Placeholder!
//   Bytes.create (FStar.UInt32.uint_to_t (suffixLen a len)) 0uy

// computed in one step (specification)
val hash: a:alg -> b:hashable a -> Tot (lbytes32 (tagLen a))
let hash a b =
  let q = suffix a (len b) in
  assume (FStar.UInt.fits (length b + length q) 32);
  let padded = b @| q in
  let v = hash2 (acc0 a) padded in
  let r = truncate v in
  assert (U32.(len r <=^ tagLen a));
  r

// HMAC specification
// in contrast with RFC 2104 (which take any key length),
// in TLS, the HMAC key has the same length as the hash [TLS1.3, 4.4.3]
type hkey (a:alg) = tag a

val hmac: a:alg -> k:hkey a -> text:macable a -> Tot (tag a)
let hmac a key message =
  let xkey = key @| create U32.(blockLen a -^ tagLen a) 0x0z  in
  let outer_key_pad = xor (blockLen a) xkey (create (blockLen a) 0x5cz) in
  let inner_key_pad = xor (blockLen a) xkey (create (blockLen a) 0x36z) in
  assume (FStar.UInt.fits (length inner_key_pad + length message) 32);
  hash a (outer_key_pad @| hash a (inner_key_pad @| message))
