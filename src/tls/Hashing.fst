(** hash algorithms and providers *)
module Hashing

// this file to be split into several once it moves to HACL*

//________________ Hash.Spec __________________

open Platform.Bytes

type alg = // CoreCrypto.hash_alg
  | MD5
  | SHA1
  | SHA224
  | SHA256
  | SHA384
  | SHA512

// see e.g. https://en.wikipedia.org/wiki/SHA-1 for a global comparison

// length of the input blocks, in bytes (used for specifying the outer hash loop)
let blockLen = function 
  | MD5 | SHA1 | SHA224 | SHA256 -> 64 
  | SHA384 | SHA512 -> 128

// length of the resulting tag, in bytes (replicating CoreCrypto.hashSize)
let tagLen = function 
  | MD5      -> 16
  | SHA1     -> 20
  | SHA224 -> 28 // truncated SHA256
  | SHA256 -> 32
  | SHA384 -> 48 // truncated SHA512
  | SHA512 -> 64 

// internal hash state for incremental computation
assume type acc (a:alg)
assume val acc0: a:alg -> Tot (acc a)
(*
let acc0 = function 
  | MD5 ->  [0x67452301; 0xefcdab89; 0x98badcfe; 0x10325476] // A, B, C, D
  | SHA1 -> [0x67452301; 0xefcdab89; 0x98badcfe; 0x10325476; 0xc3d2e1f0] // h0--h4 
  | SHA224 -> [0xc1059ed8; 0x367cd507; 0x3070dd17; 0xf70e5939; 0xffc00b31; 0x68581511; 0x64f98fa7; 0xbefa4fa4] // second 32 bits of the fractional parts of the square roots of the 9th through 16th primes 23..53
  | SHA256 -> [0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19] // first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19
  | SHA384 -> [0xcbbb9d5dc1059ed8; 0x629a292a367cd507; 0x9159015a3070dd17; 0x152fecd8f70e5939; 0x67332667ffc00b31; 0x8eb44a8768581511; 0xdb0c2e0d64f98fa7; 0x47b5481dbefa4fa4]
  | SHA512 -> [0x6a09e667f3bcc908; 0xbb67ae8584caa73b; 0x3c6ef372fe94f82b; 0xa54ff53a5f1d36f1; 0x510e527fade682d1; 0x9b05688c2b3e6c1f; 0x1f83d9abfb41bd6b; 0x5be0cd19137e2179]
*)

// core algorithm, accumulating an extra block into the current state
assume val compress: #a:alg -> acc a -> lbytes (blockLen a) -> Tot (acc a)

val hash2: #a:alg -> acc a -> b:bytes { length b % blockLen a = 0 } -> Tot (acc a) (decreases (length b))
let rec hash2 #a v b = 
  if length b = 0 then v 
  else 
    let c,b = split b (blockLen a) in 
    hash2 (compress v c) b 

assume val truncate: #a:alg -> acc a -> Tot (lbytes (tagLen a))

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

// an "outer" state for specifying incremental evaluation 
// (we may additionally record the input bytestring)
noeq type accv (a:alg) = | Acc: len:nat -> v:acc a -> b:lbytes (len % blockLen a) -> accv a 

// incremental computation (specification) 
val hashA: a:alg -> bytes -> Tot (accv a)
let hashA a b = 
  let pending = length b % blockLen a in 
  let hashed, rest = split b (length b - pending) in
  Acc (length b) (hash2 (acc0 a) hashed) rest

let start a = hashA a empty_bytes // i.e. block0

// this interface requires that the caller knows what he is hashing, to keep track of computed collisions
val extend: 
  #a:alg ->
  content:bytes (* TODO: ghost in real mode *) -> 
  v:accv a {v == hashA a content } ->
  b:bytes ->
  Tot (v:accv a {v == hashA a (content @| b) })

private assume val split_append: xs:bytes -> ys:bytes -> i:nat { i <= Seq.length xs } -> 
  Lemma(
    let c,b = split xs i in (split (xs@|ys) i == (c, (b@|ys))))
  
private val hash2_append:
  #a:alg ->
  v:acc a  -> 
  b0:bytes { length b0 % blockLen a = 0 } -> 
  b1:bytes { length b1 % blockLen a = 0 } -> 
  Lemma (ensures hash2 v (b0 @| b1) == hash2 (hash2 v b0) b1) (decreases (length b0))
let rec hash2_append #a v b0 b1 = 
  if length b0 = 0 then (
    assert(Seq.equal b0 empty_bytes);
    assert(Seq.equal (b0 @| b1) b1);
    assert_norm(hash2 v empty_bytes == v))
  else 
    let c,b = split b0 (blockLen a) in
    split_append b0 b1 (blockLen a); 
    hash2_append (compress v c) b b1
  
#set-options "--z3rlimit 200"
let extend #a content v b = 
  let z = v.b @| b in 
  let pending = length z % blockLen a in
  let hashed, rest = split z (length z - pending) in
  // proof only: unfolding a == hashA content
  assert(Seq.equal z (hashed @| rest)); 
  let b0, c0 = split content (length content - (length content % blockLen a)) in 
  assert(Seq.equal content (b0 @| v.b));
  assert(v.len = length content);
  assert(v.v == hash2 (acc0 a) b0);
  hash2_append (acc0 a) b0 hashed; 
  let content' = content @| b in  // unfolding hashA (content @| b) 
  let b0', c0' = split content' (length content' - (length content' % blockLen a)) in 
  assert(Seq.equal rest c0');
  assert(Seq.equal content' (b0' @| rest));
  assert(Seq.equal b0' (b0 @| hashed));
  assert(pending = length content' % blockLen a);
  assert(v.len + length b = length (content @| b));
  assert(hash2 v.v hashed == hash2 (acc0 a) (b0 @| hashed));
  Acc (v.len + length b) (hash2 v.v hashed) rest

val finalize: 
  #a:alg -> 
  content:bytes (* TODO: ghost in real mode *) ->
  v:accv a { v == hashA a content } -> 
  Tot (t:lbytes (tagLen a) {t = hash a content})
  
let finalize #a content v = 
  let b0, rest = split content (length content - length content % blockLen a) in 
  assert(Seq.equal content (b0 @| rest));
  let b1 = v.b @| suffix a v.len in 
  let b = content @| suffix a v.len in 
  assert(Seq.equal b (b0 @| b1)); 
  hash2_append (acc0 a) b0 b1; 
  truncate (hash2 v.v b1)




(*
//________________ Hash.OpenSSL.fsti (lax-coded in ML and C) __________________
// towards a shared API for hashes; the code above provides a reference implenentation.

assume type hash_ctx (a:alg) (r:rgn): Type0 
assume val accT: #a:alg -> #r:rgn -> hash_ctx a r -> mem -> GTot (accv a)  // getting the spec out
assume val accInv: #a:alg -> #r:region -> v:hash_ctx a r -> h0:mem -> h1:mem ->
  Lemma(h0 `on` r == h1 `on` r  ==> accT v h0 == accvT v h1)

assume val digest_create: a:alg -> parent:rgn -> ST (r:rgn & hash_ctx a r)
  (requires (fun h -> True))
  (ensures (fun h0 (r,v) h1 -> 
    modifies Set.empty h0 h1 /\
    extends r parent /\
    stronger_fresh_region r h0 h1 /\
    accT v h1 == start a ))
    
assume val digest_update: #a:alg -> #r:rgn -> v:hash_ctx a r -> b:bytes -> ST unit 
  (requires (fun h -> True))
  (ensures (fun h0 () h1 ->
    modifies_one r h0 h1 /\
    accT v h1 == extend (accT v h0) b))

assume val digest_final: #a:alg -> #r:rgn -> v:hash_ctx a r -> b:bytes -> ST (lbytes (tagLen a)) 
  (requires (fun h -> True))
  (ensures (fun h0 t h1 -> 
    modifies_one r h0 h1 /\
    t = finalize (accT v h0))) // not specifying the post accT makes v non-reusable
*)


(* TBC 
//________________ Hash.Spec.CRF __________________

// witnessing that we hashed this particular content (for collision detection)
// to be replaced by a witness of inclusion in a global table of all hash computations.
// (not sure how to manage that table)
assume val hashed: bytes -> Type 

// Hash.table: strong invariants: hash is injective on its contents.
// witnessed(fun h -> sel h Hash.table `contains` b)

// We keep a copy of the whole input bytestring to be recorded at the end of the hash.
// This is a first "instrumentation" step in the crypto proof.

val finalizeCR: 
  #a:alg -> 
  content:bytes (* TODO: ghost in real mode *) ->
  v:accv { v == hashA a content } -> 
  ST (lbytes (tagLen a))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> 
    t = hash content /\ 
    hashed content /\
    h0 == h1 
    // TBC, e.g. 
    // modifies_one h0 h1 hashTable /\ sel h1 hashTable == snoc (sel h0 hashTable) (content, t)
  ))

val stop: s:string -> ST 'a 
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> False))
let rec stop (s:string) = stop s 

let finalizeCR #a content v = 
  let h = finalize content v in 
  // do we have a collision?
  let log = !hashTable in 
  if Seq.forall (fun c -> h = hash a c => c = content)  log
  then (hashTable := Seq.snoc log content; h) 
  else stop "hash collision detected" 


(*
val collision_resistant: c0: bytes -> c1: bytes { hashed c0 /\ hashed c1 } -> ST unit 
  (requires (fun h0 -> True))
  (ensures (hash c0 = hash c1 ==> c0 = c1))
let collision_resistant c0 c1 =
  testify(hashed c0);
  testify(hashed c1);
  let current = !Hash.table in 
  ()
*)

*)



(*
(* Parametric hash algorithm (implements interface) *)
val hash': hashAlg -> bytes -> Tot bytes
let hash' alg data: bytes =
    match alg with
    | NULL    -> data
    | MD5SHA1 -> (CoreCrypto.hash MD5 data) @| (CoreCrypto.hash SHA1 data)
    | Hash h  -> (CoreCrypto.hash h  data)

val hash: hashAlg -> bytes -> Tot bytes
let hash alg data: bytes =
  let h = hash' alg data in
  let l = length h in
    h
(*
  let exp = hashSize alg in
  if l = exp then h
  else Platform.Error.unexpected "CoreCrypto.Hash returned a hash of an unexpected size"
*)
*)
