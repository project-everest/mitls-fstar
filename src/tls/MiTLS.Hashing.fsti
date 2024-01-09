(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module MiTLS.Hashing
open MiTLS

open MiTLS.Declassify
open MiTLS.Mem

include MiTLS.Hashing.Spec

open FStar.HyperStack.ST
open FStar.Bytes
open FStar.Integers

module ST = FStar.HyperStack.ST

module B = LowStar.Buffer

// defining those on FStar.Bytes, not on EverCrypt's seq Uin8.t
type hashable (a:alg) = b:bytes {length b `less_than_max_input_length` a}
type tag (a:alg) = lbytes32 (Hacl.Hash.Definitions.hash_len a)

// 18-08-31 pure hash specification;
// renamed from [hash] already included from EverCrypt.Hash
let h (a:alg) (b:hashable a): GTot (tag a) =
  let v = Spec.Agile.Hash.hash a (Bytes.reveal b) in
  Bytes.hide v

/// bytes wrapper for [EverCrypt.Hash.hash]
val compute: a:alg -> text:hashable a -> Stack (tag a)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 ->
    let v = reveal text in
    B.modifies B.loc_none h0 h1 /\
    Seq.length v `less_than_max_input_length` a /\
    t = h a text)

(* IMPLEMENTATION PLACEHOLDER,
    simply buffering the bytes underneath *)

// 18-08-29 TODO actually use EverCrypt's incremental API, but this
// requires (1) any-length incremental, and (2) switching all these
// functions from pure to modifiying an abstract footprint...

val accv (a:alg) : Type0

val content: #a:alg -> accv a -> Tot (hashable a)

val start: a:alg -> Tot (v:accv a {content v == empty_bytes})
val extend: #a:alg -> v:accv a -> b:bytes -> Tot (v':accv a {length (content v) + length b = length (content v') /\  content v' == content v @| b})

val finalize: #a:alg -> v:accv a -> ST (t:tag a {t == h a (content v)})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> B.(modifies loc_none h0 h1)))

(* older construction, still used in sig *)
let compute_MD5SHA1 data = compute MD5 data @| compute SHA1 data

(*
// 18-08-29 was in Hashing.OpenSSL
val hmac:
  a:alg ->
  k:tag a ->
  m:bytes {length m + block_length a <= max_input_length a } ->
  Stack (t:tag a {reveal t == Spec.Agile.HMAC.hmac a (reveal k) (reveal m)})
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> modifies Set.empty h0 h1)
*)

(* another PURE, VERIFIED, INCREMENTAL IMPLEMENTATION
    not usable yet, as we don't have a full F* specification
    of the underlying core algorithms, or their OpenSSL code.

// an "outer" state for specifying incremental evaluation
// (we may additionally record the input bytestring)
noeq type accv (a:alg) = | Acc:
    len:nat -> // total input length so far
    v:acc a -> // current internal state
    b:lbytes (len % block_len a) -> // pending bytes to be hashed
    accv a

// the real state for our pure reference implementation
// the ideal state may keep instead the whole input bytestring
// or we could index this type with the whole input bytestring

// incremental computation (specification)
val hashA: a:alg -> bytes -> Tot (accv a)
let hashA a b =
  let pending = length b % block_len a in
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
  b0:bytes { length b0 % block_len a = 0 } ->
  b1:bytes { length b1 % block_len a = 0 } ->
  Lemma (ensures hash2 v (b0 @| b1) == hash2 (hash2 v b0) b1) (decreases (length b0))
let rec hash2_append #a v b0 b1 =
  if length b0 = 0 then (
    assert(Seq.equal b0 empty_bytes);
    assert(Seq.equal (b0 @| b1) b1);
    assert_norm(hash2 v empty_bytes == v))
  else
    let c,b = split b0 (block_len a) in
    split_append b0 b1 (block_len a);
    hash2_append (compress v c) b b1

#set-options "--z3rlimit 200"
let extend #a content v b =
  let z = v.b @| b in
  let pending = length z % block_len a in
  let hashed, rest = split z (length z - pending) in
  // proof only: unfolding a == hashA content
  assert(Seq.equal z (hashed @| rest));
  let b0, c0 = split content (length content - (length content % block_len a)) in
  assert(Seq.equal content (b0 @| v.b));
  assert(v.len = length content);
  assert(v.v == hash2 (acc0 a) b0);
  hash2_append (acc0 a) b0 hashed;
  let content' = content @| b in  // unfolding hashA (content @| b)
  let b0', c0' = split content' (length content' - (length content' % block_len a)) in
  assert(Seq.equal rest c0');
  assert(Seq.equal content' (b0' @| rest));
  assert(Seq.equal b0' (b0 @| hashed));
  assert(pending = length content' % block_len a);
  assert(v.len + length b = length (content @| b));
  assert(hash2 v.v hashed == hash2 (acc0 a) (b0 @| hashed));
  Acc (v.len + length b) (hash2 v.v hashed) rest

val final:
  #a:alg ->
  content:bytes (* TODO: ghost in real mode *) ->
  v:accv a { v == hashA a content } ->
  Tot (t:lbytes (hash_len a) {t = hash a content})

let final #a content v =
  let b0, rest = split content (length content - length content % block_len a) in
  assert(Seq.equal content (b0 @| rest));
  let b1 = v.b @| suffix a v.len in
  let b = content @| suffix a v.len in
  assert(Seq.equal b (b0 @| b1));
  hash2_append (acc0 a) b0 b1;
  truncate (hash2 v.v b1)

