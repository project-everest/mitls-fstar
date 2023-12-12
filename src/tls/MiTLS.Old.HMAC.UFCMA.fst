(**
Idealizing HMAC for Finished message payloads and binders.
*)
module MiTLS.Old.HMAC.UFCMA
open MiTLS

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Seq
open FStar.Bytes
open FStar.Error

open MiTLS.Mem
open MiTLS.TLSError
// open TLSInfo

module HS = FStar.HyperStack

// idealizing HMAC
// for concreteness; the rest of the module is parametric in a:alg

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

type entry (i:id) (good: bytes -> Type0) : Type0 =
  | Entry: t:tag i -> p:bytes { authId i ==> good p } -> entry i good

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 30"
let gen i good parent =
  gen0 i good parent (Random.sample32 (keysize i))

let coerce i good parent kv = gen0 i good parent kv

let leak   #i #good k = k.kv

let mac #i #good k p =
  let a = alg i in 
  assume (length p + Hashing.Spec.block_length a < pow2 32);
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  assert_norm(Spec.Agile.HMAC.keysized a (Spec.Hash.Definitions.hash_length a));
  let p : p:bytes { authId i ==> good p } = p in
  let t = HMAC.hmac a k.kv p in
  let e : entry i good = Entry t p in
  recall k.log;
  k.log := snoc !k.log e;
  t

let matches #i #good p (Entry _ p') = p = p'
