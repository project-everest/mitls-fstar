(**
Idealizing HMAC for Finished message payloads and binders.
*)
module Old.HMAC.UFCMA

open FStar.Heap
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Seq
open FStar.Bytes

open Mem
open TLS.Result
// open TLSInfo

module M = LowStar.Modifies
module HS = FStar.HyperStack

// idealizing HMAC
// for concreteness; the rest of the module is parametric in a:alg

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

type entry (i:id) (good: bytes -> Type) =
  | Entry: t:tag i -> p:bytes { authId i ==> good p } -> entry i good

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 30"
// todo: mark it as private
private let gen0 i good (parent:rgn) kv : ST (key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    fresh_subregion (region #i #good k) parent h0 h1 /\
    modifies Set.empty h0 h1
  )) =
  let region = new_region parent in
  let log = ralloc region Seq.empty in
  Key #i #good #region kv log

let gen i good parent =
  gen0 i good parent (Random.sample32 (keysize i))

let coerce i good parent kv = gen0 i good parent kv

// We log every authenticated texts, with their index and resulting tag
let mac #i #good k p =
  let a = alg i in 
  assume (length p + Hashing.Spec.block_length a < pow2 32);
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 32 < pow2 125);
  assert_norm(Spec.Agile.HMAC.keysized a (Spec.Hash.Definitions.hash_length a));
  let p : p:bytes { authId i ==> good p } = p in
  let h0 = get () in
  let t = HMAC.hmac a k.kv p in
  let h1 = get () in
  assume(modifies_none h0 h1); // FIXME update memory model in HS
  let e : entry i good = Entry t p in
  recall k.log;
  k.log := snoc !k.log e;
  t

let matches #i #good p (Entry _ p') = p = p'

#set-options "--admit_smt_queries true"

// We use the log to correct any verification errors
let verify #i #good k p t =
  let x = HMAC.hmacVerify (alg i) k.kv p t in
  let log = !k.log in
  x &&
  ( not(authId i) || log_entry_matches_p log p)
