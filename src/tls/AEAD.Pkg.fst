module AEAD.Pkg

// TODO instead: package from a plausible AEAD.fsti, mirroring
// SecureAPI's one with bytes instead of buffers.

// As a second step, we will restore AEADProvider between the two, and
// use it to switch to faster, concrete, correct implementations.

// As a verification unit-test, we may also show how to package two
// instances of AEAD (for both directions) from the same create/coerce
// on their concatenated keys, in tLS 1.2 style.

open Mem
open Pkg

module HH = FStar.HyperHeap // I wish we could avoid it once Mem is open.

/// --------------------------------------------------------------------------------------------------
/// module AEAD
/// sample generic, agile functionality.
///
/// TODO package instead StAE; what to do with the algorithm?

type aeadAlg = | AES_GCM128 | AES_GCM256
let aeadLen: aeadAlg -> keylen = function
  | AES_GCM128 -> 32ul
  | AES_GCM256 -> 48ul

// 17-10-31  this abbreviation breaks typechecking when used; why?
// unfold type aeadAlgi (#ip:ipkg aeadAlg) (i:ip.t) = a:aeadAlg {a == ip.get_info i}

assume val flag_AEAD: b:bool{b ==> model}
type idealAEAD = b2t flag_AEAD

type keyrepr a = lbytes (aeadLen a)
assume new type key (ip: ipkg) (aeadAlg_of_i: ip.t -> aeadAlg) (i:ip.t{ip.registered i}) // abstraction required for indexing

let prf_region: subrgn tls_tables_region = new_region tls_tables_region

let aead_shared_footprint (#ip:ipkg) (#aeadAlg_of_i: ip.t -> aeadAlg) : rset =
  assume false; // Downward closed
  Set.singleton prf_region

assume val aead_footprint:
  #ip:ipkg -> #aeadAlg_of_i: (ip.t -> aeadAlg) -> #i:ip.t{ip.registered i} ->
  k:key ip aeadAlg_of_i i -> GTot (s:rset{s `Set.disjoint` aead_shared_footprint #ip #aeadAlg_of_i})

// The local AEAD invariant
assume val aead_inv:
  #ip:ipkg -> #aeadAlg_of_i: (ip.t -> aeadAlg) -> #i:ip.t{ip.registered i} ->
  k:key ip aeadAlg_of_i i -> h:mem -> GTot Type0

assume val aead_invariant_framing: ip:ipkg -> aeadAlg_of_i: (ip.t -> aeadAlg) ->
  i:ip.t{ip.registered i} -> k:key ip aeadAlg_of_i i ->
  h0:mem -> r:HH.rid -> h1:mem ->
  Lemma (requires aead_inv k h0 /\ modifies_one r h0 h1
          /\ ~(r `Set.mem` aead_footprint k) /\ ~(r `Set.mem` aead_shared_footprint #ip #aeadAlg_of_i))
        (ensures aead_inv k h1)

assume val aead_empty_log: ip: ipkg -> aeadAlg_of_i: (ip.t -> aeadAlg) ->
  #i: ip.t{ip.registered i} -> a: aeadAlg {a == aeadAlg_of_i i} ->
  k:key ip aeadAlg_of_i i -> h1:mem -> Type0

assume val aead_empty_log_framing: ip: ipkg -> aeadAlg_of_i: (ip.t -> aeadAlg) ->
  #i: ip.t{ip.registered i} -> a: aeadAlg {a == aeadAlg_of_i i} ->
  k:key ip aeadAlg_of_i i -> h0:mem -> r:HH.rid -> h1:mem -> Lemma
    (requires (aead_empty_log ip aeadAlg_of_i a k h0 /\ modifies_one r h0 h1 /\ ~(r `Set.mem` aead_footprint k)))
    (ensures (aead_empty_log ip aeadAlg_of_i a k h1))

assume val create_key: ip: ipkg -> aeadAlg_of_i: (ip.t -> aeadAlg) ->
  i: ip.t{ip.registered i} -> a:aeadAlg {a == aeadAlg_of_i i} ->
  ST (key ip aeadAlg_of_i i)
    (requires fun h0 -> model)
    (ensures fun h0 k h1 -> modifies_none h0 h1 /\ fresh_regions (aead_footprint k) h0 h1
      /\ aead_empty_log ip aeadAlg_of_i a k h1 /\ aead_inv k h1)

assume val coerceT_key: ip: ipkg -> aeadAlg_of_i: (ip.t -> aeadAlg) ->
  i: ip.t{ip.registered i /\ (idealAEAD ==> ~(ip.honest i))} ->
  a:aeadAlg {a == aeadAlg_of_i i} -> keyrepr a ->
  GTot (key ip aeadAlg_of_i i)

assume val coerce_key: ip: ipkg -> aeadAlg_of_i: (ip.t -> aeadAlg) ->
  i: ip.t{ip.registered i /\ (idealAEAD ==> ~(ip.honest i))} ->
  a:aeadAlg {a == aeadAlg_of_i i} -> k0:keyrepr a ->
  ST (key ip aeadAlg_of_i i)
    (requires fun h0 -> True)
    (ensures fun h0 k h1 -> k == coerceT_key ip aeadAlg_of_i i a k0
      /\ modifies_none h0 h1 /\ fresh_regions (aead_footprint k) h0 h1
      /\ aead_empty_log ip aeadAlg_of_i a k h1 /\ aead_inv k h1)

let local_ae_pkg (ip:ipkg) (aeadAlg_of_i: ip.t -> aeadAlg) =
  LocalPkg
    (key ip aeadAlg_of_i)
    (fun (i:ip.t) -> a:aeadAlg{a = aeadAlg_of_i i})
    (fun #_ a -> aeadLen a)
    idealAEAD
    (aead_shared_footprint #ip #aeadAlg_of_i)
    (aead_footprint #ip #aeadAlg_of_i)
    (aead_inv #ip #aeadAlg_of_i)
    (aead_invariant_framing ip aeadAlg_of_i)
    (aead_empty_log ip aeadAlg_of_i)
    (aead_empty_log_framing ip aeadAlg_of_i)
    (create_key ip aeadAlg_of_i)
    (coerceT_key ip aeadAlg_of_i)
    (coerce_key ip aeadAlg_of_i)

let mp (ip:ipkg) (aeadAlg_of_i: ip.t -> aeadAlg): ST (pkg ip)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 ->
    //17-12-01 we need freshness and emptyness of the new table + local packaging
    modifies_mem_table p.define_table h0 h1 /\
    p.package_invariant h1)
=
  memoization_ST #ip (local_ae_pkg ip aeadAlg_of_i)

val encrypt:
  ip:ipkg -> aeadAlg_of_i: (ip.t -> aeadAlg) -> #i:ip.t{ip.registered i} ->
  k: key ip aeadAlg_of_i i -> nat -> ST nat
  (requires fun h0 -> aead_inv k h0)
  (ensures fun h0 c h1 ->
    modifies (rset_union (aead_footprint k) (aead_shared_footprint #ip #aeadAlg_of_i)) h0 h1
    /\ aead_inv k h1)

let encrypt _ _ #_ k v = v + 1
