(**
  This modules packages AEAD.fsti as a "local package" and provides
  a functor for constructing an AEAD package from an index package

  TODO:
  The next step is to restore AEADProvider using a compile-time flag to multiplex
  between the 3 different providers: Low (verified), LowC (verification lost in translation)
  and OpenSSL. This compile-time flag is such that ~Low ==> ~model
  (we only idealize if the provider is Low).

  TODO:
  As a verification unit-test, we may show how to package two
  instances of AEAD (for both directions) from the same create/coerce
  on their concatenated keys, in TLS 1.2 style.
*)
module AEAD.Pkg

open FStar.Bytes

open Mem
open Pkg

module AE = AEAD
module I  = Crypto.Indexing

/// TODO package instead StAE? what to do with the algorithm?

type aeadAlg =
  | AES_GCM128
  | AES_GCM256

val ideal: b:bool{b ==> model}
let ideal =
  assume (b2t Flags.ideal_AEAD ==> model);
  Flags.ideal_AEAD

type safe (#ip:ipkg) (i:ip.t) = ideal /\ ip.honest i

private val is_safe: #ip:ipkg -> i:ip.t{ip.registered i} -> ST bool
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> modifies_none h0 h1 /\ (b <==> safe i))
let is_safe #ip i =
  let honest = ip.get_honesty i in
  ideal && honest

type info = {
  parent: r:rgn{~(is_tls_rgn r)};
  alg: aeadAlg
}

type info1 (#ip:ipkg) (aeadAlg_of_i:ip.t -> aeadAlg) (i:ip.t) =
  u:info{u.alg == aeadAlg_of_i i}

val keylen: aeadAlg -> keylen
let keylen = function
  | AES_GCM128 -> 32ul
  | AES_GCM256 -> 48ul

type keyrepr (u:info) = lbytes32 (keylen u.alg)

// FIXME(adl) 16/02/18 had to remove abstract to avoid F* crash

noeq abstract type concrete_key =
  | AEAD: u:info -> k:keyrepr u -> concrete_key

noeq abstract type _key (#ip:ipkg) (index_of_i:ip.t -> I.id) (i:ip.t) =
  | Ideal:
    ck: concrete_key ->
//    region: subrgn ck.u.parent{~(is_tls_rgn region)} ->
    state: AE.aead_state (index_of_i i) I.Writer ->
    _key #ip index_of_i i
  | Real:
    ck: concrete_key -> _key #ip index_of_i i

(* abstract *)
type key (ip:ipkg)
  (index_of_i:ip.t -> I.id)
  (i:ip.t{ip.registered i}) =
  (if model then
    k:_key index_of_i i{Ideal? k <==> safe i}
  else
    concrete_key)

abstract
val usage:
  #ip:ipkg ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  k:key ip index_of_i i ->
  GTot info
let usage #ip #index_of_i #i k =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal ck _ -> ck.u
    | Real ck -> ck.u
  else k.u

abstract
val keyval:
  #ip:ipkg ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  k:key ip index_of_i i ->
  GTot (keyrepr (usage k))
let keyval #ip #index_of_i #i k =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal ck _ -> ck.k
    | Real ck -> ck.k
  else k.k

val shared_footprint: rset
let shared_footprint =
  if model then AE.shared_footprint
  else Set.empty

abstract
val footprint:
  #ip:ipkg ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  k:key ip index_of_i i ->
  GTot (s:rset{s `Set.disjoint` shared_footprint})
let footprint #ip #index_of_i #i k =
  Set.lemma_equal_intro (Set.empty `Set.intersect` shared_footprint) Set.empty;
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st -> AE.footprint st
    | Real _ -> Set.empty
  else Set.empty

(** The local AEAD invariant *)
abstract
val invariant:
  #ip:ipkg ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  k:key ip index_of_i i ->
  h:mem ->
  GTot Type0
let invariant #ip #index_of_i #i k h =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st -> AE.invariant st h
    | Real _ -> True
  else True

abstract
val invariant_framing:
  #ip:ipkg ->
  #index_of_i:(ip.t -> I.id) ->
  i:ip.t{ip.registered i} ->
  k:key ip index_of_i i ->
  h0:mem ->
  r:rid ->
  h1:mem ->
  Lemma (requires invariant k h0 /\
         modifies_one r h0 h1 /\
         ~(r `Set.mem` footprint k) /\
         ~(r `Set.mem` shared_footprint))
        (ensures invariant k h1)
let invariant_framing #ip #index_of_i i k h0 r h1 =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st -> AE.frame_invariant st h0 r h1
    | Real _ -> ()

abstract
val empty_log:
  #ip:ipkg ->
  #aeadAlg_of_i:(ip.t -> aeadAlg) ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  a:info1 #ip aeadAlg_of_i i ->
  k:key ip index_of_i i ->
  h:mem ->
  GTot Type0
let empty_log #ip #aeadAlg_of_i #index_of_i #i a k h =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st ->
      if AE.safeMac (index_of_i i) then
        AE.log st h == Seq.createEmpty
      else True
    | Real _ -> True
  else True

abstract
val empty_log_framing:
  #ip:ipkg ->
  #aeadAlg_of_i:(ip.t -> aeadAlg) ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  a:info1 #ip aeadAlg_of_i i ->
  k:key ip index_of_i i ->
  h0:mem ->
  r:rid ->
  h1:mem ->
  Lemma
    (requires (empty_log a k h0 /\
               modifies_one r h0 h1 /\
               ~(r `Set.mem` footprint k)))
    (ensures  (empty_log a k h1))
let empty_log_framing #ip #aeadAlg_of_i #index_of_i #i a k h0 r h1 =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st ->
      if AE.safeMac (index_of_i i) then
        AE.frame_log st Seq.createEmpty h0 r h1
      else ()
    | Real _ -> ()

abstract
val create_key:
  ip:ipkg ->
  // 2018.03.22: To guarantee erasure of `aeadAlg_of_i`,
  // we need to switch to the GTot effect
  // aeadAlg_of_i:(ip.t -> GTot aeadAlg) ->
  // ... and erase `ipkg` for good measure:
  // (let ip = reveal ip in ...
  aeadAlg_of_i:(ip.t -> aeadAlg) ->
  index_of_i:(ip.t -> I.id) ->
  i:ip.t{ip.registered i} ->
  a:info1 #ip aeadAlg_of_i i ->
  ST (key ip index_of_i i)
     (requires fun h0 -> model) ///\ live_region h0 (AE.prf_region (index_of_i i)))
     (ensures  fun h0 k h1 ->
       modifies_none h0 h1 /\
       fresh_regions (footprint k) h0 h1 /\
       empty_log #ip #aeadAlg_of_i #index_of_i #i a k h1 /\
       invariant k h1)
let create_key ip aeadAlg_of_i index_of_i i a =
  let id = index_of_i i in
  let prf_rgn = AE.prf_region id in //new_region a.parent in
  let log_rgn = new_region a.parent in
//  let st = AE.gen id prf_rgn log_rgn in
//  if model then
//     Ideal ck st
//  else ck
  admit() // Ideal/Real

assume val coerceT_key:
  ip:ipkg ->
  aeadAlg_of_i:(ip.t -> aeadAlg) ->
  index_of_i:(ip.t -> I.id) ->
  i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} ->
  a:info1 #ip aeadAlg_of_i i ->
  keyrepr a ->
  GTot (key ip index_of_i i)

assume val coerce_key:
  ip:ipkg ->
  aeadAlg_of_i:(ip.t -> aeadAlg) ->
  index_of_i:(ip.t -> I.id) ->
  i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} ->
  a:info1 #ip aeadAlg_of_i i->
  k0:keyrepr a ->
  ST (key ip index_of_i i)
    (requires fun h0 -> True)
    (ensures fun h0 k h1 -> k == coerceT_key ip aeadAlg_of_i index_of_i i a k0
      /\ modifies_none h0 h1 /\ fresh_regions (footprint k) h0 h1
      /\ empty_log #ip #aeadAlg_of_i #index_of_i #i a k h1 /\ invariant k h1)

let len #ip #aeadAlg_of_i #i (u:info1 #ip aeadAlg_of_i i) =
  keylen u.alg

let local_ae_pkg (ip:ipkg) (aeadAlg_of_i:ip.t -> aeadAlg) (index_of_i: ip.t -> I.id)
  : Tot (local_pkg ip)
  =
  LocalPkg
    (key ip index_of_i)
    (info1 #ip aeadAlg_of_i)
    (len #ip #aeadAlg_of_i)
    ideal
    shared_footprint
    (footprint #ip #index_of_i)
    (invariant #ip #index_of_i)
    (invariant_framing #ip #index_of_i)
    (empty_log #ip #aeadAlg_of_i #index_of_i)
    (empty_log_framing #ip #aeadAlg_of_i #index_of_i)
    (create_key ip aeadAlg_of_i index_of_i)
    (coerceT_key ip aeadAlg_of_i index_of_i)
    (coerce_key ip aeadAlg_of_i index_of_i)

let mp (ip:ipkg) (aeadAlg_of_i:ip.t -> aeadAlg) (index_of_i:ip.t -> I.id)
  : ST (pkg ip)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 ->
    //17-12-01 we need freshness and emptyness of the new table + local packaging
    modifies_mem_table p.define_table h0 h1 /\
    p.package_invariant h1)
=
  memoization_ST #ip (local_ae_pkg ip aeadAlg_of_i index_of_i)

val encrypt:
  ip:ipkg ->
  aeadAlg_of_i: (ip.t -> aeadAlg) ->
  index_of_i: (ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  k: key ip (* aeadAlg_of_i *) index_of_i i -> nat -> ST nat
  (requires fun h0 -> invariant k h0)
  (ensures fun h0 c h1 ->
    modifies (rset_union (footprint k) shared_footprint) h0 h1
    /\ invariant k h1)
let encrypt _ _ _ #_ k v = v + 1
 // if model then
 // ...
 // else AEAD.encrypt k.Real?.ck.info.alg v
