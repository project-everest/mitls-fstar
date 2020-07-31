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

module M = LowStar.Modifies
module DT = DefineTable
module AE = AEAD
module I  = Crypto.Indexing

private val is_safe: #ip:ipkg -> i:ip.t{ip.registered i} -> ST bool
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> modifies_none h0 h1 /\ (b <==> safe i))
let is_safe #ip i =
  let honest = ip.get_honesty i in
  ideal && honest

// FIXME(adl) 16/02/18 had to remove abstract to avoid F* crash

noeq type concrete_key =
  | AEAD: u:info -> k:keyrepr u -> concrete_key

noeq type _key (#ip:ipkg) (index_of_i:ip.t -> I.id) (i:ip.t) =
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

let usage #ip #index_of_i #i k =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal ck _ -> ck.u
    | Real ck -> ck.u
  else k.u

let keyval #ip #index_of_i #i k =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal ck _ -> ck.k
    | Real ck -> ck.k
  else k.k

let footprint #ip #index_of_i =
  fun #i k ->
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st -> M.loc_none // AE.footprint st
    | Real _ -> M.loc_none
  else M.loc_none

(** The local AEAD invariant *)
let invariant #ip #index_of_i #i k h =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st -> AE.invariant st h
    | Real _ -> True
  else True

let invariant_framing #ip #index_of_i #i k h0 r h1 =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st -> admit() //AE.frame_invariant st h0 r h1
    | Real _ -> ()

let empty_log #ip #aeadAlg_of_i #index_of_i #i a k h =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st ->
      if AE.safeMac (index_of_i i) then
        AE.log st h == Seq.empty
      else True
    | Real _ -> True
  else True

let empty_log_framing #ip #aeadAlg_of_i #index_of_i #i a k h0 r h1 =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st ->
      if AE.safeMac (index_of_i i) then
        AE.frame_log st Seq.empty h0 r h1
      else ()
    | Real _ -> ()

let create_key ip aeadAlg_of_i index_of_i i a =
  let id = index_of_i i in
  let prf_rgn = AE.prf_region id in //new_region a.parent in
  let log_rgn = new_region a.parent in
//  let st = AE.gen id prf_rgn log_rgn in
//  if model then
//     Ideal ck st
//  else ck
  admit() // Ideal/Real

let coerceT_key = admit ()

let coerce_key = admit ()

(*

let local_ae_pkg (ip:ipkg) (aeadAlg_of_i:ip.t -> aeadAlg) (index_of_i: ip.t -> I.id)
  : Tot (local_pkg ip)
  =
  LocalPkg
    (key ip index_of_i)
    (info1 #ip aeadAlg_of_i)
    (fun #i k -> admit())
    (len #ip #aeadAlg_of_i)
    (b2t ideal)
    (footprint #ip #index_of_i)
    (invariant #ip #index_of_i)
    (invariant_framing #ip #index_of_i)
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

*)
