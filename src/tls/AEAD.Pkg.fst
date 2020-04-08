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

let is_ideal #_ #_ #_ k = Ideal? k

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

let footprint #ip #index_of_i #i k =
  Set.lemma_equal_intro (Set.empty `Set.intersect` shared_footprint) Set.empty;
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st -> AE.footprint st
    | Real _ -> Set.empty
  else Set.empty

let invariant #ip #index_of_i #i k h =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st -> AE.invariant st h
    | Real _ -> True
  else True

let invariant_framing #ip #index_of_i i k h0 r h1 =
  if model then
    let k: _key index_of_i i = k in
    match k with
    | Ideal _ st -> AE.frame_invariant st h0 r h1
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

let coerceT_key _ _ _ _ _ _ = admit ()

let coerce_key _ _ _ _ _ _ = admit ()

let encrypt _ _ _ #_ k v = v + 1
 // if model then
 // ...
 // else AEAD.encrypt k.Real?.ck.info.alg v
