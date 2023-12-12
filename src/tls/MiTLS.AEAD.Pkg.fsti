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
module MiTLS.AEAD.Pkg
open MiTLS

open FStar.Bytes

open MiTLS.Mem
open MiTLS.Pkg

module AE = MiTLS.AEAD
module I  = MiTLS.Crypto.Indexing

/// TODO package instead StAE? what to do with the algorithm?

type aeadAlg =
  | AES_GCM128
  | AES_GCM256

let ideal : (b:bool{b ==> model}) =
  assume (b2t Flags.ideal_AEAD ==> model);
  Flags.ideal_AEAD

type safe (#ip:ipkg) (i:ip.t) = ideal /\ ip.honest i

private let is_safe (#ip:ipkg) (i:ip.t{ip.registered i}) : ST bool
  (requires fun _ -> True)
  (ensures  fun h0 b h1 -> modifies_none h0 h1 /\ (b <==> safe i)) =
  let honest = ip.get_honesty i in
  ideal && honest

type info = {
  parent: r:rgn{~(is_tls_rgn r)};
  alg: aeadAlg
}

type info1 (#ip:ipkg) (aeadAlg_of_i:ip.t -> aeadAlg) (i:ip.t) =
  u:info{u.alg == aeadAlg_of_i i}

let aead_pkg_keylen (alg:aeadAlg) : keylen = match alg with
  | AES_GCM128 -> 32ul
  | AES_GCM256 -> 48ul

type keyrepr (u:info) = lbytes32 (aead_pkg_keylen u.alg)

// FIXME(adl) 16/02/18 had to remove abstract to avoid F* crash

val concrete_key : Type0

val _key (#ip:ipkg) (index_of_i:ip.t -> I.id) (i:ip.t) : Type0

val is_ideal (#ip:ipkg) (#index_of_i:ip.t -> I.id) (#i:ip.t) (_:_key index_of_i i) : Tot bool

(* abstract *)
type key (ip:ipkg)
  (index_of_i:ip.t -> I.id)
  (i:ip.t{ip.registered i}) =
  (if model then
    k:_key index_of_i i{is_ideal k <==> safe i}
  else
    concrete_key)

val usage:
  #ip:ipkg ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  k:key ip index_of_i i ->
  GTot info

val keyval:
  #ip:ipkg ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  k:key ip index_of_i i ->
  GTot (keyrepr (usage k))

let shared_footprint : rset =
  if model then AE.shared_footprint
  else Set.empty

val footprint:
  #ip:ipkg ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  k:key ip index_of_i i ->
  GTot (s:rset{s `Set.disjoint` shared_footprint})

(** The local AEAD invariant *)
val invariant:
  #ip:ipkg ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  k:key ip index_of_i i ->
  h:mem ->
  GTot Type0

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

val empty_log:
  #ip:ipkg ->
  #aeadAlg_of_i:(ip.t -> aeadAlg) ->
  #index_of_i:(ip.t -> I.id) ->
  #i:ip.t{ip.registered i} ->
  a:info1 #ip aeadAlg_of_i i ->
  k:key ip index_of_i i ->
  h:mem ->
  GTot Type0

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

val coerceT_key:
  ip:ipkg ->
  aeadAlg_of_i:(ip.t -> aeadAlg) ->
  index_of_i:(ip.t -> I.id) ->
  i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} ->
  a:info1 #ip aeadAlg_of_i i ->
  keyrepr a ->
  GTot (key ip index_of_i i)

val coerce_key:
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

let x = keylen


let len #ip #aeadAlg_of_i #i (u:info1 #ip aeadAlg_of_i i) =
  aead_pkg_keylen u.alg

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
