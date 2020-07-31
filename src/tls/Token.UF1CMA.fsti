(* Idealizing derived authentication tokens; independent of TLS, used for TLS 1.2 Finished message payloads. *)
module Token.UF1CMA

//TODO use this file instead of TLSPRF

open FStar.Bytes
open Mem
open Pkg

module M = LowStar.Modifies
module DT = DefineTable
module H = Hashing.Spec

// this file is adapted from HMAC.UFCMA but simpler, and yield
// probabilistic security: the advantage of an adversary guessing the
// random token is just 1/#tokens. (Do we need to enforce a single
// verification attempt?)

inline_for_extraction noextract
let ideal = Flags.ideal_HMAC
// secret idealization flag for the UF1CMA assumption
//TODO use a separate flag

type safe (#ip:ipkg) (i:ip.t) = b2t ideal /\ ip.honest i

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

// formally agile in the KDF algorithm, which controls the token length.
type ha = H.alg

// initial parameters
noeq type info =
| Info: 
  parent: rgn {~ (is_tls_rgn parent)} ->
  alg: ha -> 
  good: bool ->
  info

type info0 (#ip:ipkg) (ha_of_i: ip.t -> ha) (good_of_i: ip.t -> bool) (i:ip.t) =
  a:info{a.alg == ha_of_i i /\ a.good == good_of_i i}

let uf1cma_keylen (a:H.alg) : keylen = H.hash_len a
type keyrepr (a:H.alg) = lbytes32 (uf1cma_keylen a)
type tag (a:H.alg) = lbytes32 (uf1cma_keylen a)

val key (#ip:ipkg) (ha_of_i: ip.t -> ha) (good_of_i: ip.t -> bool) (i:regid ip) : Tot Type0

val usage
  (#ip: _) (#hofi: _) (#gofi: _) (#i: _) (k:key #ip hofi gofi i)
: Tot (info0 hofi gofi i)

val keyval
  (#ip: _) (#hofi: _) (#gofi: _) (#i: _) (k:key #ip hofi gofi i)
: GTot (keyrepr (usage k).alg)

val footprint
  (#ip: ipkg)
  (#hofi: ip.t -> ha)
  (#gofi: ip.t -> bool)
: DT.local_fp (key #ip hofi gofi)

val create:
  #ip:ipkg ->
  ha_of_i: (i:ip.t -> ha) ->
  good_of_i: (ip.t -> bool) ->
  i: regid ip ->
  u: info0 ha_of_i good_of_i i ->
  ST (k:key ha_of_i good_of_i i)
  (requires fun _ -> model)
  (ensures fun h0 k h1 ->
    M.modifies M.loc_none h0 h1 /\
    usage k == u /\
    fresh_loc (footprint k) h0 h1)

val coerceT (#ip: ipkg) (ha_of_i: ip.Pkg.t -> ha) (good_of_i: ip.Pkg.t -> bool)
  (i: regid ip{~(safe i)}) (u: info0 ha_of_i good_of_i i)
  (kv: lbytes32 (uf1cma_keylen u.alg)) : GTot (key ha_of_i good_of_i i)

val coerce:
  #ip: ipkg ->
  ha_of_i: (ip.Pkg.t -> ha) ->
  good_of_i: (ip.Pkg.t -> bool) ->
  i: regid ip{~(safe i)} ->
  u: info0 ha_of_i good_of_i i ->
  kv: lbytes32 (uf1cma_keylen u.alg) -> ST (k:key ha_of_i good_of_i i)
  (requires fun _ -> True)
  (ensures fun h0 k h1 ->
    M.modifies M.loc_none h0 h1 /\
    k == coerceT ha_of_i good_of_i i u kv /\
    usage k == u /\
    fresh_loc (footprint k) h0 h1)

val token:
  #ip:ipkg ->
  #ha_of_i: (ip.Pkg.t -> ha) ->
  #good_of_i: (ip.Pkg.t -> bool) ->
  #i:regid ip ->
  k:key ha_of_i good_of_i i ->
  ST (tag (usage k).alg)
  (requires fun h0 -> safe i ==> (usage k).good)
  (ensures fun h0 t h1 -> M.modifies (footprint k) h0 h1)

val verify:
  #ip:ipkg ->
  #ha_of_i: (ip.Pkg.t -> ha) ->
  #good_of_i: (ip.Pkg.t -> bool) ->
  #i:regid ip ->
  k:key ha_of_i good_of_i i ->
  t: tag (usage k).alg ->
  ST bool
  (requires fun _ -> True)
  (ensures fun h0 b h1 ->
    M.modifies M.loc_none h0 h1 /\
    (b /\ safe i ==> (usage k).good))

let localpkg (ip: ipkg) (ha_of_i: (i:ip.Pkg.t -> ha)) (good_of_i: ip.Pkg.t -> bool)
  : Pure (Pkg.local_pkg ip)
  (requires True) (ensures fun p ->
    p.Pkg.key == key ha_of_i good_of_i /\
    p.Pkg.info == info0 ha_of_i good_of_i)
  =
  Pkg.LocalPkg
    (key ha_of_i good_of_i)
    (info0 ha_of_i good_of_i)
    (usage #ip #ha_of_i #good_of_i)
    (fun #i u -> uf1cma_keylen u.alg)
    (b2t ideal)
    (footprint #ip #ha_of_i #good_of_i) // local footprint
    (fun #_ k h -> True) // local invariant
    (fun #i k h0 l h1 -> ()) // Local invariant framing
    (create ha_of_i good_of_i)
    (coerceT ha_of_i good_of_i)
    (coerce ha_of_i good_of_i)

//TODO (later) support dynamic key compromise
