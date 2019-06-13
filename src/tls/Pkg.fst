module Pkg

/// We develop a generic model for key extraction and key derivation
/// parametrized by a usage function from labels to derived keyed
/// functionalities.
///
/// * captures resumption derivations via bounded-recursive instantiation.
/// * captures PRF-ODH double game
/// * applicable to the full extract/expand key schedule of TLS 1.3
/// * models partial key compromise, controlled by the adversary for each new key
/// * features agility on hash algorithms and DH groups, and ideal-only indexes.
///
/// We first embed first-class modules as datatype "packages". This
/// module specifies three kinds of packages (for indexes, local
/// functionalities, and multi-instance functionalities) and provides
/// generic "packaging" code from local packages to multi-instance
/// packages.

open Mem

module DT = DefineTable
module M = LowStar.Modifies
module MDM = FStar.Monotonic.DependentMap
module MH = FStar.Monotonic.Heap
module HS = FStar.HyperStack

type bytes = FStar.Bytes.bytes
//let lbytes32 = FStar.Bytes.lbytes32
type lbytes32 n = FStar.Bytes.lbytes (UInt32.v n)

/// Index packages provide an abstract index for instances, with an
/// interface to project (ghost) indexes to (concrete) runtime
/// parameters, such as algorithms or key length, and to define their
/// "honesty", thereby controlling their conditional idealization.
///
/// We distinguish between "honest", which refers to the adversary's
/// intent (and is considered public) and "safe", which controls
/// fine-grained idealization: roughly safe i = Flags.ideal /\ honest i

inline_for_extraction
noeq type ipkg = | Idx:
  t: eqtype  (* abstract type for indexes *) ->
  // three abstract predicates implemented as witnesses, and a stateful reader.
  registered: (i:t -> GTot Type0) ->
  honest: (i:t -> GTot Type0) ->
  (* stateful reader, returning either honest or corrupt *)
  get_honesty: (i:t{registered i} -> ST bool
    (requires fun _ -> True)
    (ensures fun h0 b h1 -> h0 == h1 /\ (b <==> honest i))) ->
  ipkg

type regid (ip:ipkg) = i:ip.t{ip.registered i}

/// Keyed functionality define Key packages, parametric in their
/// indexes, but concrete on their key randomness. The package is
/// meant to be used merely as a generic interface for
/// creation/coercion; instances may have any number of other
/// functions (such as leak, for instance).
///
/// [ip] defines the abstract indexes used in the package.
///
/// [info] represents creation-time information, such as algorithms or
/// key lengths; it is largely determined by the (ghost) index, so
/// that all users of the instance agree on them, with details left to
/// each package definition. (For instance, parent regions for
/// allocating ideal state may differ.) We pass both the index and its
/// info inasmuch as the index will be erased.
///
/// [len] provides the concrete length of random key materials for
/// creating a new instance, as a function of the creation-time info.
///
/// [create] and [coerce] generate new instances; [create] requires
/// `model`, whereas [coerce] requires corruption when idealizing;
/// hence the two may be callable on the same indexes.
///
/// We must have [create i a == coerce i a (sample (len a))]
/// we currently check by hand that this follows from F* semantics.


/// Derived key length restriction when using HKDF
type keylen = l:UInt32.t {0 < UInt32.v l /\ UInt32.v l <= 255}

/// A package describes how instances of an idealized,
/// multi-instance cryptographic functionality are created.
/// 
/// It implements the key packages from the code-based
/// game-playing proof framework of https://eprint.iacr.org/2018/306.pdf
inline_for_extraction noextract
noeq type pkg (ip: ipkg) = | Pkg:
  // Type of instances
  key: (regid ip -> Type0) ->
  // Concrete parameters of each instance
  info: Type ->
  // Consistency relation between concrete info and crypto index
  valid_info: (i:ip.t{model} -> info -> Type) ->
  // Length of key used to create an instance
  len: (info -> keylen) ->
  // Type-level idealization flag of the functionality
  ideal: Type0{ideal ==> model} ->
  // when modelling, we maintain a global table of all allocated
  // instances of the package. Only the package modifies the table,
  // when a new instance is created (regardless of ideal flag).
  //
  // The package footprint is a function of the table contents;
  // by convention the define table is excluded from the footprint.
  define_table: DT.dt key ->
  footprint: (mem -> GTot M.loc) ->
  footprint_framing: (h0:mem -> h1:mem -> Lemma
    (requires DT.unchanged define_table h0 h1)
    (ensures footprint h0 == footprint h1)) ->
  // we maintain a package invariant,
  // which only depends on the table and footpring.
  package_invariant: (mem -> Type0) ->
  package_invariant_framing: (h0:mem -> l:M.loc -> h1:mem -> Lemma
    (requires package_invariant h0 /\
      M.modifies l h0 h1 /\ define_table `DT.live` h0 /\
      M.loc_disjoint l (DT.loc define_table) /\ M.loc_disjoint l (footprint h0))
    (ensures package_invariant h1)) ->
  // create and coerce, with a shared post-condition and framing lemma
  // so that [derive] can pass the post-condition to its caller; the
  // concrete part of the postcondition is what we need in [derive].
  post: (#i:regid ip -> info -> key i -> mem -> GTot Type0) ->
  post_framing: (#i:regid ip -> a:info -> k:key i ->
    h0:mem -> l:M.loc -> h1:mem -> Lemma
     (requires post a k h0 /\
       M.modifies l h0 h1 /\ define_table `DT.live` h0 /\
       M.loc_disjoint l (DT.loc define_table) /\ M.loc_disjoint l (footprint h0))
     (ensures post a k h1)) ->
  // Create an honest instance (that may or may not be idealized,
  // depending on the secret idealization flag).
  create: (i:regid ip -> a:info -> ST (key i)
    (requires fun h0 -> model /\
      valid_info i a /\
      package_invariant h0 /\
      DT.fresh define_table i h0)
    (ensures fun h0 k h1 ->
      post a k h1 /\
      package_invariant h1 /\
      (footprint h1) `M.loc_includes` (footprint h0) /\
      DT.extended define_table k h0 h1)) ->
  // We need a functional specification of coerce, to ensure
  // that the concrete (model off) functionality behaves like
  // the real (model on, ideal off) one
  coerceT: (i:regid ip{ideal ==> ~(ip.honest i)} ->
    a:info -> lbytes32 (len a) -> GTot (key i)) ->
  coerce: (i:regid ip{ideal ==> ~(ip.honest i)} ->
    a:info -> rk: lbytes32 (len a) -> ST (key i)
    (requires fun h0 -> (model ==> valid_info i a) /\
      package_invariant h0 /\
      DT.fresh define_table i h0)
    (ensures fun h0 k h1 ->
      k == coerceT i a rk /\
      post a k h1 /\ package_invariant h1 /\
      (footprint h1) `M.loc_includes` (footprint h0) /\
      DT.extended define_table k h0 h1)) ->
  pkg ip

/// packages of instances with local private state, before ensuring
/// their unique definition at every index and the disjointness of
/// their footprints.
inline_for_extraction noextract
noeq type local_pkg (ip: ipkg) =
| LocalPkg:
  key: (regid ip -> Type0) ->
  info: Type ->
  valid_info: (i:ip.t{model} -> info -> Type) ->
  len: (info -> keylen) ->
  ideal: Type0{ideal ==> model} ->
  local_footprint: DT.local_fp key ->
  inv: (#i:regid ip -> key i -> mem -> GTot Type0) ->
  inv_framing: (#i:regid ip -> k:key i ->
    h0:mem -> l:M.loc -> h1:mem -> Lemma
    (requires inv k h0 /\ M.modifies l h0 h1 /\ M.loc_disjoint l (local_footprint k))
    (ensures inv k h1)) ->
  create: (i:regid ip -> a:info -> ST (key i)
    (requires fun h0 -> model /\ valid_info i a)
    (ensures fun h0 k h1 -> M.modifies M.loc_none h0 h1 /\
       inv k h1 /\ fresh_loc (local_footprint k) h0 h1)) ->
  coerceT: (i:regid ip{ideal ==> ~(ip.honest i)} ->
    a:info -> lbytes32 (len a) -> GTot (key i)) ->
  coerce: (i:regid ip{ideal ==> ~(ip.honest i)} ->
    a:info -> rk:lbytes32 (len a) -> ST (key i)
    (requires fun h0 -> model ==> valid_info i a)
    (ensures fun h0 k h1 -> k == coerceT i a rk /\ M.modifies M.loc_none h0 h1 /\
      inv k h1 /\ fresh_loc (local_footprint k) h0 h1)) ->
  local_pkg ip

// Memoization functor from local to global packages that memoize
// instances produced by create/coerce and maintain their joint
// invariant.
//
// We provide both a pure, unfolded functor and a stateful,
// table-allocating functor; the latter is probably too opaque for
// correlating its result with the source definitions.

inline_for_extraction noextract
let memoization (#ip:ipkg) (p:local_pkg ip) ($dt:DT.dt p.key) : pkg ip
  =  
  [@inline_let]
  let footprint h = DT.footprint dt p.local_footprint h in    
  [@inline_let]
  let package_invariant h =
    M.loc_disjoint (DT.loc dt) (footprint h) /\
    DT.dt_forall dt p.inv h in
  [@inline_let]
  let package_invariant_framing (h0:mem) (l:M.loc) (h1:mem)
    : Lemma
      (requires package_invariant h0 /\
        M.modifies l h0 h1 /\ dt `DT.live` h0 /\
        M.loc_disjoint l (DT.loc dt) /\ M.loc_disjoint l (footprint h0))
      (ensures package_invariant h1)
    =
    DT.lemma_forall_frame dt p.inv p.local_footprint p.inv_framing h0 l h1;
    DT.lemma_footprint_frame dt p.local_footprint h0 h1
    in
  [@inline_let]
  let create (i:regid ip) (a:p.info) : ST (p.key i)
    (requires fun h0 -> model /\ p.valid_info i a /\
      package_invariant h0 /\ DT.fresh dt i h0)
    (ensures fun h0 k h1 -> package_invariant h1 /\
      (footprint h1) `M.loc_includes` (footprint h0) /\
      DT.extended dt k h0 h1)
    =
    let h0 = get () in
    let t0 = DT.ideal dt in
    recall t0;
    assert_norm(DT.live dt h0 == (model ==> h0 `HS.contains` (DT.ideal dt)));
    let k : p.key i = p.create i a in
    let h1 = get() in
    DT.lemma_footprint_frame dt p.local_footprint h0 h1;
    DT.lemma_forall_frame dt p.inv p.local_footprint p.inv_framing h0 M.loc_none h1;
    fresh_is_disjoint (DT.loc dt) (p.local_footprint k) h0 h1;
    DT.extend dt k;
    let h2 = get () in
    p.inv_framing k h1 (DT.loc dt) h2;
    DT.lemma_footprint_extend dt p.local_footprint k h1 h2;
    DT.lemma_forall_extend dt p.inv p.local_footprint p.inv_framing k h1 h2;
    k
    in
  [@inline_let]
  let coerce (i:regid ip{p.ideal ==> ~(ip.honest i)})
    (a:p.info) (k0:lbytes32 (p.len a))
    : ST (p.key i)
    (requires fun h0 -> (model ==> p.valid_info i a) /\
      package_invariant h0 /\ DT.fresh dt i h0)
    (ensures fun h0 k h1 -> k == p.coerceT i a k0 /\
      package_invariant h1 /\
      (footprint h1) `M.loc_includes` (footprint h0) /\
      DT.extended dt k h0 h1)
    =
    if model then (
      let h0 = get () in
      let t0 = DT.ideal dt in
      recall t0;
      assert_norm(DT.live dt h0 == (model ==> h0 `HS.contains` (DT.ideal dt)));
      let k : p.key i = p.coerce i a k0 in
      let h1 = get() in
      DT.lemma_footprint_frame dt p.local_footprint h0 h1;
      DT.lemma_forall_frame dt p.inv p.local_footprint p.inv_framing h0 M.loc_none h1;
      fresh_is_disjoint (DT.loc dt) (p.local_footprint k) h0 h1;
      DT.extend dt k;
      let h2 = get () in
      p.inv_framing k h1 (DT.loc dt) h2;
      DT.lemma_footprint_extend dt p.local_footprint k h1 h2;
      DT.lemma_forall_extend dt p.inv p.local_footprint p.inv_framing k h1 h2;
      k
    ) else (
      let h0 = get () in
      let k = p.coerce i a k0 in
      let h1 = get() in
      DT.lemma_footprint_frame dt p.local_footprint h0 h1;
      DT.lemma_forall_frame dt p.inv p.local_footprint p.inv_framing h0 M.loc_none h1;
      k
    )
    in
  (Pkg
    p.key
    p.info
    p.valid_info
    p.len
    p.ideal
    dt
    footprint (DT.lemma_footprint_frame dt p.local_footprint)
    package_invariant package_invariant_framing
    (fun #_ _ _ h -> True) (fun #_ _ _ _ _ _ -> ())
    create p.coerceT coerce)

noextract
let locally_packaged (#ip:ipkg) (p:pkg ip) (p':local_pkg ip) =
  LocalPkg?.key p' == Pkg?.key p /\
  p == memoization p' p.define_table

inline_for_extraction noextract
let memoization_ST (#ip:ipkg) (p:local_pkg ip)
  : ST (pkg ip)
  (requires fun h0 -> True)
  (ensures fun h0 q h1 ->
    locally_packaged q p /\
    q.package_invariant h1 /\
    fresh_loc (DT.loc q.define_table) h0 h1)
  =
  let dt = DT.alloc p.key in
  let h1 = get() in
  [@inline_let] let q = memoization #ip p dt in
  DT.lemma_footprint_empty dt p.local_footprint h1;
  DT.lemma_forall_empty dt p.inv h1;
  q

(*
Style for enforcing full normalization to enable erasure of `pkg` arguments:

inline_for_extraction
val derive: x:pkg -> bool -> x.t
let derive x n =
  normalize_term (x.f n)

inline_for_extraction
val create: bool -> ret
let create n = B n

(** Coercion to reveal the head of the implicit match in [derive] *)
noextract
val as_create: x:pkg{x.t == ret /\ x.f == create} -> y:pkg{x == y}
let as_create x = Pkg create x.n

val test: x:pkg{x.t == ret /\ x.f == create} -> ret
let test x = derive (as_create x) true
*)
