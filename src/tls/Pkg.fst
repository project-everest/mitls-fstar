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
type keylen = l:UInt32.t {UInt32.v l <= 256}


(* Definedness *)

// Framing of package invariants can be done w.r.t either a region that is
// disjoint from tls_define_region, or a define table that must be at a
// different address than the package's define_table
noeq type pkg_inv_r =
  | Pinv_region: r:rid{r `disjoint` tls_define_region} -> pkg_inv_r
  | Pinv_define: #it:eqtype -> #vt:(it -> Type) -> t:mem_table vt -> pkg_inv_r

// When calling create or coerce, the footprint of a package grows only with
// fresh subregions
type modifies_footprint (fp:mem->GTot rset) h0 h1 =
  forall (r:rid). (Set.mem r (fp h0) /\ ~(Set.mem r (fp h1))) ==> fresh_region r h0 h1  
  //AR: 12/05: Could use the pattern {:pattern (Set.mem r (fp h0)); (Set.mem r (fp h1))}

noeq type pkg (ip: ipkg) = | Pkg:
  key: (i:ip.t {ip.registered i} -> Type0)  (* indexed state of the functionality *) ->
  $info: (ip.t -> Type0)                    (* creation-time arguments, typically refined using i:ip.t *) ->
  len: (#i:ip.t -> info i -> keylen)        (* computes the key-material length from those arguments *) ->
  ideal: Type0                              (* type-level access to the ideal flag of the package *) ->
  //17-11-13 do we need to know that ideal ==> model?
  //17-11-13 is type-level access enough?

  // when modelling, we maintain a global table of all allocated
  // instances of the package. Only the package modifies the table.
  //
  // The package footprint is a function of the table contents;
  // that collects all global and instance-local regions, but not [define_table]
  define_table: mem_table #(i:ip.t {ip.registered i}) key ->
  footprint: (mem -> GTot rset) ->
  footprint_framing: (h0:mem -> h1:mem -> Lemma
    (requires mem_stable define_table h0 h1)
    (ensures footprint h0 == footprint h1)) ->

  // we maintain a package invariant,
  // which only depends on the table and footpring.
  package_invariant: (mem -> Type0) ->
  package_invariant_framing: (h0:mem -> r:pkg_inv_r -> h1:mem -> Lemma
    (requires package_invariant h0 /\ mem_contains define_table h0 /\
      (match r with
      | Pinv_region r -> modifies_one r h0 h1 /\ ~(Set.mem r (footprint h0))
      | Pinv_define #it #vt t ->
        mem_contains t h0 /\ modifies_mem_table t h0 h1 /\ mem_disjoint t define_table))
    (ensures package_invariant h1)) ->

  // create and coerce, with a shared post-condition and framing lemma
  // so that [derive] can pass the post-condition to its caller; the
  // concrete part of the postcondition is what we need in [derive].
  post: (#i:ip.t{ip.registered i} -> info i -> key i -> mem -> GTot Type0) ->
  post_framing: (#i:ip.t{ip.registered i} -> a:info i -> k:key i ->  h0:mem -> r:rid -> h1:mem -> Lemma
     (requires (post a k h0 /\ modifies_one r h0 h1 /\ ~(r `Set.mem` footprint h0)))
     (ensures (post a k h1))) ->

  create: (i:ip.t{ip.registered i} -> a:info i -> ST (key i)
    (requires fun h0 ->
      model /\
      package_invariant h0 /\
      mem_fresh define_table i h0)
    (ensures fun h0 k h1 ->
      post a k h1 /\ package_invariant h1 /\
      modifies_mem_table define_table h0 h1 /\
      modifies_footprint footprint h0 h1 /\
      mem_update define_table i k h0 h1)) ->

  coerceT: (i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} -> a:info i -> lbytes32 (len a) -> GTot (key i)) ->
  coerce: (i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} -> a:info i -> rk: lbytes32 (len a) -> ST (key i)
    (requires fun h0 ->
      package_invariant h0 /\
      mem_fresh define_table i h0)
    (ensures fun h0 k h1 ->
      k == coerceT i a rk /\
      post a k h1 /\ package_invariant h1 /\
      modifies_mem_table define_table h0 h1 /\
      modifies_footprint footprint h0 h1 /\
      mem_update define_table i k h0 h1)) ->
  pkg ip

type fresh_regions (s:rset) (h0:mem) (h1:mem) =
  forall (r:rid).{:pattern (Set.mem r s)} Set.mem r s ==>
    (fresh_region r h0 h1 \/ is_tls_rgn r)

/// packages of instances with local private state, before ensuring
/// their unique definition at every index and the disjointness of
/// their footprints.
noeq type local_pkg (ip: ipkg) =
| LocalPkg:
  $key: (i:ip.t{ip.registered i} -> Type0) ->
  info: (ip.t -> Type0) ->
  len: (#i:ip.t -> info i -> keylen) ->
  ideal: Type0 ->
  (* regions that are shared accross instances of the functionality *)
  shared_footprint: rset ->
  (* regions that are specific to each instance and freshly allocated when the instance is created *)
  local_footprint: (#i:ip.t{ip.registered i} -> key i -> GTot (s:rset{s `Set.disjoint` shared_footprint})) ->
  local_invariant: (#i:ip.t{ip.registered i} -> key i -> mem -> GTot Type0) (* instance invariant *) ->
  local_invariant_framing: (i:ip.t{ip.registered i} -> k:key i -> h0:mem -> r:rid -> h1:mem -> Lemma
    (requires local_invariant k h0 /\ modifies_one r h0 h1
      /\ ~(r `Set.mem` local_footprint k) /\ ~(r `Set.mem` shared_footprint))
    (ensures local_invariant k h1)) ->
  post: (#i:ip.t{ip.registered i} -> info i -> key i -> mem -> GTot Type0) ->
  post_framing: (#i:ip.t{ip.registered i} -> a:info i -> k:key i -> h0:mem -> r:rid -> h1:mem -> Lemma
    (requires (post a k h0 /\ modifies_one r h0 h1 /\ ~(r `Set.mem` local_footprint k)))
    (ensures (post a k h1))) ->
  create: (i:ip.t{ip.registered i} -> a:info i -> ST (key i)
    (requires fun h0 -> model)
    (ensures fun h0 k h1 ->
       modifies_none h0 h1 /\ local_invariant k h1 /\
       post a k h1 /\ fresh_regions (local_footprint k) h0 h1)) ->
  coerceT: (i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} -> a:info i -> lbytes32 (len a) -> GTot (key i)) ->
  coerce: (i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} -> a:info i -> rk:lbytes32 (len a) -> ST (key i)
    (requires fun h0 -> True)
    (ensures fun h0 k h1 -> k == coerceT i a rk /\
      modifies_none h0 h1 /\ local_invariant k h1 /\
      post a k h1 /\ fresh_regions (local_footprint k) h0 h1)) ->
  local_pkg ip

(* Iterators over Monotonic.Map, require a change of implementation *)
(* cwinter: this is now a Monotonic.DependentMap *)
(* 2018.05.26 SZ: I can't find anything like these in Monotonic.DependentMap; cwinter? *)
let mm_fold (#a:eqtype) (#b:a -> Type) (t:MDM.map a b)
  (#rt:Type) (init:rt) (folder:(rt -> i:a -> b i -> GTot rt)) : GTot rt
  = admit()

let mm_fold_grow (#a:eqtype) (#b:a -> Type) (t:MDM.map a b) (t':MDM.map a b) (i:a) (v:b i)
  (#rt:Type) (init:rt) (folder:(rt -> i:a -> b i -> GTot rt)) : Lemma
  (requires t' == MDM.upd t i v)
  (ensures mm_fold t' init folder == folder (mm_fold t init folder) i v)
  = admit()

assume type mm_forall (#a:eqtype) (#b:a -> Type) (t:MDM.map a b)
  (p: (#i:a -> b i -> mem -> GTot Type0)) (h:mem)

let lemma_mm_forall_frame (#a:eqtype) (#b:a -> Type) (t:MDM.map a b)
  (p: (#i:a -> b i -> mem -> GTot Type0))
  (footprint: (#i:a -> v:b i -> GTot rset))
  (p_frame: (i:a -> v:b i -> h0:mem -> r:rid -> h1:mem ->
    Lemma (requires p v h0 /\ modifies_one r h0 h1 /\ ~(Set.mem r (footprint v)))
          (ensures p v h1)))
  (r:rid) (h0 h1:mem)
  : Lemma (requires mm_forall t p h0 /\ modifies_one r h0 h1 /\
            ~(Set.mem r (mm_fold t #rset Set.empty (fun s i k -> rset_union s (footprint k)))))
          (ensures mm_forall t p h1)
  = admit()

let lemma_mm_forall_extend (#a:eqtype) (#b:a -> Type) (t:MDM.map a b) (t':MDM.map a b)
  (p: (#i:a -> b i -> mem -> GTot Type0)) (i:a) (v:b i) (h0 h1:mem)
  : Lemma (requires mm_forall t p h1 /\ t' == MDM.upd t i v /\ p v h1)
          (ensures mm_forall t' p h1)
  = admit()

let lemma_mm_forall_init (#a:eqtype) (#b:a -> Type) (t:MDM.map a b)
  (p: (#i:a -> b i -> mem -> GTot Type0)) (h:mem)
  : Lemma (requires t == MDM.empty)
          (ensures mm_forall t p h)
  = admit()

let lemma_mm_forall_elim (#a:eqtype) (#b:a -> Type) (t:MDM.map a b)
  (p: (#i:a -> b i -> mem -> GTot Type0)) (i:a) (v:b i) (h:mem)
  : Lemma (requires mm_forall t p h /\ MDM.sel t i == Some v)
          (ensures p v h)
  = admit()

let lemma_union_com (s1:rset) (s2:rset) (s3:rset)
  : Lemma (rset_union s1 (rset_union s2 s3) == rset_union (rset_union s1 s2) s3)
  = admit()

(* obsolete, replaced by refinement of memoize_ST
unfold type mem_package (#ip:ipkg) (p:local_pkg ip) =
  p':pkg ip{
    Pkg?.key p' == LocalPkg?.key p /\
    Pkg?.info p' == LocalPkg?.info p /\
    Pkg?.len p' == LocalPkg?.len p /\
    Pkg?.ideal p' == LocalPkg?.ideal p /\
    (forall (#i:ip.t{ip.registered i}) (k:p.key i) (h:mem).
      (mem_defined p'.define_table i /\ p'.package_invariant h) ==> p.local_invariant k h) /\
    (forall (#i:ip.t{ip.registered i}) (a:p.info i) (k:p.key i) (h:mem).
      (Pkg?.post p') #i (a <: Pkg?.info p' i) (k <: Pkg?.key p' i) h ==> (LocalPkg?.post p) #i a k h)
  }
*)

// Memoization functor from local to global packages that memoize
// instances produced by create/coerce and maintain their joint
// invariant.
//
// We provide both a pure, unfolded functor and a stateful,
// table-allocating functor; the latter is probably too opaque for
// correlating its result with the source definitions.

#set-options "--z3rlimit 100 --admit_smt_queries true"
//unfold
noextract
let memoization (#ip:ipkg) (p:local_pkg ip) ($mtable: mem_table p.key): pkg ip =
  let footprint_extend (s:rset) (i:ip.t{ip.registered i}) (k:p.key i) =
    rset_union s (p.local_footprint k)
    in
  let footprint (h:mem): GTot rset =
    let instances_footprint =
      if model then
        let map = HS.sel h (itable mtable) in
        mm_fold map #rset Set.empty footprint_extend
      else Set.empty in
    rset_union p.shared_footprint instances_footprint
    in
  let footprint_grow (h0:mem) (i:ip.t{ip.registered i}) (k:p.key i) (h1:mem) : Lemma
    (requires (mem_update mtable i k h0 h1 /\ fresh_regions (p.local_footprint k) h0 h1))
    (ensures (modifies_footprint footprint h0 h1))
    =
    if model then
     begin
      let map = HS.sel h0 (itable mtable) in
      let map = HS.sel h1 (itable mtable) in
      let fp0 = footprint h0 in
      let fp1 = footprint h1 in
      mm_fold_grow map map i k #rset Set.empty footprint_extend;
      assert(fp1 == rset_union p.shared_footprint (rset_union (mm_fold map #rset Set.empty footprint_extend) (p.local_footprint k)));
      lemma_union_com p.shared_footprint (mm_fold map #rset Set.empty footprint_extend) (p.local_footprint k);
      assert(fp1 == rset_union fp0 (p.local_footprint k));
      assert(forall (r:rid). (Set.mem r fp1 /\ ~(Set.mem r fp0)) ==> Set.mem r (p.local_footprint k));
      assert(modifies_footprint footprint h0 h1)
     end
    else ()
    in
  let footprint_framing (h0:mem) (h1:mem) : Lemma
    (requires mem_stable mtable h0 h1)
    (ensures footprint h0 == footprint h1)
    = ()
  in
  let package_invariant h =
    (model ==>
      (let log : i_mem_table p.key = itable mtable in
      mm_forall (HS.sel h log) p.local_invariant h))
    in
  let ls_footprint (#i:ip.t{ip.registered i}) (k:p.key i) =
    rset_union (p.local_footprint k) p.shared_footprint
    in
  let ls_footprint_frame (i:ip.t{ip.registered i}) (k:p.key i) (h0:mem) (r:rid) (h1:mem)
    : Lemma (requires p.local_invariant k h0 /\ modifies_one r h0 h1
                      /\ ~(r `Set.mem` ls_footprint k))
            (ensures p.local_invariant k h1)
    =
    assert(~(r `Set.mem` ls_footprint k) <==> ~(r `Set.mem` p.local_footprint k) /\ ~(r `Set.mem` p.shared_footprint));
    p.local_invariant_framing i k h0 r h1
    in
  let package_invariant_framing (h0:mem) (r:pkg_inv_r) (h1:mem) : Lemma
    (requires package_invariant h0 /\ mem_contains mtable h0 /\
      (match r with
      | Pinv_region r -> modifies_one r h0 h1 /\ ~(Set.mem r (footprint h0))
      | Pinv_define #it #vt t -> mem_contains t h0 /\ modifies_mem_table t h0 h1 /\ mem_disjoint t mtable))
    (ensures package_invariant h1)
  =
    if model then
      let map = HS.sel h0 (itable mtable) in
      assert(mm_forall map p.local_invariant h0);
      (match r with
      | Pinv_region r ->
        assert(modifies_one r h0 h1 /\ r `disjoint` tls_define_region);
        lemma_mm_forall_frame map p.local_invariant ls_footprint ls_footprint_frame r h0 h1;
        lemma_mem_frame mtable h0 r h1
      | Pinv_define t ->
        assert(modifies_mem_table t h0 h1 /\ mem_disjoint t mtable);
        lemma_mm_forall_frame map p.local_invariant ls_footprint ls_footprint_frame tls_define_region h0 h1;
        lemma_mem_disjoint_stable t mtable h0 h1)
    else () in
  let create (i:ip.t{ip.registered i}) (a:p.info i) : ST (p.key i)
    (requires fun h0 -> model /\ package_invariant h0 /\ mem_fresh mtable i h0)
    (ensures fun h0 k h1 -> modifies_mem_table mtable h0 h1
      /\ modifies_footprint footprint h0 h1 /\ p.post a k h1
      /\ package_invariant h1 /\ mem_update mtable i k h0 h1)
    =
    let h0 = get () in
    let tbl : i_mem_table p.key = itable mtable in
    recall tbl;
    let k : p.key i = p.create i a in
    let h1 = get() in
    assert(HS.sel h0 tbl == HS.sel h1 tbl);
    package_invariant_framing h0 (Pinv_region tls_tables_region) h1;
    MDM.extend tbl i k;
    let h2 = get () in
    lemma_define_tls_honest_regions (p.local_footprint k);
    p.post_framing #i a k h1 tls_define_region h2;
    lemma_mm_forall_frame (HS.sel h1 tbl) p.local_invariant ls_footprint ls_footprint_frame tls_define_region h1 h2;
    p.local_invariant_framing i k h1 tls_define_region h2;
    lemma_mm_forall_extend (HS.sel h1 tbl) (HS.sel h2 tbl) p.local_invariant i k h1 h2;
    assume(HS.modifies_ref tls_define_region (Set.singleton (mem_addr (itable mtable))) h0 h2); // How to prove?
    footprint_grow h0 i k h2;
    k in
  let coerce (i:ip.t{ip.registered i /\ (p.ideal ==> ~(ip.honest i))}) (a:p.info i) (k0:lbytes32 (p.len a))
    : ST (p.key i)
    (requires fun h0 -> package_invariant h0 /\ mem_fresh mtable i h0)
    (ensures fun h0 k h1 -> k == p.coerceT i a k0
      /\ modifies_mem_table mtable h0 h1
      /\ modifies_footprint footprint h0 h1 /\ p.post a k h1
      /\ package_invariant h1 /\ mem_update mtable i k h0 h1)
    =
    if model then (
      let h0 = get () in
      let tbl : i_mem_table p.key = itable mtable in
      recall tbl;
      let k : p.key i = p.coerce i a k0 in
      let h1 = get() in
      assert(HS.sel h0 tbl == HS.sel h1 tbl);
      package_invariant_framing h0 (Pinv_region tls_tables_region) h1;
      MDM.extend tbl i k;
      let h2 = get () in
      lemma_define_tls_honest_regions (p.local_footprint k);
      p.post_framing #i a k h1 tls_define_region h2;
      lemma_mm_forall_frame (HS.sel h1 tbl) p.local_invariant ls_footprint ls_footprint_frame tls_define_region h1 h2;
      p.local_invariant_framing i k h1 tls_define_region h2;
      lemma_mm_forall_extend (HS.sel h1 tbl) (HS.sel h2 tbl) p.local_invariant i k h1 h2;
      assume(HS.modifies_ref tls_define_region (Set.singleton (mem_addr (itable mtable))) h0 h2); // How to prove?
      footprint_grow h0 i k h2;
      k
    ) else p.coerce i a k0
    in
  let post_framing (#i:ip.t{ip.registered i}) (a:p.info i) (k:p.key i)
    (h0:mem) (r:rid) (h1:mem) : Lemma
    (requires p.post a k h0 /\ modifies_one r h0 h1 /\ ~(Set.mem r (footprint h0)))
    (ensures p.post a k h1)
    =
    // FIXME(adl): we have a problem when model is false - we have nowhere to store
    // the joint footprint of the concrete state! for now we will assume
    // not model ==> local_footprint k = Set.empty for all k
    // We may have to maintain an erased (i_mem_table p.key) when model is off to
    // store the concrete footprints
    assume(~(Set.mem r (footprint h0)) ==> ~(Set.mem r (p.local_footprint k)));
    p.post_framing #i a k h0 r h1
    in
  (Pkg
    p.key
    p.info
    p.len
    p.ideal
    mtable footprint footprint_framing
    package_invariant package_invariant_framing
    p.post post_framing
    create p.coerceT coerce)

let memoization_ST (#ip:ipkg) (p:local_pkg ip)
  : ST (pkg ip)
  (requires fun h0 -> True)
  (ensures fun h0 q h1 ->
    LocalPkg?.key p == Pkg?.key q /\ // seems to help
    (let t: mem_table p.key = q.define_table in
    modifies_mem_table t h0 h1 /\
    q == memoization #ip p t /\
    q.package_invariant h1))
=
  let h0 = get() in
  let mtable: mem_table p.key = mem_alloc #(i:ip.t{ip.registered i}) p.key in
  let h1 = get() in
  let q = memoization #ip p mtable in
  //assert(q == memoization #ip p mtable); // fails when unfolding memoization AR: 12/05: this is no longer needed per the new inlining behavior
  // assert_norm(q == memoization #ip p mtable);// also fails, with squashing error
  (if model then lemma_mm_forall_init (HS.sel h1 (itable mtable)) p.local_invariant h1);
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
