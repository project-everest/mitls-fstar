module IK

/// Standalone experiment modelling key extraction and key derivation
/// parametrized by a usage function from labels to derived keyed
/// functionalities.
///
/// * captures resumption derivations via bounded-recursive instantiation.
/// * captures PRF-ODH double game
/// * applicable to the full extract/expand key schedule of TLS 1.3
/// * models partial key compromise, controlled by the adversary for each new key
/// * features agility on hash algorithms and DH groups, and ideal-only indexes.
///
/// We plan to split this file into many modules, as planned on slack.
///
/// Not done yet:
///
/// * define/review all idealization flags. How are they accessed?
///
/// * reliance on u_of_i in DH extraction (intuitive but hard to code)
///
/// * extraction: ensure all strongly-dependent types disappear and
///   (concretely) the key schedule directly allocates all key
///   instances.
///
/// * usage restriction for KDFs, based on a generalization of wellformed_id
///   (starting with an example of hashed-log derivation)
///
/// Note also that we support rather static agility and usages; while
/// this is sufficient for TLS, we might enable more details to be
/// bound at derivation-time as part of the derivation context.

open Mem

module MR = FStar.Monotonic.RRef
module MM = FStar.Monotonic.Map
module MH = FStar.Monotonic.Heap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let model = Flags.model

// temporary imports

type bytes = Platform.Bytes.bytes
let lbytes (len:UInt32.t) = Platform.Bytes.lbytes (UInt32.v len)

let sample (len:UInt32.t): ST (lbytes len)
    (requires fun h0 -> True)
    (ensures fun h0 r h1 -> h0 == h1)
  = CoreCrypto.random (UInt32.v len)

//unfold let doubleton (#a:eqtype) (e1:a) (e2:a) : Set.set a = Set.union (Set.singleton e1) (Set.singleton e2)

/// ------------------------------------------------------------------------------------------
/// module Pkg (stateless)
/// We embed first-class modules as datatype "packages"


/// Index packages provide an abstract index for instances, with an
/// interface to project (ghost) indexes to (concrete) runtime
/// parameters, such as algorithms or key length , and to define their
/// "honesty", thereby controlling their conditional idealization.
///
/// We distinguish between "honest", which refers to the adversary's
/// intent (and is considered public) and "safe", which controls
/// fine-grained idealization: roughly safe i = Flags.ideal /\ honest i

noeq type ipkg = | Idx:
  t: Type0{hasEq t} (* abstract type for indexes *) ->  //AR: 12/05: Could use the eqtype abbrev.
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

// FIXME(adl) can't write Set.set rgn because unification fails in pkg!!
// the second line embeds the definition of rgn because of the unification bug
// FIXME(adl) overcomplicated type because of transitive modifications.
// An rset can be thought of as a set of disjoint subtrees in the region tree
// rset are downward closed - if r is in s and r' extends r then r' is in s too
// this allows us to prove disjointness with negation of set membership

/// SZ: changed the definition to quantify over [HH.rid] rather than [rgn]
type rset = s:Set.set HH.rid{
  (forall (r1:HH.rid). (Set.mem r1 s ==>  //AR: 12/05: Add the pattern (Set.mem r1 s)?
     r1 <> HH.root /\
     (is_tls_rgn r1 ==> r1 `HH.extends` tls_tables_region) /\
     (forall (r':HH.rid).{:pattern (r' `HH.includes` r1)} r' `is_below` r1 ==> Set.mem r' s) /\
     (forall (r':HH.rid).{:pattern is_eternal_region r'} r' `is_above` r1 ==> is_eternal_region r')))}

let rset_union (s1:rset) (s2:rset)
  : Tot (s:rset{forall (r:HH.rid). Set.mem r s <==> (Set.mem r s1 \/ Set.mem r s2)}) //AR: 12/05: The refinement is not needed, as Set.union provides this mem property already
  = Set.union s1 s2

/// SZ: This is the strongest lemma that is provable
/// Note that this old stronger version doesn't hold:
///
/// let lemma_rset_disjoint (s:rset) (r:HH.rid) (r':HH.rid)
///  : Lemma (requires ~(Set.mem r s) /\ (Set.mem r' s))
///          (ensures  r `HH.disjoint` r')
///  = admit() // easy
///
let lemma_rset_disjoint (s:rset) (r:HH.rid) (r':HH.rid)
  : Lemma (requires Set.mem r s /\ ~(Set.mem r' s) /\ r' `is_below` r)
          (ensures  r `HH.disjoint` r')
  = ()

// We get from the definition of rset that define_region and tls_honest_region are disjoint
let lemma_define_tls_honest_regions (s:rset)
  : Lemma (~(Set.mem tls_define_region s) /\ ~(Set.mem tls_honest_region s))
  = ()

assume val lemma_disjoint_ancestors:
  r1:rgn -> r2:rgn -> p1:rgn{r1 `is_below` p1} -> p2:rgn{r2 `is_below` p2}
  -> Lemma (requires p1 <> p2) (ensures HH.disjoint r1 r2 /\ r1 <> r2)

type trivial_inv (#it:eqtype) (#vt:it -> Type) (m:MM.map' it vt) = True
type i_mem_table (#it:eqtype) (vt:it -> Type) =
  MM.t tls_define_region it vt trivial_inv
type mem_table (#it:eqtype) (vt:it -> Type) =
  (if model then i_mem_table vt else unit)

let itable (#it:eqtype) (#vt:it -> Type) (t:mem_table vt)
  : Pure (i_mem_table vt) (requires model) (ensures fun _ -> True) = t
let mem_addr (#it:eqtype) (#vt:it -> Type) (t:i_mem_table vt)
  : GTot nat = (HS.as_addr (MR.as_hsref t))

type mem_fresh (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (i:it) (h:mem) =
  model ==> MM.fresh (itable t) i h
type mem_defined (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (i:it) =
  model ==> (MR.witnessed (MM.defined (itable t) i))
type mem_update (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (i:it) (v:vt i) (h0:mem) (h1:mem) =
  mem_defined t i /\
  (model ==> MR.m_sel h1 (itable t) == MM.upd (MR.m_sel h0 (itable t)) i v)

type mem_stable (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (h0:mem) (h1:mem) =
  model ==> MR.m_sel h0 (itable t) == MR.m_sel h1 (itable t)
type mem_empty (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (h1:mem) =
  model ==> MR.m_sel h1 (itable t) == MM.empty_map it vt

type modifies_mem_table (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (h0:mem) (h1:mem) =
  (if model then
     (modifies_one tls_define_region h0 h1 /\
     HS.modifies_ref tls_define_region (Set.singleton (mem_addr (itable t))) h0 h1)
  else modifies_none h0 h1)
type mem_disjoint (#it:eqtype) (#vt:it -> Type) (t:mem_table vt)
  (#it':eqtype) (#vt':it' -> Type) (t':mem_table vt') =
  model ==> mem_addr (itable t) <> mem_addr (itable t')

let mem_alloc (#it:eqtype) (vt:it -> Type) : ST (mem_table vt)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> modifies_mem_table t h0 h1 /\ mem_empty t h1)
  =
  if model then MM.alloc #tls_define_region #it #vt #trivial_inv else ()

type mem_contains (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (h:mem) =
  model ==> h `contains` (MR.as_hsref (itable t))
let lemma_mem_disjoint_stable (#it:eqtype) (#vt:it -> Type) (t:mem_table vt)
  (#it':eqtype) (#vt':it' -> Type) (t':mem_table vt') (h0:mem) (h1:mem) : Lemma
  (requires modifies_mem_table t h0 h1 /\ mem_disjoint t t' /\ mem_contains t h0 /\ mem_contains t' h0)
  (ensures mem_stable t' h0 h1) = ()
let lemma_mem_frame (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (h0:mem) (r:HH.rid) (h1:mem) : Lemma
  (requires modifies_one r h0 h1 /\ tls_define_region `HH.disjoint` r /\ mem_contains t h0)
  (ensures mem_stable t h0 h1) = ()

// Framing of package invariants can be done w.r.t either a region that is
// disjoint from tls_define_region, or a define table that must be at a
// different address than the package's define_table
noeq type pkg_inv_r =
  | Pinv_region: r:HH.rid{r `HH.disjoint` tls_define_region} -> pkg_inv_r
  | Pinv_define: #it:eqtype -> #vt:(it -> Type) -> t:mem_table vt -> pkg_inv_r

// When calling create or coerce, the footprint of a package grows only with
// fresh subregions
type modifies_footprint (fp:mem->GTot rset) h0 h1 =
  forall (r:HH.rid). (Set.mem r (fp h0) /\ ~(Set.mem r (fp h1))) ==> stronger_fresh_region r h0 h1  //AR: 12/05: Could use the pattern {:pattern (Set.mem r (fp h0)); (Set.mem r (fp h1))}

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
  post_framing: (#i:ip.t{ip.registered i} -> a:info i -> k:key i ->  h0:mem -> r:HH.rid -> h1:mem -> Lemma
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

  coerceT: (i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} -> a:info i -> lbytes (len a) -> GTot (key i)) ->
  coerce: (i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} -> a:info i -> rk:lbytes (len a) -> ST (key i)
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
  forall (r:HH.rid).{:pattern (Set.mem r s)} Set.mem r s ==>
    (stronger_fresh_region r h0 h1 \/ is_tls_rgn r)

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
  local_invariant_framing: (i:ip.t{ip.registered i} -> k:key i -> h0:mem -> r:HH.rid -> h1:mem -> Lemma
    (requires local_invariant k h0 /\ modifies_one r h0 h1
      /\ ~(r `Set.mem` local_footprint k) /\ ~(r `Set.mem` shared_footprint))
    (ensures local_invariant k h1)) ->
  post: (#i:ip.t{ip.registered i} -> info i -> key i -> mem -> GTot Type0) ->
  post_framing: (#i:ip.t{ip.registered i} -> a:info i -> k:key i -> h0:mem -> r:HH.rid -> h1:mem -> Lemma
    (requires (post a k h0 /\ modifies_one r h0 h1 /\ ~(r `Set.mem` local_footprint k)))
    (ensures (post a k h1))) ->
  create: (i:ip.t{ip.registered i} -> a:info i -> ST (key i)
    (requires fun h0 -> model)
    (ensures fun h0 k h1 ->
       modifies_none h0 h1 /\ local_invariant k h1 /\
       post a k h1 /\ fresh_regions (local_footprint k) h0 h1)) ->
  coerceT: (i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} -> a:info i -> lbytes (len a) -> GTot (key i)) ->
  coerce: (i:ip.t{ip.registered i /\ (ideal ==> ~(ip.honest i))} -> a:info i -> rk:lbytes (len a) -> ST (key i)
    (requires fun h0 -> True)
    (ensures fun h0 k h1 -> k == coerceT i a rk /\
      modifies_none h0 h1 /\ local_invariant k h1 /\
      post a k h1 /\ fresh_regions (local_footprint k) h0 h1)) ->
  local_pkg ip

(* Iterators over Monotonic.Map, require a change of implementation *)

let mm_fold (#a:eqtype) (#b:a -> Type) (t:MM.map' a b)
  (#rt:Type) (init:rt) (folder:rt -> i:a -> b i -> GTot rt) : GTot rt
  = admit()

let mm_fold_grow (#a:eqtype) (#b:a -> Type) (t:MM.map' a b) (t':MM.map' a b) (i:a) (v:b i)
  (#rt:Type) (init:rt) (folder:rt -> i:a -> b i -> GTot rt) : Lemma
  (requires t' == MM.upd t i v)
  (ensures mm_fold t' init folder == folder (mm_fold t init folder) i v)
  = admit()

assume type mm_forall (#a:eqtype) (#b:a -> Type) (t:MM.map' a b)
  (p: #i:a -> b i -> mem -> GTot Type0) (h:mem)

let lemma_mm_forall_frame (#a:eqtype) (#b:a -> Type) (t:MM.map' a b)
  (p: #i:a -> b i -> mem -> GTot Type0)
  (footprint: #i:a -> v:b i -> GTot rset)
  (p_frame: i:a -> v:b i -> h0:mem -> r:HH.rid -> h1:mem ->
    Lemma (requires p v h0 /\ modifies_one r h0 h1 /\ ~(Set.mem r (footprint v)))
          (ensures p v h1))
  (r:HH.rid) (h0:mem) (h1:mem)
  : Lemma (requires mm_forall t p h0 /\ modifies_one r h0 h1 /\
            ~(Set.mem r (mm_fold t #rset Set.empty (fun s i k -> rset_union s (footprint k)))))
          (ensures mm_forall t p h1)
  = admit()

let lemma_mm_forall_extend (#a:eqtype) (#b:a -> Type) (t:MM.map' a b) (t':MM.map' a b)
  (p: #i:a -> b i -> mem -> GTot Type0) (i:a) (v:b i) (h0:mem) (h1:mem)
  : Lemma (requires mm_forall t p h1 /\ t' == MM.upd t i v /\ p v h1)
          (ensures mm_forall t' p h1)
  = admit()

let lemma_mm_forall_init (#a:eqtype) (#b:a -> Type) (t:MM.map' a b)
  (p: #i:a -> b i -> mem -> GTot Type0) (h:mem)
  : Lemma (requires t == MM.empty_map a b)
          (ensures mm_forall t p h)
  = admit()

let lemma_mm_forall_elim (#a:eqtype) (#b:a -> Type) (t:MM.map' a b)
  (p: #i:a -> b i -> mem -> GTot Type0) (i:a) (v:b i) (h:mem)
  : Lemma (requires mm_forall t p h /\ t i == Some v)
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

#set-options "--z3rlimit 100"
//unfold
let memoization (#ip:ipkg) (p:local_pkg ip) ($mtable: mem_table p.key): pkg ip =
  let footprint_extend (s:rset) (i:ip.t{ip.registered i}) (k:p.key i) =
    rset_union s (p.local_footprint k)
    in
  let footprint (h:mem): GTot rset =
    let instances_footprint =
      if model then
        let map = MR.m_sel h (itable mtable) in
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
      let map = MR.m_sel h0 (itable mtable) in
      let map' = MR.m_sel h1 (itable mtable) in
      let fp0 = footprint h0 in
      let fp1 = footprint h1 in
      mm_fold_grow map map' i k #rset Set.empty footprint_extend;
      assert(fp1 == rset_union p.shared_footprint (rset_union (mm_fold map #rset Set.empty footprint_extend) (p.local_footprint k)));
      lemma_union_com p.shared_footprint (mm_fold map #rset Set.empty footprint_extend) (p.local_footprint k);
      assert(fp1 == rset_union fp0 (p.local_footprint k));
      assert(forall (r:HH.rid). (Set.mem r fp1 /\ ~(Set.mem r fp0)) ==> Set.mem r (p.local_footprint k));
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
      mm_forall (MR.m_sel h log) p.local_invariant h))
    in
  let ls_footprint (#i:ip.t{ip.registered i}) (k:p.key i) =
    rset_union (p.local_footprint k) p.shared_footprint
    in
  let ls_footprint_frame (i:ip.t{ip.registered i}) (k:p.key i) (h0:mem) (r:HH.rid) (h1:mem)
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
      let map = MR.m_sel h0 (itable mtable) in
      assert(mm_forall map p.local_invariant h0);
      (match r with
      | Pinv_region r ->
        assert(modifies_one r h0 h1 /\ r `HH.disjoint` tls_define_region);
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
    MR.m_recall tbl;
    let k : p.key i = p.create i a in
    let h1 = get() in
    assert(MR.m_sel h0 tbl == MR.m_sel h1 tbl);
    package_invariant_framing h0 (Pinv_region tls_tables_region) h1;
    MM.extend tbl i k;
    let h2 = get () in
    lemma_define_tls_honest_regions (p.local_footprint k);
    p.post_framing #i a k h1 tls_define_region h2;
    lemma_mm_forall_frame (MR.m_sel h1 tbl) p.local_invariant ls_footprint ls_footprint_frame tls_define_region h1 h2;
    p.local_invariant_framing i k h1 tls_define_region h2;
    lemma_mm_forall_extend (MR.m_sel h1 tbl) (MR.m_sel h2 tbl) p.local_invariant i k h1 h2;
    assume(HS.modifies_ref tls_define_region (Set.singleton (mem_addr (itable mtable))) h0 h2); // How to prove?
    footprint_grow h0 i k h2;
    k in
  let coerce (i:ip.t{ip.registered i /\ (p.ideal ==> ~(ip.honest i))}) (a:p.info i) (k0:lbytes (p.len a))
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
      MR.m_recall tbl;
      let k : p.key i = p.coerce i a k0 in
      let h1 = get() in
      assert(MR.m_sel h0 tbl == MR.m_sel h1 tbl);
      package_invariant_framing h0 (Pinv_region tls_tables_region) h1;
      MM.extend tbl i k;
      let h2 = get () in
      lemma_define_tls_honest_regions (p.local_footprint k);
      p.post_framing #i a k h1 tls_define_region h2;
      lemma_mm_forall_frame (MR.m_sel h1 tbl) p.local_invariant ls_footprint ls_footprint_frame tls_define_region h1 h2;
      p.local_invariant_framing i k h1 tls_define_region h2;
      lemma_mm_forall_extend (MR.m_sel h1 tbl) (MR.m_sel h2 tbl) p.local_invariant i k h1 h2;
      assume(HS.modifies_ref tls_define_region (Set.singleton (mem_addr (itable mtable))) h0 h2); // How to prove?
      footprint_grow h0 i k h2;
      k
    ) else p.coerce i a k0
    in
  let post_framing (#i:ip.t{ip.registered i}) (a:p.info i) (k:p.key i)
    (h0:mem) (r:HH.rid) (h1:mem) : Lemma
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
  (if model then lemma_mm_forall_init (MR.m_sel h1 (itable mtable)) p.local_invariant h1);
  q

#reset-options

/// Next, we define a few sample functionalities,
/// parameterized on their abstract index package.
/// --------------------------------------------------------------------------------------------------
/// a default functionality (no interface, and no idealization);
/// for modelling, we could also provide a "leak" function

assume val flag_Raw: b:bool{b ==> model}
type idealRaw = b2t flag_Raw

type rawlen (#ip: ipkg) (#len_of_i: ip.t -> keylen) (i:ip.t) = len:keylen {len = len_of_i i}
type raw (ip: ipkg) (len_of_i: ip.t -> keylen) (i:ip.t{ip.registered i}) = lbytes (len_of_i i)

let shared_footprint_raw (ip: ipkg) (len_of_i: ip.t -> keylen)
  : rset = Set.empty

let footprint_raw (ip: ipkg) (len_of_i: ip.t -> keylen)
  (#i:ip.t {ip.registered i}) (k:raw ip len_of_i i)
  : GTot (s:rset{s `Set.disjoint` shared_footprint_raw ip len_of_i})
  =
  let fp = Set.empty in
  assume(fp `Set.disjoint` shared_footprint_raw ip len_of_i);
  fp

let create_raw (ip: ipkg) (len_of_i: ip.t -> keylen)
  (i:ip.t{ip.registered i}) (len:keylen {len = len_of_i i}):
  ST (raw ip len_of_i i)
  (requires fun h0 -> model)
  (ensures fun h0 p h1 -> modifies_none h0 h1)
  = sample len

let coerceT_raw (ip: ipkg) (len_of_i: ip.t -> keylen)
  (i: ip.t {ip.registered i /\ (idealRaw ==> ~(ip.honest i))})
  (len:keylen {len = len_of_i i}) (r:lbytes len):
  GTot (raw ip len_of_i i) = r

let coerce_raw (ip: ipkg) (len_of_i: ip.t -> keylen)
  (i: ip.t {ip.registered i /\ (idealRaw ==> ~(ip.honest i))})
  (len:keylen {len = len_of_i i}) (r:lbytes len):
  ST (raw ip len_of_i i)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> k == coerceT_raw ip len_of_i i len r /\ modifies_none h0 h1)
  = r

let local_raw_pkg (ip:ipkg) (len_of_i: ip.t -> keylen) : local_pkg ip =
  LocalPkg
    (raw ip len_of_i)
    (rawlen #ip #len_of_i)
    (fun #i (n:rawlen i) -> n)
    idealRaw
    (shared_footprint_raw ip len_of_i)
    (footprint_raw ip len_of_i)
    (fun #_ _ _ -> True) // no invariant
    (fun _ _ _ _ _ -> ())
    (fun #_ _ _ _ -> True) // no post-condition
    (fun #_ _ _ _ _ _ -> ())
    (create_raw ip len_of_i)
    (coerceT_raw ip len_of_i)
    (coerce_raw ip len_of_i)

let rp (ip:ipkg) (len_of_i: ip.t -> keylen): ST (pkg ip)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> modifies_one tls_define_region h0 h1 /\ p.package_invariant h1)
  =
  memoization_ST (local_raw_pkg ip len_of_i)

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

//17-11-22 TODO: generic wrapping of encrypt from local_invariant to package_invariant

/// TLS-SPECIFIC KEY SCHEDULE
/// --------------------------------------------------------------------------------------------------

/// module Id
///
/// We provide an instance of ipkg to track key derivation (here using constant labels)
/// these labels are specific to HKDF, for now strings e.g. "e exp master".
type label = string

/// the middle extraction takes an optional DH secret, identified by this triple
/// we use our own datatype to simplify typechecking
type id_dhe =
  | NoIDH
  | IDH:
    gX: CommonDH.dhi ->
    gY: CommonDH.dhr gX -> id_dhe

// The "ciphersuite hash algorithms" eligible for TLS 1.3 key derivation.
// We will be more restrictive.
type kdfa = Hashing.Spec.alg

/// Runtime key-derivation parameters, to be adjusted.
///
/// HKDF defines an injective function from label * context to bytes, to be used as KDF indexes.
///
type context =
  | Extract: context // TLS extractions have no label and no context; we may separate Extract0 and Extract2
  | ExtractDH: v:id_dhe -> context // This is Extract1 (the middle extraction)
  | Expand: context // TLS expansion with default hash value
  | ExpandLog: // TLS expansion using hash of the handshake log
    info: TLSInfo.logInfo (* ghost, abstract summary of the transcript *) ->
    hv: Hashing.Spec.anyTag (* requires stratification *) -> context

/// Underneath, HKDF takes a "context" and a required length, with
/// disjoint internal encodings of the context:
/// [HKDF.format #ha label digest len]

type id_psk = nat // external application PSKs only; we may also set the usage's maximal recursive depth here.
type pre_id =
  | Preshared:
      a: kdfa (* fixing the hash algorithm *) ->
      id_psk  ->
      pre_id
  | Derive:
      i:pre_id (* parent index *) ->
      l:label (* static part of the derivation label *) ->
      context (* dynamic part of the derivation label *) ->
      pre_id

// always bound by the index (and also passed concretely at creation-time).
val ha_of_id: i:pre_id -> kdfa
let rec ha_of_id = function
  | Preshared a _ -> a
  | Derive i lbl ctx -> ha_of_id i

// placeholders
assume val idh_of_log: TLSInfo.logInfo -> id_dhe
assume val summary: bytes -> TLSInfo.logInfo

// concrete transcript digest
let digest_info (a:kdfa) (info:TLSInfo.logInfo) (hv: Hashing.Spec.anyTag) =
  exists (transcript: bytes).
    // Bytes.length hv = tagLen a /\
    hv = Hashing.Spec.hash a transcript /\
    Hashing.CRF.hashed a transcript /\
    info = summary transcript

/// stratified definition of id required.
///
/// we will enforce
/// * consistency on the hash algorithm
/// * monotonicity of the log infos (recursively including earlier resumption logs).
/// * usage restriction: the log after DH must include the DH identifier of the parent.
///   (Hence, we should either forbid successive DHs or authenticate them all.)
///
val wellformed_id: pre_id -> Type0
let rec wellformed_id = function
  | Preshared a _ -> True
  | Derive i l (ExpandLog info hv) -> wellformed_id i /\ digest_info (ha_of_id i) info hv
  | Derive i lbl ctx ->
      //TODO "ctx either extends the parent's, or includes its idh" /\
      wellformed_id i

type id = i:pre_id {wellformed_id i}

type honest_idh (c:context) =
  ExtractDH? c /\ IDH? (ExtractDH?.v c) /\
  (let ExtractDH (IDH gX gY) = c in CommonDH.honest_dhr gY)

/// We use a global honesty table for all indexes Inside ipkg, we
/// assume all index types are defined in the table below We assume
/// write access to this table is public, but the following global
/// invariant must be enforced: if i is corrupt then all indexes
/// derived from i are also corrupt
/// ---EXCEPT if ctx is ExtractDH g gx gy with CommonDH.honest_dhr gy
///
type honesty_invariant (m:MM.map' id (fun _ -> bool)) =
  (forall (i:id) (l:label) (c:context{wellformed_id (Derive i l c)}).
  {:pattern (m (Derive i l c))}
  Some? (m (Derive i l c)) ==> Some? (m i) /\
  (m i = Some false ==> (honest_idh c \/ m (Derive i l c) = Some false)))

private type i_honesty_table =
  MM.t tls_honest_region id (fun (t:id) -> bool) honesty_invariant
private let h_table = if model then i_honesty_table else unit

let honesty_table: h_table =
  if model then
    MM.alloc #tls_honest_region #id #(fun _ -> bool) #honesty_invariant
  else ()

// Registered is monotonic
type registered (i:id) =
  (if model then
    let log : i_honesty_table = honesty_table in
    MR.witnessed (MM.defined log i)
  else True)

type regid = i:id{registered i}

type honest (i:id) =
  (if model then
    let log: i_honesty_table = honesty_table in
    MR.witnessed (MM.contains log i true)
  else False)

type corrupt (i:id) =
  (if model then
    let log : i_honesty_table = honesty_table in
    MR.witnessed (MM.contains log i false)
  else True)

// ADL: difficult to prove, relies on an axiom outside the current formalization of FStar.Monotonic
let lemma_honest_corrupt (i:regid)
  : Lemma (honest i <==> ~(corrupt i)) =
  admit()

let lemma_corrupt_invariant (i:regid) (lbl:label)
  (ctx:context {wellformed_id (Derive i lbl ctx) /\ registered (Derive i lbl ctx)})
  : ST unit
  (requires fun h0 -> ~(honest_idh ctx))
  (ensures fun h0 _ h1 ->
    corrupt i ==> corrupt (Derive i lbl ctx) /\ h0 == h1)
  =
  lemma_honest_corrupt i;
  lemma_honest_corrupt (Derive i lbl ctx);
  if model then
    let log : i_honesty_table = honesty_table in
    MR.m_recall log;
    MR.testify (MM.defined log i);
    match MM.lookup log i with
    | Some true -> ()
    | Some false ->
      let m = MR.m_read log in
      // No annotation, but the proof relies on the global log invariant
      MR.testify (MM.defined log (Derive i lbl ctx));
      MM.contains_stable log (Derive i lbl ctx) false;
      MR.witness log (MM.contains log (Derive i lbl ctx) false)
  else ()

let get_honesty (i:id {registered i}) : ST bool
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> h0 == h1 /\ (b <==> honest i))
  =
  lemma_honest_corrupt i;
  if model then
    let log : i_honesty_table = honesty_table in
    MR.m_recall log;
    MR.testify (MM.defined log i);
    match MM.lookup log i with
    | Some b -> b
  else false

// TODO(adl) preservation of the honesty table invariant
let rec lemma_honesty_update (m:MM.map id (fun _ -> bool) honesty_invariant)
  (i:regid) (l:label) (c:context{wellformed_id (Derive i l c)}) (b:bool{b <==> honest i})
  : Lemma (honesty_invariant (MM.upd m (Derive i l c) b))
// : Lemma (requires Some? (m i ) /\ None? (m (Derive i l c)) /\ m i == Some false ==> not b)
//         (ensures honesty_invariant (MM.upd m (Derive i l c) b))
  = admit() // easy

let register_derive (i:id{registered i}) (l:label) (c:context{wellformed_id (Derive i l c)})
  : ST (i:id{registered i} * bool)
  (requires fun h0 -> True)
  (ensures fun h0 (i', b) h1 ->
    (if model then modifies_one tls_honest_region h0 h1 else h0 == h1)
    /\ (i' == Derive i l c)
    /\ (b2t b <==> honest i'))
  =
  let i':id = Derive i l c in
  if model then
    let log : i_honesty_table = honesty_table in
    MR.m_recall log;
    match MM.lookup log i' with
    | Some b -> lemma_honest_corrupt i'; (i', b)
    | None ->
      let b = get_honesty i in
      let h = get () in
      lemma_honesty_update (MR.m_sel h log) i l c b;
      MM.extend log i' b;
      lemma_honest_corrupt i';
      (i', b)
  else (i', false)

// 17-10-21 WIDE/NARROW INDEXES (old)
//
// We'd rather keep wide indexes secret.  Internally, for each salt
// index, we maintain a table from (g, gX, gY) to PRFs, with some
// sharing.  (The sharing may be public, but not wide indexes values
// are not.)  Informally this is sound because our limited use of the
// tables does not depend on their sharing.
//
// The danger of overly precise indexes is that, ideally, we may
// separate instances that use the same concrete keys---in our case
// this does not matter because security does not depend on their
// sharing.

let ii: ipkg = // (#info:Type0) (get_info: id -> info) =
  Idx id registered honest get_honesty

/// Try out on examples: we may need a stateful invariant of the form
/// "I have used this secret to create exactly these keys".


/// We expect this function to be fully applied at compile time,
/// returning a package and a algorithm-derivation function to its
/// agility parameter (to be usually applied at run-time).
///

/// ADL: PROPOSED CHANGE (09/11/17)
/// ===================================================================================
/// We propose to encode the idealization order of packages inside the usage function
/// Namely, for all labels, the associated derived package can only be ideal if
/// its parent is ideal. This condition will be checked when the packages are created
/// (the packager must provide a flag that satisfies this condition), after the
/// derivation tree is fixed.
/// ===================================================================================
/// noeq type range (info: Type0) (lbl:label) (ideal: Type0) = | Use:
///     info': Type0 ->
///     get_info': (id -> info') ->
///     pkg': pkg info' (ii #info' get_info'){pkg'.ideal ==> ideal} ->
///     derive: (i: id -> a: info -> ctx: context {wellformed_id (Derive i lbl ctx)} -> a': info' {a' == get_info' (Derive i lbl ctx)}) ->
///     range info lbl
///
/// type usage (info: Type0) = (| ideal:Type0 & lbl: label -> (* compile-time *) range info lbl parent_ideal |)
/// ===================================================================================

(*
noeq type range (lbl:label) = | Use:
    info': Type0 ->
    get_info': (id -> info') ->
    pkg': pkg ii ->
    derive: (i: id -> ctx: context {wellformed_id (Derive i lbl ctx)} -> a': info' {a' == get_info' (Derive i lbl ctx)}) ->
    range lbl
*)

type old_usage = lbl: label -> pkg ii (* compile-time *)

// Initially, the info only consists of the hash algorithm, and it is
// invariant through extractions and derivations... until the first
// hashed transcript, at which point the

(*
/// parametricity? (Old/Later)
/// we have [#id #pd #u #i #a]
/// u v returns [#ip #p (derive_alg: pd.info -> p.info) (derive_index: id.t -> i.t)]
///
/// We finally use a global, recursive instantiation of indexes to
/// compose all our functionalities, with for instance
/// (fun i -> Derived i v) to get the derived index.

// (*UNUSED *) type usage' (#ii:ipkg) (a: ii.t -> Type0) =
//   label ->
//     ip:ipkg &
//     p: pkg ip &
//     derive_index: (ii.t -> ip.t) &
//     derive_info: (i: ii.t -> a i -> p.use (derive_index i))
// note that [a] is [d.use]
// should usage be part of info?
// what about state state (safety etc)?
*)


/// 17-11-29 experiment, using chidren as a replacement for usage.

type t = pkg ii

(* ADL: the following crashes F*
noeq type tree' (par_ideal:Type0) =
  | Leaf: package:t{Pkg?.ideal package ==> par_ideal} -> tree' par_ideal
  | Node: node:t{Pkg?.ideal node ==> par_ideal} -> children: children (Pkg?.ideal node) -> tree' par_ideal
and children (par_ideal:Type0) = list (label * tree' par_ideal)
*)

noeq type tree' =
  | Leaf: package:t -> tree'
  | Node: node:t -> children:children' -> tree'
and children' = list (label * tree')

// would prefer to use Map.t, but positivity check fails

let max x y = if x <= y then y else x

// induction on n-ary trees requires explicit termination
let rec depth (x:tree') : nat =
  match x with
  | Leaf _ -> 0
  | Node _ lxs -> 1 + children_depth lxs
and children_depth (lxs:children') : nat  =
  match lxs with
  | (_,x) :: lxs -> max (depth x) (children_depth lxs)
  | [] -> 0

let valid_child ideal_parent (p:t) = Pkg?.ideal p ==> ideal_parent
val valid_tree: ideal_parent:Type0 -> t:tree' -> Tot Type0 (decreases %[t; 0])
val valid_children: ideal_parent:Type0 -> c:children' -> Tot Type0 (decreases %[c; 1])

let rec valid_tree par = function
  | Leaf p -> valid_child par p
  | Node p c -> valid_child par p /\ valid_children (Pkg?.ideal p) c
and valid_children par = function
  | [] -> True
  | (_, t)::tl -> valid_tree par t /\ valid_children par tl

// p is a property implied by the ideal flags in all sub-packages
// at the root one may use e.g. model or True
type tree (p:Type0) = t:tree'{valid_tree p t}
type children (p:Type0) = c:children'{valid_children p c}

let rec find_lbl (#p:Type0) (u:children p) (l: label) : option (tree p) =
  match u with
  | [] -> None
  | (lbl, t) :: tl ->
    if lbl = l then Some t
    else
      let tl : children p = tl in
      find_lbl tl l

let has_lbl (#p:Type0) (u:children p) (l: label) = Some? (find_lbl u l)

let down (#p:Type0) (u:children p) (l:label{u `has_lbl` l}) : tree p
  = Some?.v (find_lbl u l)

let child (#p:Type0) (u:children p) (l:label{u `has_lbl` l})
  : pkg:t{Pkg?.ideal pkg ==> p}
  =
  match down u l  with
  | Leaf p -> p
  | Node p c -> p

/// --------------------------------------------------------------------------------------------------
/// module KDF
///
/// we define a KDF parametric in both its usage and ipkg
/// We rely on type abstraction to separate secrets with different indexes
/// For soundness, we must also prevent external calls to create derived secrets.
///
/// We idealize KDF as a random function, with lazy sampling.
/// This holds syntactically only after inlining all calls to
/// pkg.create/coerce.
///
/// This requires memoizing calls, which is a bit tricky when calling
/// stateful allocators.

assume val flag_KDF: d:nat -> b:bool{b ==> model}
type idealKDF d = b2t (flag_KDF d)
assume val lemma_KDF_depth: d:nat{idealKDF d} -> Lemma (forall (d':nat). d' <= d ==> idealKDF d)

// Note that when model is off, safeKDF is False and corruptKDF is True
type safeKDF (d:nat) (i:id{registered i}) = idealKDF d /\ honest i

// KDF-specific usage: the parent property is idealKDF at level d
type usage (d:nat) = children (idealKDF d)

type details (ha:kdfa) = | Log:
  loginfo: TLSInfo.logInfo ->
  hv: Hashing.Spec.anyTag {digest_info ha loginfo hv} -> details ha

type info = | Info:
  ha:kdfa ->
  option (details ha) -> info

val get_info: id -> info
// 17-11-01 can't get it to verify; should follow from the definition of wellformed_id?
//#set-options "--initial_ifuel 2 --initial_fuel 2"
let rec get_info (i0: id): info =
  match i0 with
  | Preshared a _                 -> Info a None
  | Derive i l (ExpandLog log hv) -> Info (ha_of_id i) (Some (Log log hv))
  | Derive i _ _                  -> get_info i

assume val hkdf_derive_label_spec:
  ha: Hashing.Spec.alg -> k: Hashing.Spec.tag ha -> lbl: label -> ctx:context -> GTot (Hashing.Spec.tag ha)

let derived_key
  (d: nat)
  (u: usage d)
  (i: regid)
  (lbl: label {u `has_lbl` lbl})
  (ctx: context {wellformed_id (Derive i lbl ctx) /\ registered (Derive i lbl ctx)})
  =
  (Pkg?.key (child u lbl)) (Derive i lbl ctx)

let kdf_tables_region : tls_rgn = new_region Mem.tls_tables_region

/// key-derivation table (memoizing create/coerce)
type domain (d:nat) (u:usage d) (i:id{registered i}) = | Domain:
  lbl: label {u `has_lbl` lbl} ->
  ctx: context {wellformed_id (Derive i lbl ctx) /\ registered (Derive i lbl ctx)} ->
  domain d u i

type kdf_range (de:nat) (u:usage de) (i:id{registered i}) (d:domain de u i) =
  (let Domain lbl ctx = d in derived_key de u i lbl ctx)

type ideal_or_real (it:Type0) (rt:Type0) =
  | Ideal: v:it -> ideal_or_real it rt
  | Real: v:rt -> ideal_or_real it rt

unfold type ir_key (safe: i:id{registered i} -> GTot Type0) (it:Type0) (rt:Type0) (i:regid) =
  (if model then
    s:ideal_or_real it rt{safe i <==> Ideal? s}
  else rt)

noeq private type table (d:nat) (u:usage d) (i:id{registered i}) =
  | KDF_table:
    r:subrgn kdf_tables_region ->
    t:MM.t r (domain d u i) (kdf_range d u i) (fun _ -> True) ->
    table d u i

let secret_len (a:info) : keylen = UInt32.uint_to_t (Hashing.Spec.tagLen a.ha)
type real_secret (i:id{registered i}) = lbytes (secret_len (get_info i))

// id vs regid?
type secret (d:nat) (u:usage d) (i:id{registered i}) =
  ir_key (safeKDF d) (table d u i) (real_secret i) i

// when to be parametric on ip? not for the KDF itself: we use ip's constructors.
//type secret (u: usage info) (i:regid) =
//  (if honest i then table u i
//  else lbytes (secret_len (get_info i)))

let secret_ideal (#d:nat) (#u: usage d) (#i:id{registered i}) (t: secret d u i {safeKDF d i}): table d u i =
  let t : s:ideal_or_real (table d u i) (real_secret i) {safeKDF d i <==> Ideal? s} = t in
  Ideal?.v t

let ideal_secret (#d:nat) (#u: usage d) (#i:id{registered i}) (t: table d u i {safeKDF d i}) : secret d u i =
  let t : s:ideal_or_real (table d u i) (real_secret i) {safeKDF d i <==> Ideal? s} = Ideal t in
  assert(model); t

let secret_corrupt (#d:nat) (#u: usage d) (#i:id{registered i}) (t: secret d u i {~(safeKDF d i)}): real_secret i =
  if model then
   let t : s:ideal_or_real (table d u i) (real_secret i) {safeKDF d i <==> Ideal? s} = t in
   Real?.v t
  else t

let corrupt_secret (#d:nat) (#u: usage d) (#i:id{registered i}) (t: real_secret i {~(safeKDF d i)}) : secret d u i =
  if model then
    let s : s:ideal_or_real (table d u i) (real_secret i) {safeKDF d i <==> Ideal? s} = Real t in s
  else t

/// Real KDF schemes, parameterized by an algorithm computed from the
/// index (existing code).

let lemma_honest_parent (i:id{registered i}) (lbl:label)
  (ctx:context {wellformed_id (Derive i lbl ctx) /\ registered (Derive i lbl ctx)})
  : Lemma (requires ~(honest_idh ctx)) (ensures honest (Derive i lbl ctx) ==> honest i)
  = admit() // hard, uses the monotonic excluded middle axiom and table invariant

// For KDF, we require that being fresh in the KDF table implies being fresh
// in the derived package's definition table
type local_kdf_invariant (#d:nat) (#u:usage d) (#i:id{registered i}) (k:secret d u i) (h:mem) =
  (forall (lbl:label {u `has_lbl` lbl}) (ctx':context).
    (~(honest_idh ctx') /\ wellformed_id (Derive i lbl ctx') /\ registered (Derive i lbl ctx')) ==>
      (let ctx : c:context{wellformed_id (Derive i lbl c) /\ registered (Derive i lbl c)} = ctx' in
      let i' : i:id{registered i} = Derive i lbl ctx in
      lemma_honest_parent i lbl ctx;
      let pkg' = child u lbl in
      // Nice: we get this from the tree structure for free!
      assert(Pkg?.ideal pkg' ==> idealKDF d);
      (if model then
        let dt = itable pkg'.define_table in
        let kdf : ir:ideal_or_real (table d u i) (real_secret i) {safeKDF d i <==> Ideal? ir} = k in
        // We need this for coerce
        assert(safeKDF d i <==> Ideal? kdf);
        match kdf with
        | Ideal kdft ->
          // the entries in the KDF table match those of the child's define_table
          let KDF_table r t : table d u i = kdft in
          MM.sel (MR.m_sel h t) (Domain lbl ctx) == MM.sel (MR.m_sel h dt) i'
        | Real raw ->
          assert(~(safeKDF d i));
          assert(honest i' ==> honest i);
          assert(Pkg?.ideal pkg' ==> ~(honest i')); // to call coerceT
          // the child's define table has correctly-computed coerced entries
          (match MM.sel (MR.m_sel h dt) i' with
          | None -> True
          | Some k' ->
            // we recompute the concrete key materials, and recall the
            // existence of some prior info, which (by specification
            // of coerceT) must yield exactly the same instance as the
            // one recorded earlier.
            let i'': i:id{registered i /\ (Pkg?.ideal pkg' ==> ~(honest i))} = i' in
            let raw' = hkdf_derive_label_spec (get_info i).ha raw lbl ctx in
            exists (a':Pkg?.info pkg' i').
            Pkg?.len pkg' a' == UInt32.uint_to_t (Hashing.Spec.tagLen (get_info i).ha) /\
            k' == Pkg?.coerceT pkg' i'' a' raw')
      else True)))

let kdf_shared_footprint (#d:nat) (u:usage d) : rset =
  assume false; Set.empty
  // List.Tot.fold_left (Set.empty) (fun s p -> rset_union s p.define_region) u

let kdf_footprint (#d:nat) (#u:usage d) (#i:id{registered i}) (k:secret d u i)
  : GTot (s:rset{s `Set.disjoint` kdf_shared_footprint u}) =
  assume false; // WIP(adl) Fix rset for define_region subrgn
  if model then
    let k : ideal_or_real (table d u i) (real_secret i) = k in
    match k with
    | Ideal (KDF_table r _) -> Set.singleton r
    | Real k -> Set.empty
  else Set.empty

let local_kdf_invariant_framing (#d:nat) (#u:usage d) (i:id{registered i}) (k:secret d u i) (h0:mem) (r:HH.rid) (h1:mem)
  : Lemma (requires local_kdf_invariant k h0 /\ modifies_one r h0 h1
            /\ ~(r `Set.mem` kdf_footprint k) /\ ~(r `Set.mem` kdf_shared_footprint u))
          (ensures local_kdf_invariant k h1)
  = admit()

/// maybe reverse-inline sampling from low-level KeyGen?
/// otherwise we have to argue it is what Create does.
///
/// MK: what does reverse-inline of low-level KeyGen mean?

// The post-condition of creating a KDF is that its table is empty
// This is useful to re-establish the multi-KDF invariant
type kdf_post (#d:nat) (#u:usage d) (#i:id{registered i}) (a: info {a == get_info i}) (k:secret d u i) (h:mem) =
  (safeKDF d i ==>
    (let KDF_table r t = secret_ideal k in
     MR.m_sel h t == MM.empty_map (domain d u i) (kdf_range d u i)))

// Framing for the kdf_post depends only on kdf_footprint k
let kdf_post_framing (#d:nat) (#u:usage d) (#i:id{registered i}) (a: info {a == get_info i})
  (k:secret d u i) (h0:mem) (r:HH.rid) (h1:mem)
  : Lemma (requires (kdf_post a k h0 /\ modifies_one r h0 h1 /\ ~(r `Set.mem` kdf_footprint k)))
          (ensures (kdf_post a k h1))
  = admit()

val coerceT:
  d: nat ->
  u: usage d ->
  i: id{registered i /\ ~(safeKDF d i)} ->
  a: info {a == get_info i} (* run-time *) ->
  repr: lbytes (secret_len a) ->
  GTot (secret d u i)
let coerceT d u i a repr =
  corrupt_secret #d #u #i repr

val coerce:
  d: nat ->
  u: usage d ->
  i: id{registered i /\ ~(safeKDF d i)} ->
  a: info {a == get_info i} (* run-time *) ->
  repr: lbytes (secret_len a) ->
  ST (secret d u i)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> modifies_none h0 h1
    /\ k == coerceT d u i a repr
    /\ fresh_regions (kdf_footprint k) h0 h1
    /\ kdf_post a k h1 /\ local_kdf_invariant k h1)

let coerce d u i a repr =
  let k = corrupt_secret #d #u #i repr in
  let h1 = get() in
  // WIP stronger packaging
  (if model then assume(local_kdf_invariant k h1));
  k

/// NS:
/// MM.alloc is a stateful function with all implicit arguments
/// F* will refuse to instantiate all those arguments, since implicit
/// instantiation in F* should never result in an effect.
///
/// Stateful functions always take at least 1 concrete argument.
///
/// I added a unit here
///
/// CF: Ok; I did not know. Is it a style bug in FStar.Monotonic.Map ?
let alloc #a #b #inv (r:FStar.Monotonic.RRef.rid)
  : ST (MM.t r a b inv)
       (requires (fun h -> inv (MM.empty_map a b)))
       (ensures (fun h0 x h1 ->
    inv (MM.empty_map a b) /\
    ralloc_post r (MM.empty_map a b) h0 (FStar.Monotonic.RRef.as_hsref x) h1))
  = MM.alloc #r #a #b #inv

val create:
  d: nat ->
  u: usage d ->
  i: id{registered i} -> // using regid yields unification failures below
  a: info {a == get_info i}(* run-time *) ->
  ST (secret d u i)
  (requires fun h0 -> model)
  (ensures fun h0 k h1 -> modifies_none h0 h1
    /\ fresh_regions (kdf_footprint k) h0 h1
    /\ kdf_post a k h1 /\ local_kdf_invariant k h1)

let create d u i a =
  let h0 = get() in
  let honest = get_honesty i in
  let h1 = get() in
  if flag_KDF d && honest then
   begin
    assert(safeKDF d i);
    let r : subrgn kdf_tables_region = new_region kdf_tables_region in
    let h2 = get() in
    assert(stronger_fresh_region r h1 h2);
    let t : table d u i = KDF_table r (alloc r) in
    let h3 = get() in
    let k : secret d u i = ideal_secret t in
    assume(kdf_footprint k == Set.singleton r);
    assume(local_kdf_invariant k h3);
    assert(fresh_regions (kdf_footprint k) h0 h3);
    k
   end
  else
   begin
    let k = corrupt_secret #d #u #i (sample (secret_len a)) in
    assume(local_kdf_invariant k h1); // TODO
    k
   end

/// We are using many KDF packages (one for each usage),
/// idealized one at a time.  (Having one proof step for each nested
/// level of key derivation seems unavoidable: we need to idealize
/// parents before childrens.)

let local_kdf_pkg (d:nat) (u:usage d) : local_pkg ii =
  (LocalPkg
    (secret d u)
    (fun i -> a:info{a == get_info i})
    (fun #_ a -> secret_len a)
    (idealKDF d)
    (kdf_shared_footprint u)
    (kdf_footprint #d #u)
    (local_kdf_invariant #d #u)
    (local_kdf_invariant_framing #d #u)
    (kdf_post #d #u)
    (kdf_post_framing #d #u)
    (create d u)
    (coerceT d u)
    (coerce d u))

let pp (d:nat) (u:usage d) : ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 ->
     modifies_mem_table p.define_table h0 h1 /\
     p.package_invariant h1)
  =
  memoization_ST #ii (local_kdf_pkg d u)

let ukey (d:nat) (u:usage d) (lbl:label {u `has_lbl` lbl}) (i:id{registered i}) =
  Pkg?.key (child u lbl) i

// Derive modifies:
//  - the honesty table
//  - the define table of the derived package
//  - the KDF table
// FIXME: can't use the normalizer to compute the set... destroys the implicit
type modifies_derive (#d:nat) (#u:usage d) (#i:id{registered i}) (k:secret d u i)
  (lbl:label {u `has_lbl` lbl}) (ctx:context {wellformed_id (Derive i lbl ctx)}) (h0:mem) (h1:mem) =
  (if model then
    let modset = Set.singleton tls_define_region in
    let modset = Set.union modset (Set.singleton tls_honest_region) in
    let k : ideal_or_real (table d u i) (real_secret i) = k in
    let modset = match k with
    | Ideal (KDF_table r _) -> Set.union modset (Set.singleton r)
    | Real k -> modset in
    let utable = (child u lbl).define_table in
    modifies modset h0 h1
    /\ HS.modifies_ref tls_define_region (Set.singleton (mem_addr (itable utable))) h0 h1
  else modifies_none h0 h1) // FIXME concrete state


//OLD
let all_pkg_invariant h = forall (p:pkg ii). p.package_invariant h

/// 17-11-30 experiment, testing package trees on a simple case: AEAD
/// keying and forward re-keying; still unclear how to traverse the
/// packaging.


/// Global, generic invariant, to be rooted at the PSK
/// (do we need some "static index"?)

// node footprints already recursively collect their children's footprints
let tree_footprint (x:tree') h : GTot rset =
  match x with
  | Leaf p -> Pkg?.footprint p h
  | Node p c -> Pkg?.footprint p h
// WIP: footprint_kdf includes the define tables of children, but not the package footprints
//    rset_union (Pkg?.footprint p h)
//      (List.Tot.fold_left (fun s p -> rset_union s (Pkg?.footprint p h)) c Set.empty)

// library??
val list_forall: ('a -> Type0) -> list 'a -> Tot Type0
let rec list_forall f l = match l with
    | [] -> True
    | hd::tl -> f hd /\ list_forall f tl

val disjoint_children: mem -> children' -> Type0
let rec disjoint_children h = function
  | [] -> True
  | (l0, x0) :: tail -> list_forall (fun (l1, x1) -> tree_footprint x0 h `Set.disjoint` tree_footprint x1 h) tail

(*
/// SZ: An alternative way of defining [tree_invariant] without an ad-hoc termination measure

val move_refinement: #a:Type -> #p:(a -> Type)
  -> l:list a{forall z. List.Tot.memP z l ==> p z} -> list (x:a{p x})
let rec move_refinement #a #p = function
  | [] -> []
  | hd :: tl -> hd :: move_refinement #a #p tl

val forall_memP_precedes: #a:Type -> l:list a -> Lemma (forall x. List.Tot.memP x l ==> x << l)
let forall_memP_precedes #a l =
  let open FStar.Tactics in
  let open FStar.List.Tot in
  assert_by_tactic (forall x. memP x l ==> x << l)
    (x <-- forall_intro; apply_lemma (quote memP_precedes))

val precedes_list: #a:Type -> l:list a -> list (x:a{x << l})
let precedes_list #a l = forall_memP_precedes l; move_refinement l

val tree_invariant: mem -> tree -> Type0
let rec tree_invariant h = function
  | Leaf p -> Pkg?.package_invariant p h
  | Node lxs p ->
    Pkg?.package_invariant p h /\
    list_forall (fun (p:(label * tree){p << lxs}) -> tree_invariant h (snd p)) (precedes_list lxs) /\
    disjoint_children h lxs
*)

// another custom induction to get termination
let rec children_forall
  (lxs: children')
  (f: x:tree'{depth x <= children_depth lxs} -> Type0): Type0
=
  match lxs with
  | [] -> True
  | (_,x)::tl ->
    // children_depth tl <= children_depth lxs /\
    // depth x <= children_depth lxs /\
    f x /\ children_forall tl f

let rec tree_invariant (x:tree') (h:mem): Tot Type0 (decreases %[depth x]) =
  match x with
  | Leaf p -> Pkg?.package_invariant p h
  | Node p lxs ->
    Pkg?.package_invariant p h /\
    children_forall lxs (fun x -> tree_invariant x h) /\
    disjoint_children h lxs

// We can frame the multi-pkg invariant for free when touching tls_honest_region
let tree_invariant_frame (t:tree') (h0:mem) (h1:mem)
  : Lemma (requires tree_invariant t h0 /\ (modifies_none h0 h1 \/ modifies_one tls_honest_region h0 h1))
          (ensures tree_invariant t h1)
  = admit()

// If we touch one package's footprint, but restore this package's invariant,
// the multi-package invariant is restored
let restore_all_pkg_invariant h0 (p:pkg ii) h1
  : Lemma (requires all_pkg_invariant h0 /\ modifies (p.footprint h0) h0 h1 /\ p.package_invariant h1)
          (ensures all_pkg_invariant h1)
  = admit()

// TODO 17-12-01 we need an hypothesis that captures that p is in the tree, e.g. only deal with the case where p is a child.

type kdf_subtree (d:nat) = t:tree model{Node? t /\
  (let Node p u = t in
  Pkg?.ideal p == idealKDF d /\
  Pkg?.key p == LocalPkg?.key (local_kdf_pkg d u) /\
  p == memoization (local_kdf_pkg d u) p.define_table)}

let u_of_t (#d:nat) (t:kdf_subtree d) : usage d = Node?.children t

/// The well-formedness condition on the derived label (opaque from
/// the viewpoint of the KDF) enforces
///
inline_for_extraction
val derive:
  #d: nat ->
  #t: kdf_subtree d ->
  #i: id{registered i} ->
  k: secret d (u_of_t t) i ->
  a: info {a == get_info i} ->
  lbl: label {(u_of_t t) `has_lbl` lbl} ->
  ctx: context {~(honest_idh ctx) /\ wellformed_id (Derive i lbl ctx)} ->
  a': Pkg?.info (child (u_of_t t) lbl) (Derive i lbl ctx) ->
  ST (_:unit{registered (Derive i lbl ctx)} & ukey d (u_of_t t) lbl (Derive i lbl ctx))
  // the second pre-condition is redundant, but we don't know the package of k
  (requires fun h0 -> tree_invariant t h0)
  (ensures fun h0 r h1 ->
    modifies_derive k lbl ctx h0 h1 /\
    tree_invariant t h1 /\
    (Pkg?.post (child (u_of_t t) lbl)) a' (dsnd r) h1)

let derive #d #t #i k a lbl ctx a' =
  let u = u_of_t t in
  let kdf_dt : mem_table (secret d u) = Pkg?.define_table (Node?.node t) in
  let h0 = get() in
  let honest = get_honesty i in
  let i', honest' = register_derive i lbl ctx in  // register (Derive i lbl ctx) and return its honesty
  let h1 = get() in
  // Frame the registration, only if model is one (otherwise h0 == h1)
  tree_invariant_frame t h0 h1;

  assume false; // WIP Dec 7

  // Deduce from tree_invariant that local_kdf_invariant k h1 holds
  if model then
   begin
    let log = itable kdf_dt in
    let m = MR.m_sel h1 log in
    assume(m i == Some k); // to add, mem_defined i k
    lemma_mm_forall_elim m local_kdf_invariant i k h1;
    assert(local_kdf_invariant k h1)
   end;

  lemma_corrupt_invariant i lbl ctx;
  let x: domain d u i = Domain lbl ctx in
  let pkg = child u lbl in
  assert(Pkg?.ideal pkg ==> idealKDF d); // Nice!

  if flag_KDF d && honest then
   begin
    let KDF_table kdf_r kdf_t : table d u i = secret_ideal k in
    let v: option (derived_key d u i lbl ctx) = MM.lookup kdf_t x in
    match v with
    //17-10-30 was failing with scrutiny error: match MM.lookup (secret_ideal k) x
    | Some dk -> (| (), dk |)
    | None ->
      let dk = Pkg?.create pkg i' a' in
      let h2 = get() in
      assume(tree_invariant t h2);
      assert(mem_fresh pkg.define_table i' h2); // from kdf_local_inv
      MM.extend kdf_t x dk;
      (| (), dk |)
   end
  else
   begin
    let raw = HKDF.expand #(a.ha) (secret_corrupt k) (Platform.Bytes.abytes lbl) (UInt32.v (Pkg?.len pkg a')) in
    let h2 = get() in
    assume(modifies_none h1 h2); // FIXME HKDF framing
    assume(tree_invariant t h2);
    assert(Pkg?.ideal pkg ==> corrupt i');
    let dk = Pkg?.coerce pkg i' a' raw in
    // FIXME
    (| (), dk |)
   end

// OLD (17-12-01 to be deleted)
/// Outlining a global KDF state invariant, supported by package
/// definition tables for all derivable functionalities.
///
/// for all (i: id) (lbl) (ctx).
///   let i' = Derive lbl ctx in
///   wellformed_id i' ==>
///   let u = u_of_i i in
///   let pkg',... = u lbl in
///   match KDF.lookup i with
///   | None -> None? pkg'.lookup i' // used when creating PRFs
///   | Some k -> pkg'.lookup i' == lookup k (Domain lbl ctx) // used when extending PRFs.
///
/// The invariant is restored by the time derive return.
/// (note we implicitly rely on u_of_i)




/// We now resume with a more specific invariant, modelling
/// post-handshake key management.  (we will have other specific
/// applications).

//17-11-15 for testing; rename to aeadAlg_of_id ?
assume val get_aeadAlg: i:id -> aeadAlg
let derive_aea
  (lbl:label) (i:id)
  (a:info{wellformed_id (Derive i lbl Expand)}):
  (a':aeadAlg{a' == get_aeadAlg (Derive i lbl Expand)})
=
  //fixme! should be extracted from a
  get_aeadAlg (Derive i lbl Expand)


let memoized (p:pkg ii) (l:local_pkg ii) =
  exists (t: mem_table l.key). p == memoization l t
  // a more specific spec, saving a quantifier but stuck on subtyping:
  // let t: mem_table l.key = p.define_table in
  // p == memoization l t

let is_ae_p (p: pkg ii)           = memoized p (local_ae_pkg ii get_aeadAlg)
let is_kdf_p (p: pkg ii) children = memoized p (local_kdf_pkg children)

// this function should specify enough to call key derivations.
let rec is_secret (n:nat) (x: tree) =
  if n = 0 then
    match x with
    | Node [] p -> is_kdf_p p []
    | _ -> False
  else
    match x with
    | Node ["AE",Leaf ae; "RE",re ] p ->
      is_kdf_p p ["AE",Leaf ae; "RE",re ] /\
      is_ae_p ae /\
      is_secret (n-1) re
    | _ -> False

// let is_secret_shape (n:nat) (x:tree {is_secret n x}): Lemma (Node? x) =
//   if n = 0 then () else ()


assume val mk_kdf: u:children -> ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> is_kdf_p p u)

// this function allocates all tables and (WIP) sets up the initial invariant.
val mk_secret (n:nat): ST tree
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    is_secret n x /\
    True // tree_invariant x h1 // requires finer posts for mp pp etc
    )
let rec mk_secret n =
  if n = 0 then
    let p = mk_kdf [] in
    Node [] p
  else (
    let ae = mp ii get_aeadAlg in
    assume(is_ae_p ae);// should be in the post of mp.
    let re = mk_secret (n-1) in
    assert(is_secret (n-1) re);
    let children = [ "AE",Leaf ae; "RE",re ] in
    let p = mk_kdf children in
    assert(is_kdf_p p [ "AE",Leaf ae; "RE",re ]);
    Node children p )

//#set-options "--z3rlimit 100 --detail_errors"
let test_rekey(): St unit
=
  let x0 = mk_secret 10 in
  let h0 = get() in
  assert(is_secret 10 x0);
  assume(tree_invariant x0 h0); // soon a post of mk_secret
  // assert(Node? x0);
  match x0 with
  | Node ["AE",Leaf aepkg1; "RE",x1 ] pkg0 -> (
    let children0 = ["AE",Leaf aepkg1; "RE",x1 ] in
    let a0 = Info Hashing.Spec.SHA1 None in
    let i0: i:id {registered i /\ a0 = get_info i} = magic() in
    assert(is_kdf_p pkg0 children0);
    assert(pkg0.package_invariant h0 /\ tree_invariant x1 h0);
    // create's pre; should follow from pkg0's package invariant
    assume(model /\ mem_fresh pkg0.define_table i0 h0);
    assert(Pkg?.key pkg0 == secret children0);

    let s0: secret children0 i0 = (Pkg?.create pkg0) i0 a0 in
    assert(is_secret 9 x1);
    match x1 with
    | Node ["AE",Leaf aepkg2; "RE",x2] pkg1  -> (
      let children1 = ["AE",Leaf aepkg2; "RE",x2 ] in
      let a1 = Info Hashing.Spec.SHA1 None in
      let h1 = get() in
      assume(tree_invariant x0 h0 ==> tree_invariant x0 h1); //TODO framing of create
      assume(all_pkg_invariant h1 /\ local_kdf_invariant s0 h1);

      let (|_,s1|) = derive s0 a0 "RE" Expand a1 in
      let i1: regid = Derive i0 "RE" Expand in
      let s1: secret children1 i1 = s1 in
      let aea = derive_aea "AE" i1 a1 in
      let h2 = get() in
      // derive's abusive pre; will follow from multi-pkg invariant
      assume(all_pkg_invariant h2 /\ local_kdf_invariant s1 h2);

      let (|_,k1|) = derive s1 a1 "AE" Expand aea in
      let ik1: regid = Derive i1 "AE" Expand in
      let k1: key ii get_aeadAlg ik1 = k1 in
      let h3 = get() in
      assume(aead_inv k1 h3); // should follow from the multi-pkg invariant

      let cipher = encrypt ii get_aeadAlg #ik1 k1 42 in

      // assert(tree_invariant x1);
      // assert(tree_invariant x0);
      () ))
//    | _ -> assert false) // excluded by is_secret 9
//  |  _ -> assert false // excluded by is_secret 10
// refactoring needed, e.g. define derive_secret helper function to hide access to the tree



(* --- 
(*
let modifies_instance
  (i: id {wellformed_id i})
  (p: localpkg ii)
  (k: key i)
  (h0 h1: mem)
  (modifies_local: modifies (p.local_footprint k) h0 h1)
  (inv0: inv_node u h0):
  Lemma (inv_node u h1) =

let rec step u j i =

// from the post of a key derivation, we should have our framing lemma.

let rec descend u j i = // j decreases
  j = i \/
  match j with
  | Derive j0 lbl ctx -> derived j0 i
  | Preshared -> False

  match j, i with
  | Preshared

  i = j \/
  exists (lbl, ctx). derived (Derive i lbl ctx)
*)



/// --------------------------------------------------------------------------------------------------
/// PSKs, Salt, and Extraction (can we be more parametric?)

assume val flag_KEF0: b:bool{b ==> model /\ flag_KDF ==> b}
type idealKEF0 = b2t flag_KEF0
assume val lemma_kdf_kef0: unit -> Lemma (idealKDF ==> idealKEF0)

let safeKEF0 (i:regid) = idealKEF0 /\ honest i
let corruptKEF0 (i:regid) = idealKEF0 ==> corrupt i

/// key-derivation table (memoizing create/coerce)

val ssa: #a:Type0 -> Preorder.preorder (option a)
let ssa #a =
  let f x y =
    match x,y with
    | None, _  -> True
    | Some v, Some v' -> v == v'
    | _ -> False in
  f

// temporary
let there = Mem.tls_tables_region

// memoizing a single extracted secret
private type mref_secret (u: usage) (i: regid) =
  // would prefer: HyperStack.mref (option (secret u i)) (ssa #(secret u i))
  MR.m_rref there (option (secret u i)) ssa

/// covering two cases: application PSK and resumption PSK
/// (the distinction follow from the value of i)
type psk (u: usage) (i: (Idx?.t ii) {ii.registered i}) =
  ir_key safeKEF0 (mref_secret u i) (real_secret i) i

let psk_ideal (#u: usage) (#i:regid) (p:psk u i {safeKEF0 i}): mref_secret u i =
  let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF0 i <==> Ideal? s} = p in
  Ideal?.v t

let ideal_psk (#u: usage) (#i:regid) (t: mref_secret u i{safeKEF0 i}) : psk u i =
  let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF0 i <==> Ideal? s} = Ideal t in
  assert(model); t

let psk_real (#u: usage) (#i:regid) (p:psk u i {corruptKEF0 i}): real_secret i =
  lemma_honest_corrupt i;
  if model then
    let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF0 i <==> Ideal? s} = p in
    Real?.v t
  else p

let real_psk (#u: usage) (#i:regid) (t: real_secret i{corruptKEF0 i}) : psk u i =
  if model then
    (lemma_honest_corrupt i;
    let s : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF0 i <==> Ideal? s} = Real t in s)
  else t

type ext0 (u:usage) (i:regid) =
  _:unit{registered (Derive i "" Extract)} & psk u (Derive i "" Extract)

val coerce_psk:
  #u: usage ->
  i: regid ->
  a: info {a == get_info i} ->
  raw: lbytes (secret_len a) ->
  ST (ext0 u i)
  (requires fun h0 -> idealKEF0 ==> corrupt i)
  (ensures fun h0 p h1 -> (*TBC*) True)

let coerce_psk #u i a raw =
  let i', honest' = register_derive i "" Extract in
  lemma_corrupt_invariant i "" Extract;
  (| (), real_psk #u #i' raw |)

val create_psk:
  #u: usage ->
  i: ii.t {ii.registered i} ->
  a: info {a == get_info i} ->
  ST (ext0 u i)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> (*TBC*) True)
let create_psk #u i a =
  let i', honest' = register_derive i "" Extract in
  lemma_corrupt_invariant i "" Extract;
  if flag_KEF0 && honest' then
    let t' = secret u i' in
    let r: mref_secret u i' = MR.m_alloc #(option t') #(ssa #t') there None in
    (| (), ideal_psk #u #i' r |)
  else
    (| (), real_psk #u #i' (sample (secret_len a)) |)

let pskp (*ip:ipkg*) (u:usage): ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> (*TBC*) True)
=
  let p =
    LocalPkg
      (fun (i:ii.t {ii.registered i}) -> ext0 u i)
      (fun i -> a: info{a == get_info i})
      (fun #_ a -> secret_len a)
      idealKEF0
      // local footprint
      (fun #i (k:ext0 u i) -> Set.empty (*TBC*))
      // local invariant
      (fun #_ k h -> True)
      (fun r i h0 k h1 -> ())
      // create/coerce postcondition
      (fun #i u h0 k h1 -> True) //TODO
      (fun #i u h0 k h1 r h2 -> ())
      create_psk
      coerce_psk in
  memoization_ST p

/// HKDF.Extract(key=0, materials=k) idealized as a (single-use) PRF,
/// possibly customized on the distribution of k.
val extract0:
  #u: usage ->
  #i: regid ->
  k: ext0 u i ->
  a: info {a == get_info i} ->
  ST
    (secret u (Derive i "" Extract))
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> (*TBC*) True)

let extract0 #u #i k a =
  let (| _, p |) = k in
  let i':regid = Derive i "" Extract in
  let honest' = get_honesty i' in
  lemma_kdf_kef0 (); // idealKDF ==> idealKEF0
  if flag_KEF0 && honest'
  then
    let k: mref_secret u i' = psk_ideal p in
    match MR.m_read k with
    | Some extract -> extract
    | None ->
      let extract = create u i' a in
      let mrel = ssa #(secret u i') in
      let () =
        MR.m_recall k;
        let h = get() in
        assume (MR.m_sel h k == None); // TODO framing of call to create
        assume (mrel None (Some extract)); // TODO Fix the monotonic relation
        MR.m_write k (Some extract) in
      extract
  else
    let k = psk_real p in
    let raw = HKDF.extract #(a.ha) (Hashing.zeroHash a.ha) k in
    coerce u i' a raw

/// The "salt" is an optional secret used (exclusively) as HKDF
/// extraction key. The absence of salt (e.g. when no PSK is used) is
/// handled using a special, constant salt marked as compromised.
///
/// salt is indexed by the usage of the secret that will be extracted
/// (the usage of the salt itself is fixed).
///
/// We use separate code for salt1 and salt2 because they are
/// separately idealized (salt1 is more complicated)

assume val flag_PRF1: b:bool{flag_KDF ==> b /\ b ==> model /\ flag_KEF0 ==> b}
let idealPRF1 = b2t flag_PRF1
let lemma_kdf_prf1 (): Lemma (idealKDF ==> idealPRF1) = admit()

type safePRF1 (i:regid) = idealPRF1 /\ honest i
type corruptPRF1 (i:regid) = idealPRF1 ==> corrupt i

assume type salt (u: usage) (i: id)

assume val create_salt:
  #u: usage ->
  i: id ->
  a: info ->
  salt u i

assume val coerce_salt:
  #u: usage ->
  i: id ->
  a: info ->
  raw: lbytes (secret_len a) ->
  salt u i

let saltp (*ip:ipkg*) (u:usage): ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> True)
=
  let p = LocalPkg
    (salt u)
    (fun (i:ii.t) -> a:info{a == get_info i})
    (fun #_ a -> secret_len a)
    idealPRF1
    // local footprint
    (fun #i (k:salt u i) -> Set.empty)
    // local invariant
    (fun #_ k h -> True)
    (fun r i h0 k h1 -> ())
    // create/coerce postcondition
    (fun #i u h0 k h1 -> True)
    (fun #i u h0 k h1 r h2 -> ())
    create_salt
    coerce_salt in
  memoization_ST #ii p


/// HKDF.Extract(key=s, materials=dh_secret) idealized as 2-step
/// (KEF-ODH, KEF-Salt game); we will need separate calls for clients
/// and servers.

/// two flags; we will idealize ODH first
assume val flag_ODH: b:bool { (flag_PRF1 ==> b) /\ (b ==> model)}
type idealODH = b2t flag_ODH

type safeODH (i:regid) = idealODH /\ honest i
type corruptODH (i:regid) = idealODH ==> corrupt i

/// we write prf_ for the middle salt-keyed extraction, conditionally
/// idealized as a PRF keyed by salt1 depending on flag_prf1
///
/// its interface provides create, coerce, leak, and extract its
/// internal table memoizes it either with *wide* domain gZ, or with
/// *narrow* domain idh
///
/// Returns a narrow-indexed key,
///
/// its internal state ensures sharing
///
assume val prf_leak:
  #u: usage ->
  #i: regid ->
  #a: info {a == get_info i} ->
  s: salt u i {idealPRF1 ==> corrupt i} ->
  Hashing.Spec.hkey a.ha

type ext1 (u:usage) (i:regid) (idh:id_dhe) =
  _:unit{registered (Derive i "" (ExtractDH idh))} &
  secret u (Derive i "" (ExtractDH idh))

val prf_extract1:
  #u: usage ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt u i ->
  idh: id_dhe{~(honest_idh (ExtractDH idh))} ->
  gZ: bytes ->
  ST (ext1 u i idh)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> True)

let prf_extract1 #u #i a s idh gZ =
  let j, honest' = register_derive i "" (ExtractDH idh) in
  lemma_corrupt_invariant i "" (ExtractDH idh);
  let honest = get_honesty i in
  lemma_kdf_prf1 ();
  if flag_PRF1 && honest
  then
    // This is the narrow idealized variant--see paper for additional
    // discussion. Note the algorithm is determined by the salt index.
    //
    (| (), create u j a |)
    //
    // We use the define table of the derived KDF to represent the
    // state of the PRF.  todo: guard [create] with a table lookup;
    // informally, when calling [prf_extract1] we don't care about the
    // state of the KDF, as long as it meets its invariant.
    //
    // The wide idealized variant is as follows:
    //
    // let j0 =
    //   match Map.find !s.wide (i,gZ) with
    //   | Some j0 -> j0
    //   | None    -> s.wide := !s.wide ++ ((i,gZ), length !s.wide) in
    // JKDF.create u j j0 a
    //
    // or just
    // JKDF.create u j (i,gZ) a
  else
    let raw_salt = prf_leak #u #i #a s in
    let raw = HKDF.extract raw_salt gZ in
    (| (), coerce u j a raw |)
    // we allocate a key at a narrow index, possibly re-using key
    // materials if there are collisions on gZ or raw_salt


/// ODH (precisely tracking the games)
/// --------------------------------------------------------------------------------------------------

// Ideally, we maintain a monotonic map from every honestly-sampled
// initiator share gX to its set of honestly-sampled responders shares
// (i,gY).
// The table exists when [Flags.ideal_KDF], a precondition for [flag_odh]

// We need a variant of FStar.Monotonic.Map that enables monotonic updates to
// each entry. We used nested ones to re-use existing libraries, but
// may instead invest is a custom library.
//
// how to share the u and a parameters? intuitively, u is statically
// fixed for everyone, and a is determined by the index i.

//17-10-30 unclear how to fix the usage at packaging-time.  This
// should be entirely static. Intuitively, there is a function from
// indexes to usage. Probably definable with the actual usage (big
// mutual reduction?)
assume val u_of_i: i:id -> usage

type odhid = x:CommonDH.dhi{CommonDH.registered_dhi x}

type peer_index (x:odhid) =
  i:regid & y:CommonDH.dhr x {CommonDH.registered_dhr y /\ registered (Derive i "" (ExtractDH (IDH x y)))}

type peer_instance (#x:odhid) (iy:peer_index x) =
  secret (u_of_i (dfst iy)) (Derive (dfst iy) "" (ExtractDH (IDH x (dsnd iy))))

let peer_table (x:odhid): Type0 =
  MM.t there (peer_index x) (peer_instance #x) (fun _ -> True)
type odh_table = MM.t there odhid peer_table (fun _ -> True)

let odh_state : (if model then odh_table else unit) =
  if model then MM.alloc #there #odhid #peer_table #(fun _ -> True)
  else ()

type odh_fresh (i:odhid) (h:mem) =
  (if model then
    let log : odh_table = odh_state in
    MM.fresh log i h
  else True)

let lemma_fresh_odh (i:CommonDH.dhi) (h:mem)
  : Lemma (CommonDH.fresh_dhi i h ==> odh_fresh i h)
  = admit () // i:dhi implies registered_dhi i and registered_dhi i /\ fresh_dhi i h ==> False

let lemma_fresh_odh_framing (i:CommonDH.dhi) (h0:mem) (h1:mem)
  : Lemma (odh_fresh i h0 /\ modifies_one CommonDH.dh_region h0 h1 ==> odh_fresh i h1)
  = admit() // assume(HH.disjoint there CommonDH.dh_region)

type odh_defined (i:odhid) =
  (if model then
    let log : odh_table = odh_state in
    MR.witnessed (MM.defined log i)
  else True)

type odhr_fresh (#i:odhid) (r:peer_index i) (h:mem) =
  (if model then
    let log : odh_table = odh_state in
    (match MM.sel (MR.m_sel h log) i with
    | Some t ->
      (match MM.sel (MR.m_sel h t) r with
      | None -> True
      | _ -> False)
    | _ -> False)
  else True)

let lemma_fresh_dhr (#i:odhid) (r:peer_index i) (h:mem)
  : Lemma (CommonDH.fresh_dhr (dsnd r) h ==> odhr_fresh r h)
  = admit () // contradition on  CommonDH.registered_dhr y

let lemma_fresh_dhr_framing (#i:odhid) (r:peer_index i) (h0:mem) (h1:mem)
  : Lemma (odhr_fresh r h0 /\ modifies (Set.union (Set.singleton CommonDH.dh_region) (Set.singleton tls_honest_region)) h0 h1 ==> odhr_fresh r h1)
  = admit() // assume(HH.disjoint there CommonDH.dh_region)

/// Client-side instance creation
/// (possibly used by many honest servers)
val odh_init: g: CommonDH.group -> ST (CommonDH.ikeyshare g)
  (requires fun h0 -> True)
  (ensures fun h0 x h1 ->
    let gx : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    modifies (Set.union (Set.singleton CommonDH.dh_region) (Set.singleton there)) h0 h1
    /\ model ==> (odh_fresh gx h0 /\ odh_defined gx /\ CommonDH.honest_dhi gx))

let odh_init g =
  let h0 = get () in
  let x = CommonDH.keygen g in
  let h1 = get () in
  if model then
   begin
    let log : odh_table = odh_state in
    let i : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    lemma_fresh_odh i h0;
    lemma_fresh_odh_framing i h0 h1;
    assert(MM.sel (MR.m_sel h1 log) i == None);
    let peers = alloc() <: peer_table i in //17-11-22   MM.alloc #there #(peer_index i) #(peer_instance #i) #(fun _ -> True) in
    let h2 = get () in
    assume(MM.sel (MR.m_sel h2 log) i == None); // FIXME allocate peers somewhere else !!
    MM.extend log i peers;
    assume(MR.stable_on_t log (MM.defined log i));
    MR.witness log (MM.defined log i)
   end;
  x

// TODO crypto agility: do we record keygen as honest for a bad group?

/// Server-side creation and completion
///
/// An elaboration of "derive" for two-secret extraction
/// - kdf is the child KDF package.
/// - HKDF is the concrete algorithm
///
/// We require that gX be the share of a honest initiator,
/// but not that they agree on the salt index

private let register_odh (i:regid) (gX:CommonDH.dhi) (gY:CommonDH.dhr gX)
  : ST (j:regid{j == Derive i "" (ExtractDH (IDH gX gY))})
  (requires fun h0 -> model /\ CommonDH.honest_dhr gY)
  (ensures fun h0 _ h1 -> modifies_one tls_honest_region h0 h1)
  =
  let idh = IDH gX gY in
  let ctx = ExtractDH idh in
  assert(honest_idh ctx);
  let j = Derive i "" ctx in // N.B. this is the only case where i can be corrupt and j honest
  let hlog : i_honesty_table = honesty_table in
  MR.m_recall hlog;
  match MM.lookup hlog j with
  | None ->
    let m = MR.m_read hlog in
    assume(honesty_invariant (MM.upd m j true)); // Sepcial case: honest IDH
    MM.extend hlog j true;
    MM.contains_stable hlog j true;
    MR.witness hlog (MM.contains hlog j true); j
  | Some b -> j

val odh_test:
  #u: usage ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt u i ->
  gX: odhid{odh_defined gX} ->
  ST (j:peer_index gX{dfst j == i} & peer_instance j)
  (requires fun h0 -> model /\ CommonDH.honest_dhi gX)
  (ensures fun h0 r h1 ->
    // todo, as sanity check
    // let (|gY, s|) = dfst r in
    // flag_odh ==> s == peer_gX gY
    True)

let odh_test #u #i a s gX =
  assume (u == u_of_i i); //17-11-01 TODO modelling
  (* we get the same code as in the game by unfolding dh_responder, e.g.
  let y = CommonDH.keygen g in
  let gY = CommonDH.pubshare y in
  let gZ: bytes (*CommonDH.share g*) = ... in  // used only when (not flag_odh)
  *)
  let h0 = get() in
  let gY, gZ = CommonDH.dh_responder (dfst gX) (dsnd gX) in
  let j = register_odh i gX gY in
  let j' : peer_index gX = (| i, gY |) in
  let h1 = get() in
  lemma_fresh_dhr j' h0;
  lemma_fresh_dhr_framing j' h0 h1;
  assert(odhr_fresh j' h1);
  assert(a == get_info j);
  let k: secret u j =
    if flag_ODH then create u j a (* narrow *)
    else (
      assert(~idealPRF1);
      let raw = HKDF.extract #a.ha (prf_leak s) gZ (* wide, concrete *) in
      assume(~idealKDF); // FIXME(adl): fix the loop in the flag order dependency. See definition of usage for proposed solution
      coerce u j a raw
    ) in
  let h2 = get() in
  assume(odhr_fresh j' h2); // TODO framing of KDF
  let t: odh_table = odh_state in
  MR.testify(MM.defined t gX);
  let peers = Some?.v (MM.lookup t gX) in
  MM.extend peers j' k;
  (| j' , k |)

unfold let idh_of (#g:CommonDH.group) (x:CommonDH.ikeyshare g) (gY:CommonDH.rshare g (CommonDH.ipubshare x)) =
  IDH (| g, CommonDH.ipubshare x |) gY

// the PRF-ODH oracle, computing with secret exponent x
val odh_prf:
  #u: usage ->
  #i: regid ->
  a: info {a == get_info i}->
  s: salt u i ->
  g: CommonDH.group ->
  x: CommonDH.ikeyshare g ->
  gY: CommonDH.rshare g (CommonDH.ipubshare x) ->
  ST (_:unit{registered (Derive i "" (ExtractDH (idh_of x gY)))} & secret u (Derive i "" (ExtractDH (idh_of x gY))))
  (requires fun h0 ->
    let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    CommonDH.honest_dhi gX /\ odh_defined gX
    /\ (model ==> (CommonDH.fresh_dhr #gX gY h0)))
  (ensures fun h0 _ h1 -> True)

// FIXME. Lemma is false. Not sure how to fix
let lemma_fresh_dhr_hinv (#x:CommonDH.dhi) (y:CommonDH.dhr x) (h:mem)
  : Lemma (requires (model ==> CommonDH.fresh_dhr #x y h))
          (ensures ~(honest_idh (ExtractDH (IDH x y))))
  = admit()

let odh_prf #u #i a s g x gY =
  let h = get () in
  let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
  let idh = IDH gX gY in
  assert_norm(idh == idh_of x gY);
  lemma_fresh_dhr_hinv #gX gY h;
  let gZ = CommonDH.dh_initiator g x gY in
  let (| uu, k |) = prf_extract1 #u #i a s idh gZ in
  let k' : secret u (Derive i "" (ExtractDH idh)) = k in
  (| (), k' |)


/// --------------------------------------------------------------------------------------------------
/// Diffie-Hellman shares
/// module Extract1, or KEF.ODH

// TODO: instead of CommonDH.keyshare g, we need an abstract stateful
// [abstract type private_keyshare g = mref bool ...] that enables
// calling it exactly once

/// Initiator computes DH keyshare, irrespective of the KDF & salt.
let initI (g:CommonDH.group) = odh_init g

/// Responder computes DH secret material
val extractR:
  #u: usage ->
  #i: regid ->
  s: salt u i ->
  a: info {a == get_info i} ->
  gX: odhid ->
  ST (i_gY: peer_index gX{dfst i_gY == i} & peer_instance i_gY)
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)

let extractR #u #i s a gX =
  let b = if model then CommonDH.is_honest_dhi gX else false in
  if b then
   begin
    let t: odh_table = odh_state in
    (if None? (MM.lookup t gX) then
      let peers = MM.alloc #there #(peer_index gX) #(peer_instance #gX) #(fun _ -> True) in
      let h = get() in
      assume(None? (MM.sel (MR.m_sel h t) gX));
      MM.extend t gX peers;
      assume(MR.stable_on_t t (MM.defined t gX));
      MR.witness t (MM.defined t gX));
    odh_test a s gX
   end
  else
   begin
    // real computation: gY is honestly-generated but the exchange is doomed
    let gY, gZ = CommonDH.dh_responder (dfst gX) (dsnd gX) in
    let idh = IDH gX gY in
    assume(~(honest_idh (ExtractDH idh))); // FIXME
    let (| _ , k |) : ext1 u i idh = prf_extract1 a s idh gZ in
    let k : secret u (Derive i "" (ExtractDH idh)) = k in
    let i_gY : peer_index gX = (| i, gY |) in
    let s : peer_instance #gX i_gY = admit() in
    (| i_gY, s |)
   end

(*)
     let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
     CommonDH.honest_dhi gX /\ odh_defined gX
     /\ (model ==> (CommonDH.fresh_dhr #gX gY h0)))
*)

/// Initiator computes DH secret material
val extractI:
  #u: usage ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt u i ->
  g: CommonDH.group ->
  x: CommonDH.ikeyshare g ->
  gY: CommonDH.rshare g (CommonDH.ipubshare x) ->
  ST(_:unit{registered (Derive i "" (ExtractDH (idh_of x gY)))} & secret u (Derive i "" (ExtractDH (idh_of x gY))))
  (requires fun h0 ->
    let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
    CommonDH.honest_dhi gX /\ odh_defined gX)
  (ensures fun h0 k h1 -> True)

let extractI #u #i a s g x gY =
  let gX: CommonDH.dhi = (| g, CommonDH.ipubshare x |) in
  let b = if model then CommonDH.is_honest_dhi gX else false in
  if b then
    let t: odh_table = odh_state in
    MR.testify(MM.defined t gX);
    let peers = Some?.v (MM.lookup t gX) in
    let idh = IDH gX gY in
    let i' = Derive i "" (ExtractDH idh) in
    assume(registered i');
    assert(wellformed_id i);
    assume(wellformed_id i'); //17-11-01 same as above?
    let i_gY : peer_index gX = (| i, gY |) in
    let ot = secret u i' in
    assume (u == u_of_i i); //17-11-01 indexing does not cover u yet
    let o : option ot = MM.lookup peers i_gY in
    match o with
    | Some k -> (| (), k |)
    | None -> assume false; //17-11-22 why?
           odh_prf #u #i a s g x gY
  else odh_prf #u #i a s g x gY

val extractP:
  #u:usage ->
  #i: regid ->
  a: info {a == get_info i} ->
  s: salt u i ->
  ST(_:unit{registered (Derive i "" (ExtractDH NoIDH))} & secret u (Derive i "" (ExtractDH NoIDH)))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> True)
let extractP #u #i a s =
  let gZ = Hashing.Spec.zeroHash a.ha in
   let (| _, k |) = prf_extract1 a s NoIDH gZ in
   assert(registered (Derive i "" (ExtractDH NoIDH)));
   let k : secret u (Derive i "" (ExtractDH NoIDH)) = k in
   (| (), k |)

assume val flag_KEF2: b:bool{flag_KDF ==> b}
type idealKEF2 = b2t flag_KEF2

type safeKEF2 i = idealKEF2 /\ honest i
type corruptKEF2 i = idealKEF2 ==> corrupt i

/// ---------------- final (useless) extraction --------------------
///
type salt2 (u: usage) (i:regid) =
  ir_key safeKEF2 (mref_secret u i) (real_secret i) i

// same code as for PSKs; but extract0 and extract2 differ concretely

let real_salt2 (#u: usage) (#i:regid) (t: real_secret i{corruptKEF2 i}) : salt2 u i =
  if model then
    (lemma_honest_corrupt i;
    let s : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF2 i <==> Ideal? s} = Real t in s)
  else t

let salt2_real (#u: usage) (#i:regid) (p:salt2 u i {corruptKEF2 i}): real_secret i =
  lemma_honest_corrupt i;
  if model then
    let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF2 i <==> Ideal? s} = p in
    Real?.v t
  else p

type ext2 (u: usage) (i: ii.t {ii.registered i}) =
  _:unit{registered (Derive i "" Extract)} & salt2 u (Derive i "" Extract)

val coerce_salt2:
  #u: usage ->
  i: ii.t {ii.registered i} -> // using regid yields unification failures below
  a: info {a == get_info i} ->
  raw: lbytes (secret_len a) ->
  ST (ext2 u i)
  (requires fun h0 -> idealKEF2 ==> corrupt i)
  (ensures fun h0 p h1 -> (*TBC*) True)

let coerce_salt2 #u i a raw =
  let i', honest' = register_derive i "" Extract in
  lemma_corrupt_invariant i "" Extract;
  (| (), real_salt2 #u #i' raw |)

let ideal_salt2 (#u: usage) (#i:regid) (t: mref_secret u i{safeKEF2 i}) : salt2 u i =
  let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF2 i <==> Ideal? s} = Ideal t in
  assert(model); t

let salt2_ideal (#u: usage) (#i:regid) (p:salt2 u i {safeKEF2 i}): mref_secret u i =
  let t : s:ideal_or_real (mref_secret u i) (real_secret i) {safeKEF2 i <==> Ideal? s} = p in
  Ideal?.v t

val create_salt2:
  #u: usage ->
  i: ii.t {ii.registered i} -> // using regid yields unification failures below
  a: info {a == get_info i} ->
  ST (ext2 u i)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> (*TBC*) True)

let create_salt2 #u i a =
  let i', honest' = register_derive i "" Extract in
  let honest = get_honesty i in
  lemma_corrupt_invariant i "" Extract;
  if flag_KEF2 && honest' then
    let t' = secret u i' in
    let r: mref_secret u i' = MR.m_alloc #(option t') #(ssa #t') there None in
    (| (), ideal_salt2 #u #i' r |)
  else
    (| (), real_salt2 #u #i' (sample (secret_len a)) |)

let saltp2 (u:usage): ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> True)
=
  let p = LocalPkg
    (ext2 u)
    (fun (i:ii.t) -> a:info{a == get_info i})
    (fun #_ a -> secret_len a)
    idealKEF2
    // local footprint
    (fun #i (k:ext2 u i) -> Set.empty)
    // local invariant
    (fun #_ k h -> True)
    (fun r i h0 k h1 -> ())
    // create/coerce postcondition
    (fun #i u h0 k h1 -> True)
    (fun #i u h0 k h1 r h2 -> ())
    create_salt2
    coerce_salt2 in
  memoization_ST #ii p


/// HKDF.Extract(key=s, materials=0) idealized as a single-use PRF.
/// The salt is used just for extraction, hence [u] here is for the extractee.
/// Otherwise the code is similar to [derive], with different concrete details
val extract2:
  #u: usage ->
  #i: regid ->
  s: ext2 u i ->
  a: info {a == get_info i} ->
  ST (secret u (Derive i "" Extract))
    (requires fun h0 -> True)
    (ensures fun h0 p h1 -> (*TBC*) True)

let extract2 #u #i e2 a =
  let (| _, s |) = e2 in
  let i' : regid = Derive i "" Extract in
  let honest' = get_honesty i' in
  assert(wellformed_id i');
  assert(a = get_info i');
  assume(idealKDF ==> idealKEF2); // TODO
  if flag_KEF2 && honest' then
    let k: mref_secret u i' = salt2_ideal s in
    match MR.m_read k with
    | Some extract -> extract
    | None ->
        let extract = create u i' a in
        let mrel = ssa #(secret u i') in
        let () =
          MR.m_recall k;
          let h = get() in
          assume (MR.m_sel h k == None); // TODO framing of call to create
          assume (mrel None (Some extract)); // TODO Fix the monotonic relation
          MR.m_write k (Some extract) in
        extract
  else
    let k = salt2_real s in
    let raw = HKDF.extract #(a.ha) (Hashing.zeroHash a.ha) k in
    coerce u i' a raw



// not sure how to enforce label restrictions, e.g.
// val u_traffic: s:string { s = "ClientKey" \/ s = "ServerKey"} -> ip:ipkg -> pkg ip

let some_keylen: keylen = 32ul
let get_keylen (i:id) = some_keylen

inline_for_extraction
let u_default: usage = fun lbl -> rp ii get_keylen

//17-11-15 rename to aeadAlg_of_id ?
assume val get_aeadAlg: i:id -> aeadAlg
let derive_aea
  (lbl:label) (i:id)
  (a:info{wellformed_id (Derive i lbl Expand)}):
  (a':aeadAlg{a' == get_aeadAlg (Derive i lbl Expand)})
=
  //fixme! should be extracted from a
  get_aeadAlg (Derive i lbl Expand)

inline_for_extraction
let u_traffic: usage =
  fun (lbl:label) ->
  match lbl with
  | "ClientKey" | "ServerKey" -> mp ii get_aeadAlg
  | _ -> u_default lbl

// #set-options "--detail_errors"
// #set-options "--print_universes --print_implicits"

let derive_info (lbl:label) (i:id) (a:info) (ctx:context{wellformed_id (Derive i lbl ctx)}): a': info {a' == get_info (Derive i lbl ctx)}
=
  let Info ha o = a in
  assume false; //17-11-02 lemma needed?
  match ctx with
  | ExpandLog log hv -> Info ha (Some (Log log hv))
  | _ -> Info ha o

let labels = list label

(*
let psk_tables depth = ...
let pskp n u =
  memoization (local_pskp n u) psk_tables.[n]
  *)

// 17-10-20 this causes an extraction-time loop, as could be expected.
inline_for_extraction
let rec u_master_secret (n:nat ): Tot usage (decreases (%[n; 0])) =
  fun lbl -> match lbl with
  | "traffic"    -> pp u_traffic
  | "resumption" -> if n > 0
                   then pskp (u_early_secret (n-1))
                   else u_default lbl
  | _            -> u_default lbl
and u_handshake_secret (n:nat): Tot usage (decreases (%[n; 1])) =
  fun lbl -> match lbl with
  | "traffic"    -> pp u_traffic
  | "salt"       -> saltp2 (u_master_secret n)
  | _            -> u_default lbl
and u_early_secret (n:nat): Tot usage (decreases (%[n;2])) =
  fun lbl -> match lbl with
  | "traffic"    -> pp u_traffic
  | "salt"       -> saltp (u_handshake_secret n)
  | _            -> u_default lbl
/// Tot required... can we live with this integer indexing?
/// One cheap trick is to store a PSK only when it enables resumption.

//17-11-16 these functions suffice to implement `i_to_u`, but
// - this may be too late to be useful
// - this feel like writing twice the same code... refactor?

let rec f_master_secret (n:nat) (labels: list label): Tot usage (decreases (%[n; 0])) =
  match labels with
  | [] -> u_master_secret n
  | lbl :: labels ->
    match lbl with
    | "traffic" -> u_traffic
    | "resumption" ->
      if n > 0 then f_early_secret (n-1) labels else u_default
    | _ -> u_default
and f_handshake_secret (n:nat) (labels: list label): Tot usage (decreases (%[n; 1])) =
  match labels with
  | [] -> u_handshake_secret n
  | lbl :: labels ->
    match lbl with
    | "traffic" -> u_traffic
    | "salt" -> f_master_secret n labels
    | _ -> u_default
and f_early_secret (n:nat) (labels: list label): Tot usage (decreases (%[n;2])) =
  match labels with
  | [] -> u_early_secret n
  | lbl :: labels ->
    match lbl with
    | "traffic" -> u_traffic
    | "salt" -> f_handshake_secret n labels
    | _ -> u_default

let _: unit =
  assert(f_master_secret 3 ["resumption";"salt"] == u_handshake_secret 2)




(* not necessary?

We can write a List.fold on sequences of labels that yields the derived u.

u returns a package (not the next u)
we have a (partial, recursive) function from u to u'

type shape = |
  | Preshared0: nat
  | Derive0: shape -> label -> shape

type secret (ui: id -> usage info) (i: id)
type secret (u: usage info) (ul: label -> usage info) (i: id)

let pp (#s: shape) (u: usage s info): pkg info (ii get_info) = Pkg
  (secret s u)
  secret_len
  (create s u)
  (coerce s u)

val u_of_i: id -> usage info

/// We replay the key derivation (in reverse constructor order)
let rec u_of_i i = match i with
  | Preshared _ _ -> u_early_secret 1
  | Derive i lbl _ ->
       let u = u_of_i i in
       let (| info', get_info', pkg', _ |) = u lbl in
*)

/// Usability? A mock-up of the TLS 1.3 key schedule.
///
/// Although the usage computes everything at each derivation, each
/// still requires 3 type annotations to go through... Can we improve
/// it?
//NS: Not sure what sort of improvement you're aiming for
//    Can you sketch what you would like to write instead?
//    And why you would expect it to work?
// CF: The comment is out of date: this sample code is simpler than
// one week ago. Still, I would prefer not to have to write the
// intermediate indexes, which are all computable from the usage in
// the caller context and not necessarily useful for the caller.

// Testing normalization works for a parametric depth
assume val depth:  n:nat {n > 1}
let u: usage = u_early_secret depth

let gen_pskid a : St (n:nat{registered (Preshared a n)}) = admit()

val ks: unit -> St unit
let ks() =
  let pskctr = gen_pskid Hashing.Spec.SHA1 in
  let ipsk: regid = Preshared Hashing.Spec.SHA1 pskctr in
  let a = Info Hashing.Spec.SHA1 None in

  let psk0 : ext0 u ipsk = create_psk ipsk a in
  let i0 : regid = Derive ipsk "" Extract in
  let early_secret : secret u i0 = extract0 psk0 a in

  let (| _, et |) = derive early_secret a "traffic" Expand a in
  let i_traffic0 : regid = Derive i0 "traffic" Expand in
  let a_traffic0 = Info Hashing.Spec.SHA1 None in
  let early_traffic : secret u_traffic i_traffic0 = et in

  let aea_0rtt = derive_aea "ClientKey" i_traffic0 a in
  let (| _, ae0 |) = derive early_traffic a "ClientKey" Expand aea_0rtt in
  let i_0rtt : regid = Derive i_traffic0 "ClientKey" Expand in
  let k0: key ii get_aeadAlg i_0rtt = ae0 in
  let cipher  = encrypt k0 10 in

  let (| _, s1 |) = derive early_secret a "salt" Expand a in
  let i_salt1: regid = Derive i0 "salt" Expand in
  let salt1: salt (u_handshake_secret depth) i_salt1 = s1 in

  let g = CommonDH.default_group in
  let x = initI g in
  let gX : CommonDH.dhi = (| g, CommonDH.ipubshare x |) in

  let (| i_gY, hs1 |) = extractR salt1 a gX in
  let (| _, gY |) = i_gY in
  let i1 : regid = Derive i_salt1 "" (ExtractDH (IDH gX gY)) in

  // FIXME(adl) This requires a proof that u_of_i (dfst i_gY) == u_handshake_secret depth
  //assume(peer_instance i_gY == secret (u_handshake_secret depth) i1);
  let hs_secret: secret (u_handshake_secret depth) i1 = admit() in

  let (| _, hst |) = derive hs_secret a "traffic" Expand a in
  let i_traffic1: regid = Derive i1 "traffic" Expand  in
  let hs_traffic: secret u_traffic i_traffic1 = hst in

  let aea_1rtt = derive_aea "ServerKey" i_traffic1 a in
  let (| _, ae1 |) = derive hs_traffic a "ServerKey" Expand aea_1rtt in
  let i_1rtt : regid = Derive i_traffic1 "ServerKey" Expand in
  let k1: key ii get_aeadAlg i_1rtt = ae1 in

  let cipher  = encrypt k1 11 in

  let (| _, s2 |) = derive hs_secret a "salt" Expand a in
  let i_salt2: regid = Derive i1 "salt" Expand in
  let salt2 : salt2 (u_master_secret depth) i_salt2 = s2 in

  let i2 : regid = Derive i_salt2 "" Extract in
  let master_secret: secret (u_master_secret depth) i2 = extract2 #(u_master_secret depth) #i_salt2 salt2 a in
  let i3: regid = Derive i2 "resumption" Expand in

  let rsk: ext0 (u_early_secret (depth - 1)) i3 = derive master_secret a "resumption" Expand a in
  let i4: regid = Derive i3 "" Extract in
  let next_early_secret: secret (u_early_secret (depth - 1)) i4 = extract0 rsk a in
  ()
--- *)
