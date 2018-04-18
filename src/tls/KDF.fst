module KDF

/// We define a KDF parametric in both its usage and ipkg
/// We rely on type abstraction to separate secrets with different indexes
/// For soundness, we must also prevent external calls to create derived secrets.
///
/// We idealize KDF as a random function, with lazy sampling.
/// This holds syntactically only after inlining all calls to
/// pkg.create/coerce.
///
/// This requires memoizing calls, which is a bit tricky when calling
/// stateful allocators.

open Mem
open Pkg
open Idx 
open Pkg.Tree

module MDM = FStar.Monotonic.DependentMap
module HS = FStar.HyperStack

let sample (len:UInt32.t): ST (lbytes32 len)
    (requires fun h0 -> True)
    (ensures fun h0 r h1 -> h0 == h1)
  = CoreCrypto.random (UInt32.v len)



assume val flag_KDF: d:nat -> b:bool{b ==> model}
type idealKDF d = b2t (flag_KDF d)
assume val lemma_KDF_depth: d:nat{d>0} -> Lemma (idealKDF d ==> idealKDF (d-1))

// Note that when model is off, safeKDF is False
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

unfold type ir_key (safe: (i:id{registered i} -> GTot Type0)) (it:Type0) (rt:Type0) (i:regid) =
  (if model then
    s:ideal_or_real it rt{safe i <==> Ideal? s}
  else rt)

noeq private type table (d:nat) (u:usage d) (i:id{registered i}) =
  | KDF_table:
    r:subrgn kdf_tables_region ->
    t:MDM.t r (domain d u i) (kdf_range d u i) (fun _ -> True) ->
    table d u i

let secret_len (a:info) : keylen = Hashing.Spec.tagLen a.ha
type real_secret (i:id{registered i}) = lbytes32 (secret_len (get_info i))

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
          MDM.sel (sel h t) (Domain lbl ctx) == MDM.sel (sel h dt) i'
        | Real raw ->
          assert(~(safeKDF d i));
          assert(honest i' ==> honest i);
          assert(Pkg?.ideal pkg' ==> ~(honest i')); // to call coerceT
          // the child's define table has correctly-computed coerced entries
          (match MDM.sel (sel h dt) i' with
          | None -> True
          | Some k' ->
            // we recompute the concrete key materials, and recall the
            // existence of some prior info, which (by specification
            // of coerceT) must yield exactly the same instance as the
            // one recorded earlier.
            let i'': i:id{registered i /\ (Pkg?.ideal pkg' ==> ~(honest i))} = i' in
            let raw' = hkdf_derive_label_spec (get_info i).ha raw lbl ctx in
            exists (a':Pkg?.info pkg' i').
            Pkg?.len pkg' a' == Hashing.Spec.tagLen (get_info i).ha /\
            k' == Pkg?.coerceT pkg' i'' a' raw')
      else True)))

noextract
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

let local_kdf_invariant_framing (#d:nat) (#u:usage d) (i:id{registered i}) (k:secret d u i) (h0:mem) (r:rid) (h1:mem)
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
     sel h t == MDM.empty #(domain d u i) #(kdf_range d u i)))

// Framing for the kdf_post depends only on kdf_footprint k
let kdf_post_framing (#d:nat) (#u:usage d) (#i:id{registered i}) (a: info {a == get_info i})
  (k:secret d u i) (h0:mem) (r:rid) (h1:mem)
  : Lemma (requires (kdf_post a k h0 /\ modifies_one r h0 h1 /\ ~(r `Set.mem` kdf_footprint k)))
          (ensures (kdf_post a k h1))
  = admit()

val coerceT:
  d: nat ->
  u: usage d ->
  i: id{registered i /\ ~(safeKDF d i)} ->
  a: info {a == get_info i} (* run-time *) ->
  repr: lbytes32 (secret_len a) ->
  GTot (secret d u i)
let coerceT d u i a repr =
  corrupt_secret #d #u #i repr

val coerce:
  d: nat ->
  u: usage d ->
  i: id{registered i /\ ~(safeKDF d i)} ->
  a: info {a == get_info i} (* run-time *) ->
  repr: lbytes32 (secret_len a) ->
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
/// MDM.alloc is a stateful function with all implicit arguments
/// F* will refuse to instantiate all those arguments, since implicit
/// instantiation in F* should never result in an effect.
///
/// Stateful functions always take at least 1 concrete argument.
///
/// I added a unit here
///
/// CF: Ok; I did not know. Is it a style bug in FStar.Monotonic.Map ? 
#reset-options "--admit_smt_queries true"
let alloc #a #b #inv (r: erid): 
  ST (MDM.t r a b inv)
    (requires (fun h -> 
      inv (MDM.empty_partial_dependent_map #a #b) /\ 
      witnessed (region_contains_pred r) ))
    (ensures (fun h0 x h1 ->
      inv (MDM.empty_partial_dependent_map #a #b) /\
      ralloc_post r (MDM.empty #a #b) h0 x h1))
  = MDM.alloc #a #b #inv #r ()
#reset-options

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

#reset-options "--admit_smt_queries true"
let create d u i a =
  let h0 = get() in
  let honest = get_honesty i in
  let h1 = get() in
  if flag_KDF d && honest then
   begin
    assert(safeKDF d i);
    let r : subrgn kdf_tables_region = new_region kdf_tables_region in
    let h2 = get() in
    assert(Mem.fresh_region r h1 h2);
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
#reset-options

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
  (f: (x:tree'{depth x <= children_depth lxs} -> Type0)): Type0
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

type kdf_subtree (d:nat) = t:tree (idealKDF d){
  Node? t /\ (let Node p u = t in
  Pkg?.ideal p == idealKDF d /\
  Pkg?.key p == LocalPkg?.key (local_kdf_pkg d u) /\
  p == memoization (local_kdf_pkg d u) p.define_table)}

let u_of_t (#d:nat) (t:kdf_subtree d) : usage d = Node?.children t
let kdf_dt (#d:nat) (t:kdf_subtree d) : mem_table (secret d (u_of_t t)) = Pkg?.define_table (Node?.node t)

/// The well-formedness condition on the derived label (opaque from
/// the viewpoint of the KDF) enforces
///
noextract
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
  (requires fun h0 ->
    mem_defined (kdf_dt t) i /\ // Need a witness that k is defined to get local_kdf_invariant
    tree_invariant t h0)
  (ensures fun h0 r h1 ->
    modifies_derive k lbl ctx h0 h1 /\
    tree_invariant t h1 /\
    (Pkg?.post (child (u_of_t t) lbl)) a' (dsnd r) h1)

noextract
let derive #d #t #i k a lbl ctx a' =
  let u = u_of_t t in
  let dt = kdf_dt t in

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
    let log = itable dt in
    recall log;
    let m = sel h1 log in
    assume(MDM.sel m i == Some k); // testify
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
    let v: option (derived_key d u i lbl ctx) = MDM.lookup kdf_t x in
    match v with
    //17-10-30 was failing with scrutiny error: match MDM.lookup (secret_ideal k) x
    | Some dk -> (| (), dk |)
    | None ->
      let dk = Pkg?.create pkg i' a' in
      let h2 = get() in
      assume(tree_invariant t h2);
      assert(mem_fresh pkg.define_table i' h2); // from kdf_local_inv
      MDM.extend kdf_t x dk;
      (| (), dk |)
   end
  else
   begin
    let raw = HKDF.expand #(a.ha) (secret_corrupt k) (FStar.Bytes.bytes_of_string lbl) (Pkg?.len pkg a') in
    let h2 = get() in
    assume(modifies_none h1 h2); // FIXME HKDF framing
    assume(tree_invariant t h2);
    assert(Pkg?.ideal pkg ==> corrupt i');
    let dk = Pkg?.coerce pkg i' a' raw in
    (| (), dk |)
   end
