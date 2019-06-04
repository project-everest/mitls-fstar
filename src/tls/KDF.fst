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

inline_for_extraction
let sample (len:UInt32.t): ST (lbytes32 len)
    (requires fun h0 -> True)
    (ensures fun h0 r h1 -> h0 == h1)
  = assume false; Random.sample32 len

type details (ha:kdfa) =
| Log:
  loginfo: TLSInfo.logInfo ->
  hv: Hashing.Spec.anyTag {digest_info ha loginfo hv} -> details ha

type info =
| Info:
  ha:kdfa ->
  option (details ha) -> info

noextract
let rec index_info (i:id{model}) =
  let i':pre_id = i in
  match i' with
  | Preshared a _ -> Info a None
  | Derive i l (ExpandLog log hv) -> Info (ha_of_id i) (Some (Log log hv))
  | Derive i _ _ -> index_info i

let valid_info (i0:id) (v:info) =
  if model then v == index_info i0 else True

type info0 (i:id) = u:info{valid_info i u}
type iflag = b:bool{b ==> model}
type usage (ideal:iflag) = children (b2t ideal)

unfold type regid = i:(Idx?.t ii){(Idx?.registered ii) i}

let derived_key
  (#ideal:iflag)
  (u: usage ideal)
  (i: regid)
  (lbl: label {u `has_lbl` lbl})
  (ctx: context)
  : Pure Type0
  (requires wellformed_derive i lbl ctx /\
    registered (derive i lbl ctx) /\ model)
//    (model ==> Pkg?.key (child u lbl) == ktype))
  (ensures fun t -> True)
  =
  Pkg?.key (child u lbl) (Derive i lbl ctx)
//  (Pkg?.key (child u lbl)) (Derive i lbl ctx)

let kdf_tables_region : tls_rgn = new_region Mem.tls_tables_region

/// key-derivation table (memoizing create/coerce)
noextract
type domain (#ideal:iflag) (u:usage ideal) (i:regid) : eqtype =
| Domain:
  lbl: label {u `has_lbl` lbl} ->
  ctx: context {wellformed_derive i lbl ctx /\ registered (derive i lbl ctx)} ->
  domain u i

noextract
let kdf_range (#ideal:iflag) (u:usage ideal) (i:regid{model}) (d:domain u i) =
  (let Domain lbl ctx = d in derived_key u i lbl ctx)

noextract
noeq private type table (#ideal:iflag) (u:usage ideal) (i:regid) (s:squash model) =
  | KDF_table:
    r:subrgn kdf_tables_region ->
    t:MDM.t r (domain u i) (kdf_range u i) (fun _ -> True) ->
    table u i s

inline_for_extraction
let secret_len (a:info) : keylen = Hacl.Hash.Definitions.hash_len a.ha
type real_secret (i:regid) = a:info0 i & lbytes32 (secret_len a)

let safe (#ideal:iflag) (u:usage ideal) (i:regid) =
  honest i /\ b2t ideal

type secret (#ideal:iflag) (u:usage ideal) (i:regid) =
  Model.ir (safe u) (table u i) (real_secret i) i

/// Real KDF schemes, parameterized by an algorithm computed from the
/// index (existing code).

let lemma_honest_parent (i:regid) (lbl:label) (ctx:context)
  : Lemma (requires wellformed_derive i lbl ctx /\ registered (derive i lbl ctx) /\ ~(honest_idh ctx))
  (ensures honest (derive i lbl ctx) ==> honest i)
  = admit() // hard, uses the monotonic excluded middle axiom and table invariant

inline_for_extraction
let get_info (#ideal:iflag) (#u:usage ideal) (#i:regid) (k:secret u i) =
  if Model.is_safe k then index_info i
  else dfst (Model.real k)

// For KDF, we require that being fresh in the KDF table implies being fresh
// in the derived package's definition table
#set-options "--z3rlimit 30"
type local_kdf_invariant (#ideal:iflag) (#u:usage ideal) (#i:regid) (k:secret u i) (h:mem) =
  (forall (lbl:label {u `has_lbl` lbl}) (ctx':context).
    (~(honest_idh ctx') /\ wellformed_derive i lbl ctx' /\ registered (derive i lbl ctx')) ==>
    (if model then
      let ctx : c:context{wellformed_derive i lbl c /\ registered (derive i lbl c)} = ctx' in
      let i' : regid = derive i lbl ctx in
      lemma_honest_parent i lbl ctx;
      let pkg' = child u lbl in
      // Nice: we get this from the tree structure for free!
      assert(Pkg?.ideal pkg' ==> b2t ideal);
      let dt = itable pkg'.define_table in
      match Model.is_safe k with
      | true ->
        // the entries in the KDF table match those of the child's define_table
        let KDF_table r t : table u i () = Model.ideal k () in
        MDM.sel (sel h t) (Domain lbl ctx) == MDM.sel (sel h dt) i'
      | false ->
        let (| a, raw |) = Model.real k in
        assert(~(safe u i));
        assert(honest i' ==> honest i);
        assert(Pkg?.ideal pkg' ==> ~(honest i')); // to call coerceT
        // the child's define table has correctly-computed coerced entries
        (match MDM.sel (sel h dt) i' with
        | None -> True
        | Some k' -> exists (a': (Pkg?.info pkg') i').
          // we recompute the concrete key materials, and recall the
          // existence of some prior info, which (by specification
          // of coerceT) must yield exactly the same instance as the
          // one recorded earlier.
          let i'': i:regid{Pkg?.ideal pkg' ==> ~(honest i)} = i' in
	  let len' = Pkg?.len pkg' a' in
          let lb = FStar.Bytes.bytes_of_string lbl in
          let raw' = HKDF.expand_spec #a.ha raw lb len' in
          k' == Pkg?.coerceT pkg' i'' a' raw')
    else True))
#reset-options

noextract
let kdf_shared_footprint (#ideal:iflag) (u:usage ideal) : rset =
  assume false; Set.empty
  // List.Tot.fold_left (Set.empty) (fun s p -> rset_union s p.define_region) u

let kdf_footprint (#ideal:iflag) (#u:usage ideal) (#i:regid) (k:secret u i)
  : GTot (s:rset{s `Set.disjoint` kdf_shared_footprint u}) =
  assume false; // WIP(adl) Fix rset for define_region subrgn
  if Model.is_safe k then
    let KDF_table r _ = Model.ideal k () in
    Set.singleton r
  else Set.empty

let local_kdf_invariant_framing (#ideal:iflag) (#u:usage ideal) (i:regid) (k:secret u i) (h0:mem) (r:rid) (h1:mem)
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
type kdf_post (#ideal:iflag) (#u:usage ideal) (#i:regid)
  (a:info0 i) (k:secret u i) (h:mem) =
  (safe u i ==>
    (let KDF_table r t = Model.ideal k () in
     sel h t == MDM.empty #(domain u i) #(kdf_range u i)))

// Framing for the kdf_post depends only on kdf_footprint k
let kdf_post_framing (#ideal:iflag) (#u:usage ideal) (#i:regid) (a:info0 i)
  (k:secret u i) (h0:mem) (r:rid) (h1:mem)
  : Lemma (requires (kdf_post a k h0 /\ modifies_one r h0 h1 /\ ~(r `Set.mem` kdf_footprint k)))
          (ensures (kdf_post a k h1))
  = admit()

val coerceT:
  #ideal: iflag ->
  u: usage ideal ->
  i: regid{~(safe u i)} ->
  a: info0 i ->
  repr: lbytes32 (secret_len a) ->
  GTot (secret u i)
let coerceT #ideal u i a repr =
  Model.mk_real (| a, repr |)

val coerce:
  #ideal: iflag ->
  u: usage ideal ->
  i: regid{~(safe u i)} ->
  a: info0 i ->
  repr: lbytes32 (secret_len a) ->
  ST (secret u i)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> modifies_none h0 h1
    /\ k == coerceT u i a repr
    /\ fresh_regions (kdf_footprint k) h0 h1
    /\ kdf_post a k h1 /\ local_kdf_invariant k h1)

#reset-options "--z3rlimit 100" 
let coerce #ideal u i a repr =
  let k = Model.mk_real (| a, repr |) in
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
let alloc #a #b #inv (r: erid): 
  ST (MDM.t r a b inv)
    (requires (fun h -> 
      inv (MDM.empty_partial_dependent_map #a #b) /\ 
      witnessed (region_contains_pred r) ))
    (ensures (fun h0 x h1 ->
      inv (MDM.empty_partial_dependent_map #a #b) /\
      ralloc_post r (MDM.empty #a #b) h0 x h1))
  = MDM.alloc #a #b #inv #r ()

noextract
val create:
  #ideal: iflag ->
  u: usage ideal ->
  i: regid ->
  a: info0 i ->
  ST (secret u i)
  (requires fun h0 -> model)
  (ensures fun h0 k h1 -> modifies_none h0 h1
    /\ fresh_regions (kdf_footprint k) h0 h1
    /\ kdf_post a k h1 /\ local_kdf_invariant k h1)

noextract
let create #ideal u i a =
  let h0 = get() in
  let honest = get_honesty i in
  let h1 = get() in
  if ideal && honest then
   begin
    assert(safe u i);
    let r : subrgn kdf_tables_region = new_region kdf_tables_region in
    let h2 = get() in
    assert(Mem.fresh_region r h1 h2);
    let t : table u i () = KDF_table r (alloc r) in
    let h3 = get() in
    let k : secret u i = Model.mk_ideal t in
    assume(kdf_footprint k == Set.singleton r);
    assume(local_kdf_invariant k h3);
    assert(fresh_regions (kdf_footprint k) h0 h3);
    k
   end
  else
   begin
    let k = Model.mk_real (| a, sample (secret_len a) |) in
    assume(local_kdf_invariant k h1);
    k
   end


/// We are using many KDF packages (one for each usage),
/// idealized one at a time.  (Having one proof step for each nested
/// level of key derivation seems unavoidable: we need to idealize
/// parents before childrens.)

noextract inline_for_extraction
let local_kdf_pkg (ideal:iflag) (u:usage ideal) : local_pkg ii =
  (LocalPkg
    (secret u)
    info0
    (fun #_ a -> secret_len a)
    (b2t ideal)
    (kdf_shared_footprint u)
    (kdf_footprint #ideal #u)
    (local_kdf_invariant #ideal #u)
    (local_kdf_invariant_framing #ideal #u)
    (kdf_post #ideal #u)
    (kdf_post_framing #ideal #u)
    (create #ideal u)
    (coerceT #ideal u)
    (coerce #ideal u))

noextract
let pp (ideal:iflag) (u:usage ideal) : ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 ->
     modifies_mem_table p.define_table h0 h1 /\
     p.package_invariant h1)
  =
  memoization_ST #ii (local_kdf_pkg ideal u)

/// 17-11-30 experiment, testing package trees on a simple case: AEAD
/// keying and forward re-keying; still unclear how to traverse the
/// packaging.


/// Global, generic invariant, to be rooted at the PSK
/// (do we need some "static index"?)

// node footprints already recursively collect their children's footprints
let tree_footprint (#p:Type0) (x:tree' p) h : GTot rset =
  match x with
  | Leaf p -> Pkg?.footprint p h
  | Node p c -> Pkg?.footprint p h

// WIP: footprint_kdf includes the define tables of children, but not the package footprints
//    rset_union (Pkg?.footprint p h)
//      (List.Tot.fold_left (fun s p -> rset_union s (Pkg?.footprint p h)) c Set.empty)

// library??
noextract
val list_forall: ('a -> Type0) -> list 'a -> Tot Type0
let rec list_forall f l = match l with
    | [] -> True
    | hd::tl -> f hd /\ list_forall f tl

noextract
val disjoint_children: mem -> #p:Type0 -> children' p -> Type0
let rec disjoint_children h #p x =
  match x with
  | [] -> True
  | (l0, x0) :: tail -> list_forall (fun (l1, x1) -> tree_footprint #p x0 h `Set.disjoint` tree_footprint #p x1 h) tail

noextract
let rec children_forall
  (#p:Type0) (lxs: children' p)
  (f: (x:tree' p{depth x <= children_depth lxs} -> Type0)): Type0
=
  match lxs with
  | [] -> True
  | (_,x)::tl -> f x /\ children_forall tl f

noextract
let rec tree_invariant' (#pp:Type0) (x:tree' pp) (h:mem)
  : Tot Type0 (decreases %[depth x]) =
  match x with
  | Leaf p -> Pkg?.package_invariant p h
  | Node p lxs ->
    Pkg?.package_invariant p h /\
    children_forall lxs (fun x -> tree_invariant' x h) /\
    disjoint_children h lxs

inline_for_extraction
let tree_invariant #p (x:tree p) h =
  if model then
    let x' : tree' p = x in tree_invariant' x' h
  else True

// We can frame the multi-pkg invariant for free when touching tls_honest_region
let tree_invariant_frame #p (t:tree p) (h0:mem) (h1:mem)
  : Lemma (requires tree_invariant t h0 /\ (modifies_none h0 h1 \/ modifies_one tls_honest_region h0 h1))
          (ensures tree_invariant t h1)
  = admit()

// TODO 17-12-01 we need an hypothesis that captures that p is in the tree, e.g. only deal with the case where p is a child.

type kdf_subtree (ideal:iflag) (t:tree (b2t ideal)) =
  (if model then
    let t : tree' (b2t ideal) = t in
    Node? t /\ (let Node p u = t in
    Pkg?.ideal p == b2t ideal /\
    Pkg?.key p == LocalPkg?.key (local_kdf_pkg ideal u) /\
    p == memoization (local_kdf_pkg ideal u) p.define_table)
  else True)

noextract
let itree (#p:Type0) (t:tree p) : Pure (tree' p) (requires model)
  (ensures fun t' -> t' == t) = let t':tree' p = t in t'

inline_for_extraction noextract
let u_of_t (#ideal:iflag) (t:tree (b2t ideal){kdf_subtree ideal t}) : usage ideal =
  if model then Node?.children (itree t) else erased_tree

// Derive can now be called outside the tree specification
// (i.e. when u(lbl) undefined), but only concretely.
// Otherwise, the model code modifies:
//  - the honesty table
//  - the define table of the derived package
//  - the KDF table
type modifies_derive (#ideal:iflag) (#u:usage ideal) (#i:regid) (k:secret u i)
  (lbl:label) (ctx:context {wellformed_derive i lbl ctx}) (h0:mem) (h1:mem) =
  (if u `has_lbl` lbl then
    let modset = Set.singleton tls_define_region in
    let modset = Set.union modset (Set.singleton tls_honest_region) in
    let modset =
      if Model.is_safe k then
        let KDF_table r _ = Model.ideal k () in Set.union modset (Set.singleton r)
      else modset in
    let utable = (child u lbl).define_table in
    modifies modset h0 h1
    /\ HS.modifies_ref tls_define_region (Set.singleton (mem_addr (itable utable))) h0 h1
  else modifies_none h0 h1) // FIXME concrete state

(** Ugly coercion, required because the type equality is proved by normalization **)
noextract
private let _mem_coerce (#t0:eqtype) (#t1:t0 -> Type) (dt:mem_table t1) (#ideal:iflag) (t:tree (b2t ideal){kdf_subtree ideal t})
  : Pure (mem_table (secret (u_of_t t)))
  (requires model /\ t0 == regid /\ t1 == secret (u_of_t t))
  (ensures fun dt' -> True) = dt

inline_for_extraction noextract
let kdf_dt (#ideal:iflag) (t:tree (b2t ideal){kdf_subtree ideal t})
  : mem_table (secret (u_of_t t)) =
  if model then
    let Node p u = itree t in
    _mem_coerce (Pkg?.define_table p) t
  else ()

// FIXME(adl) only works for packages built from local_pkg
// need to extend to global state packages
// WIP(adl) hopefully, this all packages will fit this case now
let compatible_packages (lp:local_pkg ii) (p:pkg ii) =
  Pkg?.key p == LocalPkg?.key lp /\
  p == memoization lp p.define_table

/// The well-formedness condition on the derived label (opaque from
/// the viewpoint of the KDF) enforces
///
#set-options "--query_stats"
noextract inline_for_extraction
val derive:
  #ideal: iflag ->
  #t: tree (b2t ideal){kdf_subtree ideal t} ->
  #i: regid ->
  k: secret (u_of_t t) i ->
  lbl: label ->
  ctx: context {~(honest_idh ctx) /\ wellformed_derive i lbl ctx} ->
  child_pkg: local_pkg ii{~(LocalPkg?.ideal child_pkg)} ->
  a': LocalPkg?.info child_pkg (derive i lbl ctx) ->
  ST (_:squash (registered (derive i lbl ctx)) &
      (LocalPkg?.key child_pkg) (derive i lbl ctx))
  (requires fun h0 ->
    (LocalPkg?.len child_pkg) a' == Hacl.Hash.Definitions.hash_len (get_info k).ha /\
    ((u_of_t t) `has_lbl` lbl ==>
      compatible_packages child_pkg (child (u_of_t t) lbl)) /\
    mem_defined (kdf_dt t) i /\
    tree_invariant t h0)
  (ensures fun h0 (| () , r |) h1 ->
    modifies_derive k lbl ctx h0 h1 /\
    tree_invariant t h1 /\
    (~(safe (u_of_t t) i) ==> (
      let (| a, raw |) = Model.real k in
      let lb = Bytes.bytes_of_string lbl in
      let len' = LocalPkg?.len child_pkg a' in
      r == (LocalPkg?.coerceT child_pkg) (derive i lbl ctx) a'
      (HKDF.expand_spec #a.ha raw lb len'))) /\
    (model ==> (LocalPkg?.post child_pkg) a' r h1))

noextract inline_for_extraction
let derive #ideal #t #i k lbl ctx child_pkg a' =
  let u = u_of_t t in
  let dt = kdf_dt t in
  let h0 = get() in
  let honest = get_honesty i in
  let i', honest' = register_derive i lbl ctx in
  let h1 = get() in
  tree_invariant_frame t h0 h1;
  lemma_corrupt_invariant i lbl ctx;

  if model then
   begin
    assume false; // Ideal branch is WIP, working on extraction now
    let _ = // Ghost section
      let log = itable dt in
      recall log;
      let m = sel h1 log in
      assume(MDM.sel m i == Some k); // testify
      lemma_mm_forall_elim m local_kdf_invariant i k h1;
      assert(local_kdf_invariant k h1)
      in
    let pkg = child u lbl in
    assert(Pkg?.ideal pkg ==> b2t ideal); // Nice!
    
    if (u `has_lbl` lbl) && ideal && honest then
     begin
      let x: domain u i = Domain lbl ctx in
      let KDF_table kdf_r kdf_t : table u i () = Model.ideal k () in
      let v: option (derived_key u i lbl ctx) = MDM.lookup kdf_t x in
      match v with
      | Some dk -> (| (), dk |)
      | None ->
	let dk = (Pkg?.create pkg) i' a' in
	let h2 = get() in
	assume(tree_invariant t h2);
	assert(mem_fresh pkg.define_table i' h2); // from kdf_local_inv
	MDM.extend kdf_t x dk;
	(| (), dk |)
      end
    else
     begin
      let dlen = (LocalPkg?.len child_pkg) a' in 
      let raw = HKDF.expand #((get_info k).ha) (dsnd (Model.real k)) (FStar.Bytes.bytes_of_string lbl) dlen in
      let dk = (LocalPkg?.coerce child_pkg) i' a' raw in
      (| (), dk |)
     end
   end
  else
   begin
    assert(h1 == h0);
    let len' = (LocalPkg?.len child_pkg) a' in 
    let (| a, key |) = Model.real k in
    let lb = FStar.Bytes.bytes_of_string lbl in
    let raw = HKDF.expand #(a.ha) key lb len' in
    let dk = (LocalPkg?.coerce child_pkg) i' a' raw in
    let h2 = get() in
//    assert(modifies_none h1 h2); 
    assume(modifies_derive k lbl ctx h0 h2); // FIXME stronger spec for Pkg.coerce?
    (| (), dk |)
   end
