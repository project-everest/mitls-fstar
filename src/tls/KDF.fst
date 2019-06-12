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
open FStar.HyperStack.ST

module M = LowStar.Modifies
module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module HS = FStar.HyperStack
module DT = DefineTable
module HD = Spec.Hash.Definitions

#set-options "--max_fuel 1 --max_ifuel 1 --z3rlimit 30"

(*
This module defines a universal, packaged KDF parametric in its
usage (which is a tree of derived packages).

The KDF is idealized as a memoization table from label and context
to instances (whose type is computed from the usage and label)
*)

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

let valid_info (i:id) (v:info) = model ==> (v == index_info i)

type info0 (i:id) = u:info{valid_info i u}
type iflag = b:bool{b ==> model}
type usage (ideal:iflag) = children (b2t ideal)

(* Computes the type of a derived instance from the KDF usage *)
let derived_key
  (#ideal:iflag)
  (u: usage ideal)
  (i: regid)
  (lbl: label {u `has_lbl` lbl})
  (ctx: context)
  : Pure Type0
  (requires model /\ wellformed_derive i lbl ctx /\
    registered (derive i lbl ctx))
  (ensures fun t -> True)
  = Pkg?.key (child u lbl) (Derive i lbl ctx)

inline_for_extraction
let secret_len (a:info) : keylen = Hacl.Hash.Definitions.hash_len a.ha
type real_secret (i:regid) = a:info0 i & lbytes32 (secret_len a)

let safe (#ideal:iflag) (u:usage ideal) (i:regid) =
  honest i /\ b2t ideal

// This is the type of KDF instances
// The idealized KDF does not have any state; 
// we rely on the children packages to compute
// a virtual idealization table
type secret (#ideal:iflag) (u:usage ideal) (i:regid) =
  Model.ir (safe u) unit (real_secret i) i

(* Honestly invariants for derived instances *)

val lemma_witnessed_true (p:mem_predicate) :
  Lemma (requires (forall h. p h)) (ensures witnessed p)
let lemma_witnessed_true p =
  lemma_witnessed_constant True;  weaken_witness (fun _ -> True) p

private let lemma_honest_parent (i:regid) (lbl:label) (ctx:context)
  : Lemma
  (requires wellformed_derive i lbl ctx /\ 
    registered (derive i lbl ctx) /\ 
    ~(honest_idh ctx) /\ 
    honest (derive i lbl ctx))
  (ensures honest i)
  =
  if model then
    let log : i_honesty_table = honesty_table in
    lemma_witnessed_true (fun h ->
      MDM.contains log (derive i lbl ctx) true h ==> MDM.contains log i true h);
    lemma_witnessed_impl (MDM.contains log (derive i lbl ctx) true)
      (MDM.contains log i true)

let lemma_honest_parent_impl (i:regid) (lbl:label) (ctx:context)
  : Lemma
    (requires wellformed_derive i lbl ctx /\ 
      registered (derive i lbl ctx) /\ ~(honest_idh ctx))
    (ensures honest (derive i lbl ctx) ==> honest i)
  = FStar.Classical.impl_intro_gen #(honest (derive i lbl ctx)) #(fun _ -> honest i)
    (fun (u:squash (honest (derive i lbl ctx))) -> lemma_honest_parent i lbl ctx)

(* Concrete info (hash agility) *)

inline_for_extraction
let get_info (#ideal:iflag) (#u:usage ideal) (#i:regid) (k:secret u i) =
  if Model.is_safe k then index_info i else dfst (Model.real k)

(*** Virtual KDF table ***)

(*
The ideal behavior of a KDF is to map labels and contexts to derived instances:

  ideal_kdf u i == l:label -> c:context -> k:(child u l).key (derive i l c)

However, to avoid state duplication, we do not actually materialize this table.
Instead, we compute the table from the define_table of children packages.
This is a nice simplification because the only state of a KDF table is its own
define table. (However, the footprint of a KDF package now includes the
define tables of all of its children).

The define table for package pkg is of the form (i:regid -> pkg.key i),
and it is global for the package. In contrast, the KDF table is specific
to the instance of the KDF. Hence, we need to filter the entries of children's
define table to only the instances whose index is derived from the KDF
instance's index. We also need to re-index the filtered table to get
the computed idealization table.

Then, we specify the security of the KDF based on operations on the virtual
KDF table. The implementation, however, only operates on the children's
define tables.
*)

// KDF tables are indexed by label and context
type kdf_key (#ideal:iflag) (u:usage ideal) (i:regid{model}) (l:label{u `has_lbl` l}) =
  c:context{wellformed_derive i l c /\ registered (derive i l c)}

// They store derived instances, whose type is directed by the usage
type kdf_value (#ideal:iflag) (u:usage ideal) (i:regid{model})
  (l:label{u `has_lbl` l}) (k:kdf_key u i l) =
  option (derived_key u i l k)

// We shard the table by label
type kdf_table_shard (#ideal:iflag) (u:usage ideal)
  (i:regid{model}) (l:label{u `has_lbl` l}) =
  DM.t (kdf_key u i l) (kdf_value u i l)

// The type of computed KDF tables, indexed by label, then context
type kdf_table (#ideal:iflag) (u:usage ideal) (i:regid{model}) =
  DM.t (l:label{u `has_lbl` l}) (kdf_table_shard u i)

type derived_from (#ideal:iflag) (u:usage ideal)
  (i:regid{model}) (l:label{u `has_lbl` l}) (j:regid) =
  (let j' : pre_id = j in
  match j' with
  | Derive i' lbl ctx -> i' == i /\ lbl == l
  | _ -> False)

// To compute the virtual KDF table, we need to re-index the
// projection of the children's KDF tables
let reindex (#ideal:iflag) (u:usage ideal) (i:regid{model})
  (l:label{u `has_lbl` l}) (k:kdf_key u i l)
  : (j:regid{derived_from u i l j}) =
  derive i l k

// This is not used concretely, but we prove that
// the re-indexing is bijective by constructing its inverse
let reindex_inv (#ideal:iflag) (u:usage ideal) (i:regid{model})
  (l:label{u `has_lbl` l}) (j:regid{derived_from u i l j})
  : kdf_key u i l =
  let j' : pre_id = j in
  let Derive i lbl ctx = j' in
  ctx

// We prove that the re-indexed virtual KDF table
// is isomorphic to the filtered define table
let lemma_reindex_correct (#ideal:iflag) (u:usage ideal)
  (i:regid{model}) (l:label{u `has_lbl` l}) (k:kdf_key u i l)
  : Lemma (reindex_inv u i l (reindex u i l k) == k)
  = ()

// When re-indexing the define table, we get a complicated type for the
// renamed instances. We show this type is equivalent to kdf_value
private noextract
let coerce_reindex (#ideal:iflag) (u:usage ideal) (i:regid{model}) (l:label{u `has_lbl` l})
  (k:kdf_key u i l) (v:DM.rename_value (MDM.opt (Pkg?.key (child u l))) (reindex u i l) k)
  : kdf_value u i l k
  = v

private let lemma_has_lbl_cons (#p:Type0) (u:children' p)
  (h:label * tree' p) (lbl:label)
  : Lemma (requires u `has_lbl'` lbl /\ fst h <> lbl)
  (ensures (h::u) `has_lbl'` lbl /\ child' (h::u) lbl == child' u lbl)
  = ()

// We desine a custom function for nth because we need to prove that
// has_lbl and child are preseved by list inclusion
private let rec nth_child (#p:Type0) (u:children' p{List.Tot.length u > 0})
  (n:nat{model /\ n < List.Tot.length u})
  : GTot (l:label{u `has_lbl'` l} & p:pkg ii{p == child' u l})
  (decreases n)
  =
  if n = 0 then
    let (lbl, p) = List.Tot.hd u in
    let pkg = match p with Node p _ -> p | Leaf p -> p in
    let _ = assert(child' u lbl == pkg) in
    (| lbl, pkg |)
  else 
    let u' = List.Tot.tl u in
    let (|lbl, p|) = nth_child u' (n-1) in
    // FIXME(adl): label disjointness, see disjoint_labels in Pkg.Tree
    let _ = assume(fst (List.Tot.hd u) <> lbl) in
    let _ = lemma_has_lbl_cons u' (List.Tot.hd u) lbl in
    (|lbl, p|)

// Given the index i of a KDF instance, we compute
// the associated virtual idealization table
let compute_kdf_table (#ideal:iflag) (u:usage ideal) (i:regid{model}) (h:mem)
  : GTot (kdf_table u i)
  =
  let l : children' (b2t ideal) = u in
  let m = List.Tot.length l in
  let rec aux (n:nat{n <= m}) : GTot (kdf_table u i) =
    if n = 0 then
      DM.create (fun l -> DM.create (fun k -> None <: kdf_value u i l k))
    else
      let (| lbl, pkg |) = nth_child l (m - n) in
      let dt : DT.dt #regid (Pkg?.key (child u lbl)) = pkg.define_table in
      // The define table is specified by a DependentMap
      let m = MDM.repr (HS.sel h (DT.ideal dt)) in
      // Filter for entries derived from i with label lbl
      let m' = DM.restrict (derived_from u i lbl) m in
      // Re-index table by context
      let m'' = DM.rename m' (reindex u i lbl) in
      // Coerce the type of instances to the type of KDF tables
      let m''' = DM.map (coerce_reindex u i lbl) m'' in
      DM.upd (aux (n-1)) lbl m'''
    in
  aux m

(*
type empty (#ideal:iflag) (#u:usage ideal) (#i:regid) (k:secret u i) (h:mem) =
  (if Model.is_safe k then HS.sel h (Model.ideal k) == MDM.empty else True)

type live (#ideal:iflag) (#u:usage ideal) (#i:regid) (k:secret u i) (h:mem) =
  Model.is_safe k ==> h `HS.contains` (Model.ideal k)
*)

// The KDF invariant specifies that when the KDF is ideal,
// its table contains entries that are defined if, and only if,
// the derived index is in the define table of the child package.
//
// If the KDF is real, we functionally specify the instances that
// defined in the child package's define table using coerceT
type kdf_invariant_wit (#ideal:iflag) (#u:usage ideal) (#i:regid)
  (k:secret u i) (h:mem) (lbl:label {u `has_lbl` lbl})
  (ctx:context{~(honest_idh ctx) /\ wellformed_derive i lbl ctx /\ registered (derive i lbl ctx)})
  =
  (let i' : regid = derive i lbl ctx in
  lemma_honest_parent_impl i lbl ctx;
  let pkg' = child u lbl in
  let dt = DT.ideal pkg'.define_table in
  DT.live #_ #(Pkg?.key pkg') dt h /\
  (if Model.is_safe k then (
    True
//    h `HS.contains` (Model.ideal k) // KDF table is live
//    MDM.sel (sel h (Model.ideal k)) (Domain lbl ctx) == MDM.sel (sel h dt) i'
  ) else
   begin
    let (| a, raw |) = Model.real k in
    (match MDM.sel (sel h dt) i' with
    | None -> True
    | Some k' ->
      let a' = Pkg?.info_of_id pkg' i' in
      let len' = Pkg?.len pkg' a' in
      let lb = FStar.Bytes.bytes_of_string lbl in
      let raw' = HKDF.expand_spec #a.ha raw lb len' in
      k' == Pkg?.coerceT pkg' i' a' raw')
   end))

let lemma_kdf_invariant_init_wit (#ideal:iflag) (#u:usage ideal) (#i:regid)
  (k:secret u i) (h:mem) (lbl:label {u `has_lbl` lbl})
  (ctx:context{~(honest_idh ctx) /\ wellformed_derive i lbl ctx /\ registered (derive i lbl ctx)})
  : Lemma (requires // empty k h /\ live k h /\
    DT.live (child u lbl).define_table h /\
    DT.empty (child u lbl).define_table h)
  (ensures kdf_invariant_wit k h lbl ctx)
  =
  if model then (
    let dt = DT.ideal (child u lbl).define_table in
    assert_norm(DT.empty (child u lbl).define_table h == (model ==> HS.sel h dt == MDM.empty))
  ) else ()

// The KDF invariant holds for all children (i.e. all lbl s.t. u `has_lbl` lbl)
type kdf_invariant (#ideal:iflag) (#u:usage ideal) (#i:regid) (k:secret u i) (h:mem) =
  (if model then
    (forall (lbl:label {u `has_lbl` lbl})
       (ctx:context{~(honest_idh ctx) /\ wellformed_derive i lbl ctx /\ registered (derive i lbl ctx)}).
    kdf_invariant_wit k h lbl ctx)
  else True)

// The union of all the define table of the children of the KDF
let rec children_fp (#p:Type) (u:children' p) : GTot M.loc =
  match u with
  | [] -> M.loc_none
  | (lbl, _)::t ->
    M.loc_union (DT.loc (child' u lbl).define_table) (children_fp #p t)

// The footprint of the KDF invariant is:
//  - DEPRECATED 1. its idealized KDF table
//  - 2. the define table of all children
let kdf_footprint (#ideal:iflag) (#u:usage ideal) (#i:regid) (k:secret u i)
  : GTot M.loc =
  if model then children_fp (u <: children' (b2t ideal)) else M.loc_none

// Intuitively, if a location is disjoint from the KDF footprint,
// it is disjoint from the define table of all children. The proof
// is by induction over the children but it is very difficult to define
// the restriction of a KDF to a sub-list of children.
let lemma_kdf_footprint_disjoint_wit (#ideal:iflag) (#u:usage ideal)
  (#i:regid) (k:secret u i) (lbl:label {u `has_lbl` lbl})
  (ctx:context{~(honest_idh ctx) /\ wellformed_derive i lbl ctx
    /\ registered (derive i lbl ctx)}) (l:M.loc)
  : Lemma (requires M.loc_disjoint l (kdf_footprint k))
  (ensures M.loc_disjoint l (DT.loc (child u lbl).define_table))
  =
  if model then
    let rec aux (#p:Type0) (u:children' p) (lbl:label{u `has_lbl'` lbl})
      : Lemma
        (requires M.loc_disjoint l (children_fp u))
        (ensures M.loc_disjoint l (DT.loc (child' u lbl).define_table))
      =
      match u with
      | [] -> assert_norm(u `find_lbl'` lbl == None)
      | (lbl', _) :: t ->
        if lbl = lbl' then ()
        else aux t lbl
      in
    aux (u <: children' (b2t ideal)) lbl
  else ()

// Trivial lemma but useful to drive stateful proofs by introducing
// the expected goals and the right patterns
private let lemma_unchanged #a #rel (r:mreference a rel) h0 l h1 : Lemma
  (requires M.modifies l h0 h1 /\ h0 `HS.contains` r /\
    M.loc_disjoint l (M.loc_mreference r))
  (ensures HS.sel h0 r == HS.sel h1 r) = ()

let lemma_kdf_invariant_init (#ideal:iflag) (#u:usage ideal)
  (#i:regid) (k:secret u i) (h:mem)
  : Lemma (requires //empty k h /\ live k h /\
    (forall (l:label{u `has_lbl` l}).
      DT.live (child u l).define_table h /\
      DT.empty (child u l).define_table h))
    (ensures kdf_invariant k h)
  =
  if model then
    let prove_on_witness (lbl:label {u `has_lbl` lbl})
      (ctx:context{~(honest_idh ctx) /\ wellformed_derive i lbl ctx
        /\ registered (derive i lbl ctx)})
      : Lemma (kdf_invariant_wit k h lbl ctx)
      =
      lemma_kdf_invariant_init_wit k h lbl ctx
    in
    FStar.Classical.forall_intro_2 prove_on_witness

let kdf_invariant_framing (#ideal:iflag) (#u:usage ideal)
  (#i:regid) (k:secret u i) (h0:mem) (l:M.loc) (h1:mem)
  : Lemma (requires kdf_invariant k h0 /\ M.modifies l h0 h1 /\
    M.loc_disjoint l (kdf_footprint k))
    (ensures kdf_invariant k h1)
  =
  if model then
    let prove_on_witness (lbl:label {u `has_lbl` lbl})
      (ctx:context{~(honest_idh ctx) /\ wellformed_derive i lbl ctx
        /\ registered (derive i lbl ctx)})
      : Lemma (kdf_invariant_wit k h1 lbl ctx)
      =
      let i' : regid = derive i lbl ctx in
      lemma_honest_parent_impl i lbl ctx;
      let pkg' = child u lbl in
      let dt : DT.table (Pkg?.key pkg') = DT.ideal pkg'.define_table in
      assert_norm(DT.live pkg'.define_table h0 ==
        (model ==> h0 `HS.contains` dt));
      assert_norm(DT.loc pkg'.define_table ==
        (if model then M.loc_mreference dt else M.loc_none));
      lemma_kdf_footprint_disjoint_wit k lbl ctx l;
      lemma_unchanged dt h0 l h1 // Trivial, but helps the proof
//      if Model.is_safe k then lemma_unchanged (Model.ideal k) h0 l h1
    in
    FStar.Classical.forall_intro_2 prove_on_witness

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
  (requires fun h0 -> valid_info i a)
  (ensures fun h0 k h1 ->
    M.modifies M.loc_none h0 h1 /\
    k == coerceT u i a repr /\
    fresh_loc (kdf_footprint k) h0 h1 /\
    kdf_invariant k h1)

let coerce #ideal u i a repr =
  let h0 = get () in
  let k = Model.mk_real (| a, repr |) in
  let h1 = get () in
  assume false;
  lemma_kdf_invariant_init k h1;
  k

noextract
val create:
  #ideal: iflag ->
  u: usage ideal ->
  i: regid ->
  a: info0 i ->
  ST (secret u i)
  (requires fun h0 -> model)
  (ensures fun h0 k h1 -> modifies_none h0 h1
//    /\ fresh_regions (kdf_footprint k) h0 h1
//    /\ kdf_post a k h1
     /\ kdf_invariant k h1)

#set-options "--admit_smt_queries true"

noextract
let create #ideal u i a =
  let h0 = get() in
  let honest = get_honesty i in
  let h1 = get() in
  if ideal && honest then
   begin
     (*
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
    k *) Model.mk_ideal () <: secret u i
   end
  else
   begin
    let k = Model.mk_real (| a, sample (secret_len a) |) in
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
    index_info
    (fun #_ a -> secret_len a)
    (b2t ideal)
    (fun #_ _ -> M.loc_none)
    (kdf_invariant #ideal #u)
    (kdf_invariant_framing #ideal #u)
    (create #ideal u)
    (coerceT #ideal u)
    (coerce #ideal u))

noextract
let pp (ideal:iflag) (u:usage ideal) : ST (pkg ii)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 ->
    locally_packaged p (local_kdf_pkg ideal u) /\
    p.package_invariant h1 /\
    fresh_loc (DT.loc p.define_table) h0 h1)
  =
  memoization_ST #ii (local_kdf_pkg ideal u)

// library??
noextract
val list_forall: ('a -> Type0) -> list 'a -> Tot Type0
let rec list_forall f l = match l with
    | [] -> True
    | hd::tl -> f hd /\ list_forall f tl

(*
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
*)

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
    let lhonest = M.loc_region_only true tls_honest_region in
    let utable = (child u lbl).define_table in
    M.modifies (M.loc_union utable lhonest) h0 h1
  else M.modifies M.loc_none h0 h1)

noextract
private let _mem_coerce (#t0:eqtype) (#t1:t0 -> Type)
  (dt:DT.dt t1) (#ideal:iflag) (t:tree (b2t ideal){kdf_subtree ideal t})
  : Pure (DT.dt (secret (u_of_t t)))
  (requires model /\ t0 == rid /\ t1 == secret (u_of_t t))
  (ensures fun dt' -> True) = assert_norm(rid == regid); dt

inline_for_extraction noextract
let kdf_dt (#ideal:iflag) (t:tree (b2t ideal){kdf_subtree ideal t})
  : DT.dt (secret (u_of_t t)) =
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

// The well-formedness condition on the derived label (opaque from
// the viewpoint of the KDF) enforces
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
  ST (
    _:squash (registered (derive i lbl ctx)) &
    (LocalPkg?.key child_pkg) (derive i lbl ctx))
  (requires fun h0 ->
    UInt32.v ((LocalPkg?.len child_pkg) a') == HD.hash_length (get_info k).ha /\
    ((u_of_t t) `has_lbl` lbl ==>
      compatible_packages child_pkg (child (u_of_t t) lbl)) /\
    DT.defined (kdf_dt t) i /\
    tree_inv t h0)
  (ensures fun h0 (| () , r |) h1 ->
    modifies_derive k lbl ctx h0 h1 /\
    tree_inv t h1 /\
    (~(safe (u_of_t t) i) ==> (
      let (| a, raw |) = Model.real k in
      let lb = Bytes.bytes_of_string lbl in
      let len' = LocalPkg?.len child_pkg a' in
      r == (LocalPkg?.coerceT child_pkg) (derive i lbl ctx) a'
      (HKDF.expand_spec #a.ha raw lb len')))
    )
//    /\ (model ==> (LocalPkg?.post child_pkg) a' r h1))

noextract inline_for_extraction
let derive #ideal #t #i k lbl ctx child_pkg a' =
  let u = u_of_t t in
  let dt = kdf_dt t in
  let h0 = get() in

  // parent honesty is defined; child honesty is set accordingly if it is unregistered.
  let honest = get_honesty i in
  let i', honest' = register_derive i lbl ctx in
  let h1 = get() in
//  tree_invariant_frame t h0 h1;
  lemma_corrupt_invariant i lbl ctx;

  if model then
   begin
   (*
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
    *)
    admit()
   end
  else 
   begin
    assert(h1 == h0);
    let len' = (LocalPkg?.len child_pkg) a' in
    let (| a, key |) = Model.real k in
    let raw = HKDF.expand #a.ha key (Bytes.bytes_of_string lbl) len' in
    let dk = (LocalPkg?.coerce child_pkg) i' a' raw in
    let h2 = get() in
    (| (), dk |)
   end
