module Mem

/// Setting a uniform HyperStack-based memory model, and gathering
/// abbreviations and top-level regions. Note this module already
/// depends on Flags (as we do not wish to extract the global TLS
/// region and its contents).

open FStar.HyperStack.All

open FStar.Seq
open Platform.Bytes
open Platform.Error
open TLSError

include FStar.HyperStack
include FStar.HyperStack.ST

module HH = FStar.HyperHeap // avoid if we can
module HS = FStar.HyperStack
//module ST = FStar.HyperStack.ST

let model = Flags.model 

let disjoint = HH.disjoint

//type fresh_subregion r0 r h0 h1 = ST.stronger_fresh_region r h0 h1 /\ ST.extends r r0

(** Regions and colors for objects in memory *)
let tls_color = -1  //17-11-22 The color for all regions in the TLS global region.
let epoch_color = 1 //17-11-22 This needs fixing: we are not on the stack yet.
let hs_color = 2

let is_tls_rgn r   = HH.color r = tls_color
let is_epoch_rgn r = HH.color r = epoch_color
let is_hs_rgn r    = HH.color r = hs_color

(*
 * AR: Adding the eternal region predicate.
 * Strengthening the predicate because at some places, the code uses HH.parent.
 *)
let rgn = r:HH.rid{
  r<>HH.root /\
  (forall (s:HH.rid).{:pattern HS.is_eternal_region s} HS.is_above s r ==> HS.is_eternal_region s)}

let tls_rgn   = r:rgn {is_tls_rgn r}
let epoch_rgn = r:rgn {is_epoch_rgn r}
let hs_rgn    = r:rgn {is_hs_rgn r}

type fresh_subregion child parent h0 h1 =
  (is_tls_rgn child <==> is_tls_rgn parent) /\
  stronger_fresh_region child h0 h1 /\
  HH.extends child parent

type subrgn parent = r:rgn{HH.parent r = parent}

/// Global top-level region for TLS ideal state.
///
/// Top-level disjointness is awkward; we could instead maintain a
/// private mutable set of regions known to be pairwise-distinct.
///
let tls_region: tls_rgn = new_colored_region HH.root tls_color

type subtls = r: subrgn tls_region {is_tls_rgn r}

private let p : r0: subtls & r1: subtls & r2: subtls
  {r1 `disjoint` r0 /\ r2 `disjoint` r0 /\ r2 `disjoint` r1} =
  let r0 = new_colored_region tls_region tls_color in
  let r1 = new_colored_region tls_region tls_color in
  let r2 = new_colored_region tls_region tls_color in
  (| r0, r1, r2 |)

// consider dropping the tls_ prefix
let tls_tables_region: r:tls_rgn =
  match p with | (| r, _, _ |) -> r
let tls_define_region: r:tls_rgn{r `disjoint` tls_tables_region} =
  match p with | (| _, r, _ |) -> r
let tls_honest_region: r:tls_rgn{r `disjoint` tls_tables_region /\ r `disjoint` tls_define_region} =
  match p with | (| _, _, r |) -> r




// used for defining 1-shot PRFs.
val ssa: #a:Type0 -> Preorder.preorder (option a)
let ssa #a =
  let f x y =
    match x,y with
    | None, _  -> True
    | Some v, Some v' -> v == v'
    | _ -> False in
  f




(* An earlier variant of the code below, to be deleted 

// FIXME(adl) can't write Set.set rgn because unification fails in pkg!!
// FIXME(adl) overcomplicated type because of transitive modifications.
// An rset can be thought of as a set of disjoint subtrees in the region tree
// the second line embeds the definition of rgn because of the unification bug
type rset = s:Set.set HH.rid{
  (forall (r1:rgn) (r2:rgn).{:pattern (Set.mem r1 s /\ Set.mem r2 s)} (Set.mem r1 s /\ Set.mem r2 s) ==> (r1 == r2 \/ HH.disjoint r1 r2)) /\
  (forall (r1:rgn). (Set.mem r1 s ==>
     r1<>HH.root /\
     (is_tls_rgn r1 ==> r1 `HH.extends` tls_tables_region) /\
     (forall (s:HH.rid).{:pattern is_eternal_region s} s `is_above` r1 ==> is_eternal_region s)))}

// We get from the definition of rset that define_region and tls_honest_region are disjoint
let lemma_define_tls_honest_regions (s:rset)
  : Lemma (~(Set.mem tls_define_region s) /\ ~(Set.mem tls_honest_region s))
  = ()

//  if Set.mem tls_define_region s then
//    assert(tls_define_region `HH.extends` tls_)

type disjoint_rset (s1:rset) (s2:rset) =
  Set.disjoint s1 s2 /\
  (forall (r1:rgn) (r2:rgn).{:pattern (Set.mem r1 s1 /\ Set.mem r2 s2)}
   (Set.mem r1 s1 /\ Set.mem r2 s2) ==> HH.disjoint r1 r2)

assume val lemma_disjoint_ancestors:
  r1:rgn -> r2:rgn -> p1:rgn{r1 `is_below` p1} -> p2:rgn{r2 `is_below` p2}
  -> Lemma (requires p1 <> p2) (ensures HH.disjoint r1 r2 /\ r1 <> r2)
*)

// FIXME(adl) can't write Set.set rgn because unification fails in pkg!!
// the second line embeds the definition of rgn because of the unification bug
// FIXME(adl) overcomplicated type because of transitive modifications.
// An rset can be thought of as a set of disjoint subtrees in the region tree
// rset are downward closed - if r is in s and r' extends r then r' is in s too
// this allows us to prove disjointness with negation of set membership


module MR = FStar.Monotonic.RRef
module MM = FStar.Monotonic.Map
module MH = FStar.Monotonic.Heap

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

/// SZ: commented out this lemma that is also false. E.g. consider
/// p2 = new_region p1; r1 = new_region p2; r2 = new_region r1
(*
assume val lemma_disjoint_ancestors:
  r1:rgn -> r2:rgn -> p1:rgn{r1 `is_below` p1} -> p2:rgn{r2 `is_below` p2}
  -> Lemma (requires p1 <> p2) (ensures HH.disjoint r1 r2 /\ r1 <> r2)
*)

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
