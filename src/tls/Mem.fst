module Mem

/// Setting a uniform HyperStack-based memory model, and gathering
/// abbreviations and top-level regions. Note this module already
/// depends on Flags (as we do not wish to extract the global TLS
/// region and its contents).

open FStar.HyperStack.All

open FStar.Seq
open FStar.Bytes
open FStar.Error
open TLSError

include FStar.HyperStack
include FStar.HyperStack.ST

module HS = FStar.HyperStack
//module ST = FStar.HyperStack.ST

let model = Flags.model 

let disjoint = HS.disjoint

/// 18-01-04 We need to explicitly choose between using colors and
/// using hierarchy & transitivity.
/// 
//type fresh_subregion r0 r h0 h1 = ST.HS.fresh_region r h0 h1 /\ ST.extends r r0

(** Regions and colors for objects in memory; negative numbers are for eternal regions *)
let tls_color = -1   //17-11-22 The color for all regions in the TLS global region.
let epoch_color = -2 //17-11-22 Unused so far.
let hs_color = -3

let is_tls_rgn r   = HS.color r = tls_color
let is_epoch_rgn r = HS.color r = epoch_color
let is_hs_rgn r    = HS.color r = hs_color

(*
 * AR: 12/26: Adding the witnessed (region_contains_pred)
 *            This is required for allocation subregions
 *            And is provided as a postcondition of allocation
 *
 *            Also, the predicate `is_above s r ==> is_eternal_region s` was not necessary
 *            The shape of the memory provides it already
 *            See the lemma just below rgn
 *            Also see HyperStack.lemma_downward_closed that provides this from the memory model
 *)
let rgn = r:HS.rid{r =!= HS.root /\ is_eternal_region r /\ witnessed (region_contains_pred r)}

// 18-01-04 we would prefer [is_live_region] to [region_contains_pred].

let tls_rgn   = r:rgn {is_tls_rgn r}
let epoch_rgn = r:rgn {is_epoch_rgn r}
let hs_rgn    = r:rgn {is_hs_rgn r}

type fresh_subregion child parent h0 h1 =
  (is_tls_rgn child <==> is_tls_rgn parent) /\
  fresh_region child h0 h1 /\
  HS.extends child parent

type subrgn parent = r:rgn{HS.parent r == parent}

/// Global top-level region for TLS ideal state.
///
/// Top-level disjointness is awkward; we could instead maintain a
/// private mutable set of regions known to be pairwise-distinct.
///

private let p :
  tls_region:tls_rgn &
  r0:subrgn tls_region &
  r1:subrgn tls_region &
  r2:subrgn tls_region
  {is_tls_rgn r0 /\ is_tls_rgn r1 /\ is_tls_rgn r2 /\ r1 `disjoint` r0 /\ r2 `disjoint` r0 /\ r2 `disjoint` r1} =
  let tls_region: tls_rgn = new_colored_region HS.root tls_color in
  let r0 = new_colored_region tls_region tls_color in
  let r1 = new_colored_region tls_region tls_color in
  let r2 = new_colored_region tls_region tls_color in
  (| tls_region, r0, r1, r2 |)

// consider dropping the tls_ prefix
let tls_region: r:tls_rgn =
  match p with | (| r, _, _, _ |) -> r
let tls_tables_region: r:tls_rgn =
  match p with | (| _, r, _, _ |) -> r
let tls_define_region: r:tls_rgn{r `disjoint` tls_tables_region} =
  match p with | (| _, _, r, _ |) -> r
let tls_honest_region: r:tls_rgn{r `disjoint` tls_tables_region /\ r `disjoint` tls_define_region} =
  match p with | (| _, _, _, r |) -> r


// used for defining 1-shot PRFs and authenticators
//18-01-04 could be promoted to Preorder 
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
type rset = s:Set.set HS.rid{
  (forall (r1:rgn) (r2:rgn).{:pattern (Set.mem r1 s /\ Set.mem r2 s)} (Set.mem r1 s /\ Set.mem r2 s) ==> (r1 == r2 \/ HS.disjoint r1 r2)) /\
  (forall (r1:rgn). (Set.mem r1 s ==>
     r1<>HS.root /\
     (is_tls_rgn r1 ==> r1 `HS.extends` tls_tables_region) /\
     (forall (s:HS.rid).{:pattern is_eternal_region s} s `is_above` r1 ==> is_eternal_region s)))}

// We get from the definition of rset that define_region and tls_honest_region are disjoint
let lemma_define_tls_honest_regions (s:rset)
  : Lemma (~(Set.mem tls_define_region s) /\ ~(Set.mem tls_honest_region s))
  = ()

//  if Set.mem tls_define_region s then
//    assert(tls_define_region `HS.extends` tls_)

type disjoint_rset (s1:rset) (s2:rset) =
  Set.disjoint s1 s2 /\
  (forall (r1:rgn) (r2:rgn).{:pattern (Set.mem r1 s1 /\ Set.mem r2 s2)}
   (Set.mem r1 s1 /\ Set.mem r2 s2) ==> HS.disjoint r1 r2)

assume val lemma_disjoint_ancestors:
  r1:rgn -> r2:rgn -> p1:rgn{r1 `is_below` p1} -> p2:rgn{r2 `is_below` p2}
  -> Lemma (requires p1 <> p2) (ensures HS.disjoint r1 r2 /\ r1 <> r2)
*)


module MM = FStar.Monotonic.Map

// We use this instead of Set.set rgn because otherwise subtyping fails in pkg.
// The second line embeds the definition of rgn because of the unification bug
//
// An rset can be thought of as a set of disjoint subtrees in the region tree
// rset are downward closed - if r is in s and r' extends r then r' is in s too
// this allows us to prove disjointness with negation of set membership.

type rset = s:Set.set HS.rid{
  (forall (r1:HS.rid).{:pattern (Set.mem r1 s)} (Set.mem r1 s ==> 
     r1 <> HS.root /\
     (is_tls_rgn r1 ==> r1 `HS.extends` tls_tables_region) /\
     (forall (r':HS.rid).{:pattern (r' `HS.includes` r1)} r' `is_below` r1 ==> Set.mem r' s)))}

let rset_union (s1:rset) (s2:rset): Tot rset = Set.union s1 s2

/// SZ: This is the strongest lemma that is provable
/// Note that this old stronger version doesn't hold:
///
/// let lemma_rset_disjoint (s:rset) (r:HS.rid) (r':HS.rid)
///  : Lemma (requires ~(Set.mem r s) /\ (Set.mem r' s))
///          (ensures  r `HS.disjoint` r')

let lemma_rset_disjoint (s:rset) (r:HS.rid) (r':HS.rid)
  : Lemma (requires Set.mem r s /\ ~(Set.mem r' s) /\ r' `is_below` r)
          (ensures  r `HS.disjoint` r')
  = ()

// We get from the definition of rset that define_region and tls_honest_region are disjoint
let lemma_define_tls_honest_regions (s:rset)
  : Lemma (~(Set.mem tls_define_region s) /\ ~(Set.mem tls_honest_region s))
  = ()


//18-01-04 Consider moving the rest to a separate library
type trivial_inv (#it:eqtype) (#vt:it -> Type) (m:MM.map' it vt) = True
type i_mem_table (#it:eqtype) (vt:it -> Type) =
  MM.t tls_define_region it vt trivial_inv
type mem_table (#it:eqtype) (vt:it -> Type) =
  (if model then i_mem_table vt else unit)

let itable (#it:eqtype) (#vt:it -> Type) (t:mem_table vt)
  : Pure (i_mem_table vt) (requires model) (ensures fun _ -> True) = t

let mem_addr (#it:eqtype) (#vt:it -> Type) (t:i_mem_table vt): GTot nat = HS.as_addr t

type mem_fresh (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (i:it) (h:mem) =
  model ==> MM.fresh (itable t) i h
type mem_defined (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (i:it) =
  model ==> witnessed (MM.defined (itable t) i)
type mem_update (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (i:it) (v:vt i) (h0 h1:mem) =
  mem_defined t i /\
  (model ==> HS.sel h1 (itable t) == MM.upd (HS.sel h0 (itable t)) i v)

type mem_stable (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (h0 h1:mem) =
  model ==> HS.sel h0 (itable t) == HS.sel h1 (itable t)
type mem_empty (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (h1:mem) =
  model ==> HS.sel h1 (itable t) == MM.empty_map it vt

type modifies_mem_table (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (h0 h1:mem) =
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
  model ==> h `contains` (itable t)
let lemma_mem_disjoint_stable (#it:eqtype) (#vt:it -> Type) (t:mem_table vt)
  (#it':eqtype) (#vt':it' -> Type) (t':mem_table vt') (h0:mem) (h1:mem) : Lemma
  (requires modifies_mem_table t h0 h1 /\ mem_disjoint t t' /\ mem_contains t h0 /\ mem_contains t' h0)
  (ensures mem_stable t' h0 h1) = ()
let lemma_mem_frame (#it:eqtype) (#vt:it -> Type) (t:mem_table vt) (h0:mem) (r:HS.rid) (h1:mem) : Lemma
  (requires modifies_one r h0 h1 /\ tls_define_region `HS.disjoint` r /\ mem_contains t h0)
  (ensures mem_stable t h0 h1) = ()
