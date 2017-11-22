module Mem

/// Setting a uniform HyperStack-based memory model, and gathering
/// abbreviations and top-level regions.

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

let disjoint = HH.disjoint 

//type fresh_subregion r0 r h0 h1 = ST.stronger_fresh_region r h0 h1 /\ ST.extends r r0

(** Regions and colors for objects in memory *)
let tls_color = -1
let epoch_color = 1
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


(* Definedness *)

module MM = FStar.Monotonic.Map
module MR = FStar.Monotonic.RRef

let model = Flags.model


// FIXME(adl) extend MonotoneMap
let mm_fold 
  (#r:MR.rid) (#a:Type) (#b:a -> Type) (#inv:MM.map' a b -> Type0) (t:MM.t r a b inv)
  (#rt:Type) (init:rt) (folder: rt -> i:a -> b i -> GTot rt) (h:mem): GTot rt
 = admit()

type mm_forall 
  (#r:MR.rid) (#a:Type) (#b:a -> Type) (#inv:MM.map' a b -> Type0) (t:MM.t r a b inv) 
  (phi: #i:a -> b i -> mem -> GTot Type0) (h:mem) =
   forall (i:a).{:pattern (MM.defined t i h)}
     MM.defined t i h ==>
       (let k = Some?.v (MM.sel (MR.m_sel h t) i) in phi k h)

let lemma_forall_frame 
  (#r:MR.rid) (#a:Type) (#b:a -> Type) (#inv:MM.map' a b -> Type0) (t:MM.t r a b inv) 
  (phi: #i:a -> b i -> mem -> GTot Type0)
  (footprint: #i:a -> v:b i -> GTot rset)
  (phi_frame: r:HH.rid -> i:a -> h0:mem -> v:b i -> h1:mem ->
    Lemma (requires phi v h0 /\ modifies_one r h0 h1 /\ ~(Set.mem r (footprint v)))
          (ensures phi v h1))
  (r:HH.rid) 
  (h0:mem) 
  (h1:mem): Lemma 
  (requires 
    mm_forall t phi h0 /\ 
    (modifies_one r h0 h1 \/ modifies_none h0 h1) /\
    (forall (i:a) (v:b i). ~(r `Set.mem` footprint v)))
  (ensures mm_forall t phi h1)
= 
  admit()
