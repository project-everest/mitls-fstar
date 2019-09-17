module Mem

/// * Sets a uniform Low* HyperStack-based memory model, gathering
///   abbreviations and top-level regions.
///
/// * Depends on Flags, as we do not to extract the global TLS region
///   and its contents (only ideal stuff).
///
/// Coding guidelines (aligned to EverCrypt)
/// - avoid eternal refs and buffers (fstar may deprecate them in lowstar)
/// - use LowStar.Buffer
/// - use monotonic buffers
///
/// - migrate from Bytes --> Spec-level sequences or Buffer [will take a while]
/// - enable divergence checking (try it out on a Everest feature branch?)
/// - use abbreviations wisely, e.g. only those to be defined in this file
///   (no clear consensus yet)
/// - use FStar.Integers (but avoid opening it because of v n etc... IntegersOps?)
///
/// - [create parent_region ...] may allocate a private sub-region,
///   unless its state is e.g. just a single transparent reference;
///   the caller usually tracks it using locations rather than regions.

open FStar.Error

include FStar.HyperStack
include FStar.HyperStack.ST

open LowStar.Buffer
open LowStar.BufferOps

open TLSError

/// 2019.06.20 SZ TODO: Port these to LowStar.Buffer
module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

#set-options "--z3rlimit 40 --max_fuel 0  --max_ifuel 0"

inline_for_extraction noextract
let model = Flags.model

let fresh_loc (l:loc) (h0 h1:mem) = loc_not_in l h0 /\ loc_in l h1

val fresh_is_disjoint (old_loc:loc) (new_loc:loc) (h0 h1:mem) : Lemma
  (requires fresh_loc new_loc h0 h1 /\ old_loc `loc_in` h0)
  (ensures  loc_disjoint old_loc new_loc)
let fresh_is_disjoint old_loc new_loc h0 h1 = ()

(** Used for defining one-shot PRFs and authenticators (could be moved to FStar.Preorder) *)
val ssa: #a:Type0 -> Preorder.preorder (option a)
let ssa #a = fun x y ->
  match x,y with
  | None, _  -> True
  | Some v, Some v' -> v == v'
  | _ -> False

/// Regions and colors for objects in memory; negative numbers are for eternal regions

let tls_color   = -1 // For all regions in the TLS global region.
let epoch_color = -2 // Unused so far.
let hs_color    = -3

let is_tls_rgn r   = (color r = tls_color)
let is_epoch_rgn r = (color r = epoch_color)
let is_hs_rgn r    = (color r = hs_color)

let rgn = r:erid{r =!= root}

let tls_rgn   = r:rgn{is_tls_rgn r}
let epoch_rgn = r:rgn{is_epoch_rgn r}
let hs_rgn    = r:rgn{is_hs_rgn r}

type fresh_subregion child parent h0 h1 =
  (is_tls_rgn child <==> is_tls_rgn parent) /\
  fresh_region child h0 h1 /\
  extends child parent

type subrgn p = r:rgn{parent r == p}

(** Global top-level region for TLS ideal state *)
let tls_region: tls_rgn = new_colored_region root tls_color

type subtls = r:subrgn tls_region{is_tls_rgn r}

/// Top-level disjointness
///
/// This is awkward; we could instead maintain a private mutable set of
/// regions known to be pairwise-distinct.
/// 2019.06.21 SZ: How?

#push-options "--max_ifuel 1"

(** r `rlist_disjoint` l holds if r is disjoint from all regions in l *)
val rlist_disjoint: subtls -> list subtls -> Type0
let rec rlist_disjoint r = function
  | [] -> True
  | r' :: l -> r `HS.disjoint` r' /\ rlist_disjoint r l

(** r_pairwise_disjoint l holds if all regions in l are pairwise disjoint *)
val r_pairwise_disjoint: list subtls -> Type0
let rec r_pairwise_disjoint = function
  | [] -> True
  | r :: l -> rlist_disjoint r l /\ r_pairwise_disjoint l

(** r_fresh l h0 h1 holds when all regions in l are fresh between h0 and h1 *)
val r_fresh: list subtls -> mem -> mem -> Type0
let rec r_fresh l h0 h1 =
  match l with
  | [] -> True
  | r :: l -> fresh_region r h0 h1 /\ r_fresh l h0 h1

val fresh_back (r:rgn) (h0 h1 h2:mem) : Lemma
  (requires fresh_region r h1 h2 /\ modifies_none h0 h1)
  (ensures  fresh_region r h0 h2)
//  [SMTPat (fresh_region r h1 h2); SMTPat (modifies_none h0 h1)]
let fresh_back r h0 h1 h2 = ()

#pop-options

#push-options "--max_fuel 1 --max_ifuel 1"

val r_fresh_back (l:list subtls) (h0 h1 h2:mem) : Lemma
  (requires r_fresh l h1 h2 /\ modifies_none h0 h1)
  (ensures  r_fresh l h0 h2)
let rec r_fresh_back l h0 h1 h2 =
  match l with
  | [] -> ()
  | r :: l' -> r_fresh_back l' h0 h1 h2

val r_fresh_fwd (l:list subtls) (h0 h1 h2:mem) : Lemma
  (requires r_fresh l h0 h1 /\ modifies_none h1 h2)
  (ensures  r_fresh l h0 h2)
let rec r_fresh_fwd l h0 h1 h2 =
  match l with
  | [] -> ()
  | r :: l' -> r_fresh_fwd l' h0 h1 h2

val r_fresh_disjoint (r:subtls) (l:list subtls) (h0 h1 h2:mem) : Lemma
  (requires r_fresh l h0 h1 /\ fresh_region r h1 h2)
  (ensures  rlist_disjoint r l)
let rec r_fresh_disjoint r l h0 h1 h2 =
  match l with
  | [] -> ()
  | r' :: l' ->
    lemma_extends_disjoint tls_region r r';
    r_fresh_disjoint r l' h0 h1 h2

val r_fresh_forall: l:list subtls -> h0:mem -> h1:mem -> Lemma
  ((forall r.{:pattern fresh_region r h0 h1} List.Tot.mem r l ==> fresh_region r h0 h1) <==>
   r_fresh l h0 h1)
let rec r_fresh_forall l h0 h1 =
  match l with
  | [] -> ()
  | r :: l' -> r_fresh_forall l' h0 h1

(** Allocates n pairwise disjoint subregions of tls_region *)
val r_disjoint_alloc: n:nat -> ST (l:list subtls)
  (requires fun h0 -> True)
  (ensures  fun h0 l h1 ->
    modifies_none h0 h1 /\
    r_fresh l h0 h1 /\
    List.Tot.length l == n /\
    r_pairwise_disjoint l)
let rec r_disjoint_alloc n =
  if n = 0 then []
  else
    begin
    let h0 = ST.get () in
    let l = r_disjoint_alloc (n-1) in
    let h1 = ST.get () in
    let r = new_colored_region tls_region tls_color in
    let h2 = ST.get () in
    r_fresh_disjoint r l h0 h1 h2;
    r_fresh_fwd l h0 h1 h2;
    r :: l
    end

#pop-options

// We use region disjointness as a coarse grained way of framing invariants.
let top_regions: (l:list subtls{List.Tot.length l == 5 /\ r_pairwise_disjoint l})
  = r_disjoint_alloc 5

let tls_tables_region = List.Tot.index top_regions 0
let tls_define_region = List.Tot.index top_regions 1
let tls_honest_region = List.Tot.index top_regions 2
let tls_psk_region    = List.Tot.index top_regions 3
let tls_crf_region    = List.Tot.index top_regions 4

#push-options "--z3rlimit 40 --max_fuel 5  --max_ifuel 0"

val top_regions_disjoint: i:nat{i < 5} -> j:nat{j < 5} -> Lemma
  (requires i <> j)
  (ensures  (List.Tot.index top_regions i) `HS.disjoint` (List.Tot.index top_regions j))
  [SMTPat (List.Tot.index top_regions i); SMTPat (List.Tot.index top_regions j)]
let top_regions_disjoint i j = ()

#pop-options

(** Sanity check: this works with fuel=0, ifuel=0 because of the lemma above *)
let _ = assert (tls_crf_region `HS.disjoint` tls_tables_region)

/// Loc-based disjointness
///
/// `loc_region_only` has GTot effect so we need to thunk these to avoid
/// problems with top-level masked effects

val loc_tables_region: unit -> GTot loc
let loc_tables_region _ = loc_region_only true tls_tables_region

val loc_define_region: unit -> GTot loc
let loc_define_region _ = loc_region_only true tls_define_region

val loc_honest_region: unit -> GTot loc
let loc_honest_region _ = loc_region_only true tls_honest_region

val loc_psk_region: unit -> GTot loc
let loc_psk_region _ = loc_region_only true tls_psk_region

val loc_crf_region: unit -> GTot loc
let loc_crf_region _ = loc_region_only true tls_crf_region

(** Sanity check: this works with fuel=0, ifuel=0 because of the lemma above *)
let _ = assert (all_disjoint
  [loc_tables_region ();
   loc_define_region ();
   loc_honest_region ();
   loc_psk_region ();
   loc_crf_region ()])
