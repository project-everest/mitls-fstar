module Mem

/// * Sets a uniform Low* HyperStack-based memory model, gathering
///   abbreviations and top-level regions.
///
/// * Depends on Flags, as we do not to extract the global TLS region
///   and its contents (only ideal stuff).
/// 
/// Coding guidelines (aligned to EverCrypt)
/// - avoid eternal refs and buffer (fstar may deprecate them in lowstar)
/// - use LowStar.buffer and LowStar.modifies
/// - use monotonic buffers
/// 
/// - migrate from Bytes --> Spec-level sequences or Buffer [will take a while] 
/// - enable divergence checking (try it out on a Everest feature branch?)
/// - use abbreviations wisely, e.g. only those to be defined in this file (no clear consensus yet)
/// - use FStar.Integers (but avoid opening it because of v n etc... IntegersOps?)
/// 
/// - [create parent_region ...] may allocate a private sub-region,
///   unless its state is e.g. just a single transparent reference;
///   the caller usually tracks it using locations rather than
///   regions.

// TODO FStar.IntegerOps

// TODO LowStar.Lib variants of the stateful FStar.Lib we use,
// e.g. [FStar.DependentMap] and [FStar.Monotonic.DependentMap]


// open FStar.HyperStack.All // no need for Ocaml exceptions!
// open FStar.Seq
// open FStar.Bytes
open FStar.Error
open TLSError

include FStar.HyperStack
include FStar.HyperStack.ST

/// Low* buffers (new)

open LowStar.BufferOps 
// enabling the concrete syntax below. We don't open [LowStar.Buffer] to avoid shadowing
// [b.(i) <- v; b.(i)]
// [b *= v; !*b] when i = 0 for even nicer C syntax

module B = LowStar.Buffer // rather than bytes
module M = LowStar.Modifies

(* trying out  syntax 
open FStar.Integers 

// ? 
// inline_for_extraction
// let op_String_Access = Seq.index 

let f (b: B.buffer UInt8.t {B.length b = 1}): 
  ST unit
  (requires fun h0 -> B.live h0 b /\ Seq.head (B.as_seq h0 b) < 10uy  )
  (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer b) h0 h1  /\ B.live h1 b) = 
  b *= (3uy + (!*b))
// two details: 
// * fix precedences to avoid parentheses?
// * integers type inference fails when swapping the arguments 
*) 

module HS = FStar.HyperStack

// 18-09-22 Avoid those, too specific?
module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap



/// Global, ideal memory

inline_for_extraction 
let model = Flags.model 

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
// TODO aseem: pls use library abbreviations

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

let tls_region: tls_rgn = new_colored_region HS.root tls_color 

type subtls = r: subrgn tls_region {is_tls_rgn r} 

noextract
private let p :
  r0:subtls &
  r1:subtls &
  r2:subtls
  {r1 `disjoint` r0 /\ r2 `disjoint` r0 /\ r2 `disjoint` r1} =
  let r0 = new_colored_region tls_region tls_color in
  let r1 = new_colored_region tls_region tls_color in
  let r2 = new_colored_region tls_region tls_color in
  (| r0, r1, r2 |)

// consider dropping the tls_ prefix
noextract
let tls_tables_region: r:tls_rgn =
  match p with | (| r, _, _ |) -> r

noextract
let tls_define_region: r:tls_rgn{r `disjoint` tls_tables_region} =
  match p with | (| _, r, _ |) -> r

noextract
let tls_honest_region: r:tls_rgn{r `disjoint` tls_tables_region /\ r `disjoint` tls_define_region} =
  match p with | (| _, _, r |) -> r


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

let loc_in (l: M.loc) (h: HS.mem) =
  M.loc_not_unused_in h `M.loc_includes` l

let loc_unused_in (l: M.loc) (h: HS.mem) =
  M.loc_unused_in h `M.loc_includes` l

let fresh_loc (l: M.loc) (h0 h1: HS.mem) =
  loc_unused_in l h0 /\ loc_in l h1

let fresh_is_disjoint (old_loc:M.loc) (new_loc:M.loc)
  (h0 h1:HS.mem) : Lemma
  (requires (fresh_loc new_loc h0 h1 /\ old_loc `loc_in` h0))
  (ensures (M.loc_disjoint old_loc new_loc))
  = ()

type sub_loc (parent:M.loc) =
  l:M.loc{if model then M.loc_includes parent l else l == M.loc_none}
