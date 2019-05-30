module Pkg.Tree

open Mem
open Pkg
open Idx

/// When modelling is on, we specify the (bounded, recursive) usage of
/// a KDF as a tree of derived packages.
///
/// This module is generic, and could be made parametric in its index
/// package. The TLS-specific details are filled-in in KeySchedule.

type t = pkg ii

/// Structural tree property: we idealize from the top, hence a child
/// can be ideal only if its parent is ideal.

noeq noextract
type tree' (ideal_parent:Type0) =
  | Leaf: package:t{Pkg?.ideal package ==> ideal_parent} -> tree' ideal_parent
  | Node: node:t{Pkg?.ideal node ==> ideal_parent} -> children: children' (Pkg?.ideal node) -> tree' ideal_parent
and children' (ideal_parent:Type0) = list (label * tree' ideal_parent)

// would prefer to use Map.t, but positivity check fails

inline_for_extraction
let max x y = if x <= y then y else x

/// induction on n-ary trees requires explicit termination based on their depths

noextract
let rec depth (#p:Type0) (x:tree' p) : nat =
  match x with
  | Leaf _ -> 0
  | Node _ lxs -> 1 + children_depth lxs
and children_depth (#p:Type0) (lxs:children' p) : nat  =
  match lxs with
  | (_,x) :: lxs -> max (depth x) (children_depth lxs)
  | [] -> 0

/// Eliding trees when model is off

inline_for_extraction
let no_tree : Type u#1 = a:Type u#0 -> GTot unit
inline_for_extraction
let erased_tree : no_tree = fun (_:Type0) -> ()

type tree (p:Type0) =
  (if model then tree' p else no_tree)

type children (p:Type0) =
  (if model then children' p else no_tree)

/// Package lookup based on the derivation label

inline_for_extraction
let rec find_lbl (#p:Type0) (u:children p) (l: label) : option (tree p) =
  if not model then None else
  let u' = u <: children' p in
  match u' with
  | [] -> None
  | (lbl, t) :: tl ->
    if lbl = l then Some t
    else
      find_lbl tl l

inline_for_extraction
let has_lbl (#p:Type0) (u:children p) (l: label) =
  if model then Some? (find_lbl u l) else false

noextract
let down (#p:Type0) (u:children p) (l:label{u `has_lbl` l}) : tree p =
  Some?.v (find_lbl u l)

noextract
let child 
  (#p:Type0) (u:children p) 
  (l:label{model /\ u `has_lbl` l}) : pkg:t{Pkg?.ideal pkg ==> p}
  =
  let x = down u l <: tree' p in
  match x with
  | Leaf p -> p
  | Node p c -> p
