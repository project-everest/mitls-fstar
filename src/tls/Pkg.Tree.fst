module Pkg.Tree

open Mem
open Pkg
open Idx

/// We use subtrees to specify KDF usages. We hope we can erase
/// them when modelling is off!
///
/// This module is generic, and could be made parametric in its index
/// package. The TLS-specific details are filled-in in KeySchedule.

type t = pkg ii

noeq noextract
type tree' (par_ideal:Type0) =
  | Leaf: package:t{Pkg?.ideal package ==> par_ideal} -> tree' par_ideal
  | Node: node:t{Pkg?.ideal node ==> par_ideal} -> children: children' (Pkg?.ideal node) -> tree' par_ideal
and children' (par_ideal:Type0) = list (label * tree' par_ideal)

// would prefer to use Map.t, but positivity check fails

inline_for_extraction
let max x y = if x <= y then y else x

// induction on n-ary trees requires explicit termination
noextract
let rec depth (#p:Type0) (x:tree' p) : nat =
  match x with
  | Leaf _ -> 0
  | Node _ lxs -> 1 + children_depth lxs
and children_depth (#p:Type0) (lxs:children' p) : nat  =
  match lxs with
  | (_,x) :: lxs -> max (depth x) (children_depth lxs)
  | [] -> 0

inline_for_extraction
let no_tree : Type u#1 = a:Type u#0 -> GTot unit
inline_for_extraction
let erased_tree : no_tree = fun (_:Type0) -> ()

type tree (p:Type0) =
  (if model then tree' p else no_tree)

type children (p:Type0) =
  (if model then children' p else no_tree)

inline_for_extraction
let rec find_lbl (#p:Type0) (u:children p) (l: label) : option (tree p) =
  if not model then None else
  let u' : children' p = u in
  match u' with
  | [] -> None
  | (lbl, t) :: tl ->
    if lbl = l then Some t
    else
      let tl : children p = tl in
      find_lbl tl l

inline_for_extraction
let has_lbl (#p:Type0) (u:children p) (l: label) =
  if model then Some? (find_lbl u l) else false

noextract
let down (#p:Type0) (u:children p) (l:label{u `has_lbl` l}) : tree p =
  Some?.v (find_lbl u l)

noextract
let child (#p:Type0) (u:children p) (l:label{model /\ u `has_lbl` l})
  : pkg:t{Pkg?.ideal pkg ==> p}
  =
  let x : tree' p = down u l in
  match x with
  | Leaf p -> p
  | Node p c -> p
