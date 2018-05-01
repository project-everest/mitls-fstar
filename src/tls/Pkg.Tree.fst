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

(* ADL: the following crashes F*
noeq type tree' (par_ideal:Type0) =
  | Leaf: package:t{Pkg?.ideal package ==> par_ideal} -> tree' par_ideal
  | Node: node:t{Pkg?.ideal node ==> par_ideal} -> children: children (Pkg?.ideal node) -> tree' par_ideal
and children (par_ideal:Type0) = list (label * tree' par_ideal)
*)

// The `[@ Gc]` attribute instructs Kremlin to translate the `pre_id` field as a pointer,
// otherwise it would generate an invalid type definition.
[@ Gc]
noeq type tree' =
  | Leaf: package:t -> tree'
  | Node: node:t -> children:children' -> tree'
and children' = list (label * tree')
// MK: would it simplify things to remove Leaf and use a Node with an empty children list to represent leaves? 


// would prefer to use Map.t, but positivity check fails

let max x y = if x <= y then y else x

#reset-options "--admit_smt_queries true"

// induction on n-ary trees requires explicit termination
let rec depth (x:tree') : nat =
  match x with
  | Leaf _ -> 0
  | Node _ lxs -> 1 + children_depth lxs
and children_depth (lxs:children') : nat  =
  match lxs with
  | (_,x) :: lxs -> max (depth x) (children_depth lxs)
  | [] -> 0

let valid_child ideal_parent (p:t) = Pkg?.ideal p ==> ideal_parent
val valid_tree: ideal_parent:Type0 -> t:tree' -> Tot Type0 (decreases %[t; 0])
val valid_children: ideal_parent:Type0 -> c:children' -> Tot Type0 (decreases %[c; 1])

let rec valid_tree par = function
  | Leaf p -> valid_child par p
  | Node p c -> valid_child par p /\ valid_children (Pkg?.ideal p) c
and valid_children par = function
  | [] -> True
  | (_, t)::tl -> valid_tree par t /\ valid_children par tl

// p is a property implied by the ideal flags in all sub-packages
// at the root one may use e.g. model or True
type tree (p:Type0) = t:tree'{valid_tree p t}
type children (p:Type0) = c:children'{valid_children p c}

let rec find_lbl (#p:Type0) (u:children p) (l: label) : option (tree p) =
  match u with
  | [] -> None
  | (lbl, t) :: tl ->
    if lbl = l then Some t
    else
      let tl : children p = tl in
      find_lbl tl l

let has_lbl (#p:Type0) (u:children p) (l: label) = Some? (find_lbl u l)

let down (#p:Type0) (u:children p) (l:label{u `has_lbl` l}) : tree p
  = Some?.v (find_lbl u l)

let child (#p:Type0) (u:children p) (l:label{u `has_lbl` l})
  : pkg:t{Pkg?.ideal pkg ==> p}
  =
  match down u l  with
  | Leaf p -> p
  | Node p c -> p
