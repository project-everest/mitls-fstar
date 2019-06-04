module Pkg.Tree

open Mem
open Pkg
open Idx

module M = LowStar.Modifies
module DT = DefineTable

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

inline_for_extraction noextract
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

// Used to start building children
inline_for_extraction noextract
let no_children (p:Type0) : children p =
  (if model then [] <: children' p else erased_tree)

inline_for_extraction
let rec find_lbl' (#p:Type0) (u:children' p) (l: label) : option (tree' p) =
  match u with
  | [] -> None
  | (lbl, t) :: tl ->
    if lbl = l then Some t
    else find_lbl' tl l

noextract
let rec find_lbl (#p:Type0) (u:children p) (l:label) : option (tree p) =
  if model then find_lbl' (u <: children' p) l else None

inline_for_extraction
let has_lbl' (#p:Type0) (u:children' p) (l: label) =
  Some? (find_lbl' u l)

inline_for_extraction
let has_lbl (#p:Type0) (u:children p) (l: label) =
  if model then (u <: children' p) `has_lbl'` l else false

noextract
let down' (#p:Type0) (u:children' p) (l:label{u `has_lbl'` l}) : tree' p =
  Some?.v (find_lbl' u l)

noextract
let down (#p:Type0) (u:children p) (l:label{u `has_lbl` l}) : tree p =
  Some?.v (find_lbl u l)

noextract
let child (#p:Type0) (u:children' p) (l:label{u `has_lbl'` l})
  : pkg:t{Pkg?.ideal pkg ==> p}
  =
  let x : tree' p = down' u l in
  match x with
  | Leaf p -> p
  | Node p c -> p

type initial_state (#p:Type0) (pkg:t{Pkg?.ideal pkg ==> p}) (h:mem) =
  DT.empty (Pkg?.define_table pkg)

(**** Tree invariant ****)

(*

The structure of indexes defined in each package of the tree
follows the structure of the tree itself:

      KDF   package invariant = children invariant of usage
     / | \
    a  b  c   derivation labels
   /   |   \
[ X    Y    Z ] children (KDF usage)
           / \

if (x i) is an instance of package X, then i must be of the
form Derive j a ctx where j is defined in KDF.

Furthermore, the invariant of a node pacakge implies the
invariant of every descendent package.
*)

let regid : eqtype = i:ii.t{ii.registered i}

val tree_inv': #p:Type0 -> t:tree' p -> mem ->
  Ghost Type0 (requires model) (ensures fun _ -> True) (decreases %[t])
val children_inv': #vt:(regid->Type) -> DT.dt vt -> #p:Type0 -> u:children' p -> mem ->
  Ghost Type0 (requires model) (ensures fun _ -> True) (decreases %[u])

let child_instance_inv (#vt:regid->Type) (parent_dt:DT.dt vt)
  (lbl:label) (#kt:regid->Type) (#i:regid) (k:kt i) (h:mem)
  : Ghost Type0 (requires model) (ensures fun _ -> True) =
  let i : pre_id = i in
  match i  with
  | Preshared _ _ -> False
  | Derive j lbl' ctx -> lbl == lbl' /\
    registered j /\ DT.defined parent_dt j

let rec tree_inv' #p t h =
  match t with
  | Leaf p -> Pkg?.package_invariant p h
  | Node p u -> Pkg?.package_invariant p h /\
    children_inv' p.define_table u h

and children_inv' #vt parent_dt #p u h =
  match u with
  | [] -> True
  | (lbl,x)::tl ->
    let pkg = match x with Leaf p -> p | Node p _ -> p in
    tree_inv' x h /\ children_inv' parent_dt tl h /\
    M.loc_disjoint (DT.loc parent_dt) (DT.loc pkg.define_table) /\
    DT.dt_forall pkg.define_table (child_instance_inv parent_dt lbl) h

let tree_inv (#p:Type0) (t:tree p) (h:mem) =
  (if model then tree_inv' (t <: tree' p) h else True)

let children_inv #vt (dt:DT.dt vt) (#p:Type0) (t:children p) (h:mem) =
  (if model then children_inv' dt (t <: children' p) h else True)

noextract
let rec labels_of_id (i:pre_id) (acc:list label) =
  match i with
  | Preshared a pski -> acc
  | Derive i l ctx -> labels_of_id i (l::acc)

(*
let x : label = assume false; "x"
let y : label = assume false; "y"
let _ = assert_norm (labels_of_id (Derive(Derive (Preshared Hashing.Spec.SHA1 0) x Extract) y Extract) [] == [x; y])
*)

let rec subtree (#p:Type0) (t:tree' p)
  (#q:Type0) (c:children' q) (l:list label)
  : Pure Type (requires model) (ensures fun _ -> True) (decreases %[l])
  =
  Node? t /\
  (match l with
  | [] -> q == Pkg?.ideal (Node?.node t) /\ Node?.children t == c
  | lbl::tl ->
    let c' = Node?.children t in
    c' `has_lbl'` lbl /\
    subtree (down' c' lbl) c tl)

let rec defined_path (#p:Type0) (t:tree' p) (l:list label)
  : GTot Type (decreases %[l]) =
  match t with
  | Leaf _ -> l == []
  | Node p c ->
    match l with
    | [] -> False
    | lbl::tl -> c `has_lbl'` lbl /\ defined_path (down' c lbl) tl

let rec get_package (#p:Type0) (t:tree' p) (l:list label{defined_path t l})
  : GTot (pkg ii) (decreases %[l]) =
  match t with
  | Leaf p -> p
  | Node p c ->
    match l with
    | lbl :: tl -> get_package (down' c lbl) tl

let rec get_usage (#p:Type0) (t:tree' p) (l:list label{defined_path t l})
  : GTot (p:Type0 & children' p) (decreases %[l]) =
  match t with
  | Leaf p -> (| Pkg?.ideal p, ([] <: children' (Pkg?.ideal p)) |)
  | Node pkg c ->
    match l with
    | [] -> (| p, c |)
    | lbl :: tl -> get_usage (down' c lbl) tl

let defined' (#p:Type0) (t:tree' p) (i:regid{model}) =
  let path = labels_of_id i [] in
  defined_path t path /\
  (let pkg = get_package t path in
  DT.defined pkg.define_table i)

let defined (#p:Type0) (t:tree p) (i:regid) =
  if model then defined' (t <: tree' p) i else True

val lemma_derive_children:
  #vt: (regid->Type) ->
  dt: DT.dt vt ->
  #p: Type0 ->
  u: children' p ->
  i: regid{DT.defined dt i} ->
  lbl: label{u `has_lbl'` lbl} ->
  ctx: context{wellformed_derive i lbl ctx /\ registered (derive i lbl ctx)} ->
  k: Pkg?.key (child u lbl) (derive i lbl ctx) ->
  h0:mem -> h1:mem ->
  Lemma (requires model /\ children_inv' dt u h0 /\
    DT.extended (child u lbl).define_table k h0 h1 /\
    (child u lbl).package_invariant h1)
  (ensures children_inv' dt u h1)
  (decreases %[u])

val lemma_derive_tree:
  #p: Type0 ->
  t: tree' p ->
  h0:mem -> l:M.loc -> h1:mem ->
  Lemma (requires model /\ tree_inv' t h0 /\ M.modifies l h0 h1 /\
    M.loc_disjoint l l)
  (ensures tree_inv' t h1)
  (decreases %[t])

(*
// Local subtree invariant restoration
let rec lemma_derive 
  =
  match u with
  | [] -> ()
  | (lbl', t) :: tl ->
    if lbl = lbl' then
     begin
      lemma_
     end
    else lemma_derive dt tl i lbl ctx k h0 h1
  
  let rec aux
    : Lemma ()
    =
    admit()
    in
  admit()
*)

(*
Building the tree is quite technical because the tree
invariant must be initialized (which requires the define
table of the parent to be allocated before children can be
defined.

We provide stateful helper functions to help construct trees
*)

