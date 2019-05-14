module DefineTable

open Mem

module M = LowStar.Modifies
module DM = FStar.DependentMap
module MDM = FStar.Monotonic.DependentMap
module MH = FStar.Monotonic.Heap
module HS = FStar.HyperStack

(*
Define tables are a core feature of the cryptographic model.

Their purpose is to record the creation of instances of a
packaged functionality, and memoize the created instances
to guarantee that instances are unique for a given index.

Whenever possible, we try to sepaate the state of functionalities
by instance (see LocalPkg). In that case, the invariant and
footprint for the collection of instances can be managed entirely
based on the define table. This requires some specialization
over FStar.Monotonic.DependentMap, in particular to compute
and reason about joint footprints and invariants.
*)

type table (#it:eqtype) (vt: it -> Type) =
  MDM.t tls_define_region it vt (fun _ -> True)

inline_for_extraction type dt (#it:eqtype) (vt:it->Type) =
  (if model then table vt else unit)

let ideal (#it:eqtype) (#vt:it->Type) (t:dt vt) : Pure (table vt)
  (requires model) (ensures fun _ -> True) = t

let real (#it:eqtype) (#vt:it->Type) (t:dt vt) : Pure unit
  (requires not model) (ensures fun _ -> True) = t

let loc (#it:eqtype) (#vt:it->Type) (t:dt vt) =
  (if model then M.loc_mreference (ideal t) else M.loc_none)

type live (#it:eqtype) (#vt:it -> Type) (t:dt vt) (h:mem) =
  (model ==> h `HS.contains` (ideal t))

type fresh (#it:eqtype) (#vt:it -> Type) (t:dt vt) (i:it) (h:mem) =
  (model ==> MDM.fresh (ideal t) i h)

let lemma_fresh_frame (#it:eqtype) (#vt:it -> Type) (t:dt vt) (i:it)
  (h0:mem) (l:M.loc) (h1:mem) : Lemma
  (requires fresh t i h0 /\ M.modifies l h0 h1 /\
    M.loc_disjoint l (loc t) /\ live t h0)
  (ensures fresh t i h1) = ()

type defined_as (#it:eqtype) (#vt:it -> Type) (t:dt vt) (i:it) (k:vt i) (h:mem) =
  model ==> (MDM.sel (HS.sel h (ideal t)) i == Some k)

type defined (#it:eqtype) (#vt:it -> Type) (t:dt vt) (i:it) =
  model ==> witnessed (MDM.defined (ideal t) i)

type extended (#it:eqtype) (#vt:it -> Type) (t:dt vt)
  (i:it) (v:vt i) (h0 h1:mem) =
  (if model then
    M.modifies (loc t) h0 h1 /\
    MDM.fresh (ideal t) i h0 /\
    MDM.defined (ideal t) i h1 /\
    HS.sel h1 (ideal t) == MDM.upd (HS.sel h0 (ideal t)) i v
  else M.modifies M.loc_none h0 h1)

type unchanged (#it:eqtype) (#vt:it -> Type) (t:dt vt) (h0 h1:mem) =
  model ==> HS.sel h0 (ideal t) == HS.sel h1 (ideal t)

let lemma_unchanged_frame (#it:eqtype) (#vt:it -> Type) (t:dt vt)
  (h0:mem) (l:M.loc) (h1:mem) : Lemma
  (requires M.modifies l h0 h1 /\ live t h0 /\ M.loc_disjoint l (loc t))
  (ensures unchanged t h0 h1) = ()

type empty (#it:eqtype) (#vt:it -> Type) (t:dt vt) (h1:mem) =
  model ==> HS.sel h1 (ideal t) == MDM.empty

type disjoint (#it:eqtype) (#vt:it -> Type) (t:dt vt)
  (#it':eqtype) (#vt':it' -> Type) (t':dt vt') =
  M.loc_disjoint (loc t) (loc t')

let lemma_disjoint_unchanged (#it:eqtype) (#vt:it -> Type) (t:dt vt)
  (#it':eqtype) (#vt':it' -> Type) (t':dt vt') (h0:mem) (h1:mem) : Lemma
  (requires M.modifies (loc t) h0 h1 /\ disjoint t t' /\
    live t h0 /\ live t' h0)
  (ensures unchanged t' h0 h1) = ()

val alloc:
  #it:eqtype ->
  vt: (it -> Type) ->
  ST (dt vt)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> M.modifies M.loc_none h0 h1 /\
    empty t h1 /\ fresh_loc (loc t) h0 h1)

val extend:
  #it:eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  i: it ->
  k: vt i ->
  ST unit
  (requires fun h0 -> fresh t i h0)
  (ensures fun h0 () h1 -> extended t i k h0 h1)

(* Used to define a joint invariant over all defined instances
The definition is opaque but the lemmas below are enough to use
and extend the joint invariant in the memoization functor *)
val dt_forall:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  pred: (#i:it -> vt i -> mem -> GTot Type0) ->
  h: mem ->
  Type0

type local_fp (#it:eqtype) (vt:it->Type) (parent:M.loc) =
  #i:it -> vt i -> sub_loc parent

// Package footprint = union of all instance footprints
val footprint:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  #parent: M.loc ->
  fp: local_fp vt parent ->
  h: mem ->
  GTot (sub_loc parent)

val lemma_footprint_frame:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  #parent: M.loc ->
  fp: local_fp vt parent ->
  h0: mem ->
  h1: mem ->
  Lemma
    (requires unchanged t h0 h1)
    (ensures footprint t fp h0 == footprint t fp h1)

val lemma_footprint_extend: 
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  #parent: M.loc ->
  fp: local_fp vt parent ->
  i: it ->
  k: vt i ->
  h0: mem ->
  h1: mem ->
  Lemma
    (requires extended t i k h0 h1)
    (ensures footprint t fp h1 == M.loc_union (footprint t fp h0) (fp k))

val lemma_footprint_includes:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  #parent: M.loc ->
  fp: local_fp vt parent ->
  i: it ->
  k: vt i ->
  h: mem ->
  Lemma
    (requires defined_as t i k h)
    (ensures (footprint t fp h) `M.loc_includes` (fp k))

val lemma_forall_empty:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  pred: (#i:it -> vt i -> mem -> GTot Type0) ->
  h: mem ->
  Lemma 
    (requires empty t h)
    (ensures dt_forall t pred h)

val lemma_forall_elim:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  pred: (#i:it -> vt i -> mem -> GTot Type0) ->
  i: it -> k: vt i ->
  h: mem ->
  Lemma
    (requires dt_forall t pred h /\ model)
    (ensures defined_as t i k h ==> pred k h)

val lemma_forall_extend:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  pred: (#i:it -> vt i -> mem -> GTot Type0) ->
  #parent: M.loc ->
  fp: local_fp vt parent ->
  pred_frame: (#i:it -> k:vt i -> h0:mem -> l:M.loc -> h1:mem -> Lemma
    (requires pred k h0 /\ M.modifies l h0 h1 /\ M.loc_disjoint l (fp k))
    (ensures pred k h1)) ->
  #i: it -> k: vt i ->
  h0: mem -> h1: mem ->
  Lemma
    (requires dt_forall t pred h0 /\ extended t i k h0 h1 /\
      pred k h1 /\ M.loc_disjoint (loc t) parent)
    (ensures dt_forall t pred h1)

val lemma_forall_frame:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  pred: (#i:it -> vt i -> mem -> GTot Type0) ->
  #parent: M.loc ->
  fp: local_fp vt parent ->
  pred_frame: (#i:it -> k:vt i -> h0:mem -> l:M.loc -> h1:mem -> Lemma
    (requires pred k h0 /\ M.modifies l h0 h1 /\ M.loc_disjoint l (fp k))
    (ensures pred k h1)) ->
  h0: mem -> l:M.loc -> h1: mem ->
  Lemma
    (requires dt_forall t pred h0
      /\ M.modifies l h0 h1 /\ t `live` h0
      /\ M.loc_disjoint l (loc t) /\ M.loc_disjoint l (footprint t fp h0))
    (ensures dt_forall t pred h1)

(*
val dt_fold:
  #it: eqtype ->
  #vt: (it -> Type) ->
  t: dt vt ->
  #rt: Type ->
  init: rt ->
  f: (rt -> i:it -> vt i -> rt) ->
  h: mem ->
  GTot rt
*)
