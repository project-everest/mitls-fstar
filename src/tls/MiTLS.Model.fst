module MiTLS.Model
open MiTLS

open MiTLS.Mem
open MiTLS.Idx

module M = LowStar.Modifies
module HS = FStar.HyperStack
open FStar.HyperStack.ST

(**
This module provides convenience abbrevation
for model-conditional types, i.e. types that
are simplified when model is off. The scaffolding
step between model off (i.e. concrete) and model
on (i.e. real, then ideal) must be justified by
a functional correctness argument.
**)

(** When model is on, instances are either ideal or real **)
noextract
type ideal_or_real (it:Type0) (rt:Type0) =
  | Ideal: v:it -> ideal_or_real it rt
  | Real: v:rt -> ideal_or_real it rt

(** Type used during extraction, erases the Ideal/Real tag and uses the real type **)
inline_for_extraction noextract
type ir (safe: (i:regid -> GTot Type0)) (it:squash model -> Type0) (rt:Type0) (i:regid) =
  (if model then s:ideal_or_real (it ()) rt{safe i <==> Ideal? s} else rt)

noextract
let model_on (#safe:(i:regid -> GTot Type0)) (#it:squash model -> Type0)
  (#rt:Type0) (#i:regid) (k:ir safe it rt i) (u:squash model)
  : Pure (ideal_or_real (it ()) rt)
  (requires model) (ensures fun x -> safe i <==> Ideal? x) =
  let x:ideal_or_real (it ()) rt = k in x

noextract
let ideal (#safe:(i:regid -> GTot Type0)) (#it:squash model -> Type0)
  (#rt:Type0) (#i:regid) (k:ir safe it rt i) (u:squash model)
  : Pure (it u) (requires safe i) (ensures fun _ -> True) =
  let x:ideal_or_real (it ()) rt = k in
  Ideal?.v x

inline_for_extraction noextract
let real (#safe:(i:regid -> GTot Type0)) (#it:squash model -> Type0)
  (#rt:Type0) (#i:regid) (k:ir safe it rt i)
  : Pure rt (requires model ==> ~(safe i)) (ensures fun _ -> True) =
  if model then
    let x:ideal_or_real (it ()) rt = k in
    Real?.v x
  else k

noextract
let mk_ideal (#safe:(i:regid -> GTot Type0)) (#it:squash model -> Type0)
  (#rt:Type0) (#i:regid) (#u:squash model) (v:it u)
  : Pure (ir safe it rt i) (requires safe i) (ensures fun _ -> True) =
  let x : ideal_or_real (it ()) rt = Ideal v in x

inline_for_extraction noextract
let mk_real (#safe:(i:regid -> GTot Type0)) (#it:squash model -> Type0)
  (#rt:Type0) (#i:regid) (v:rt)
  : Pure (ir safe it rt i) (requires model ==> ~(safe i)) (ensures fun _ -> True) =
  if model then
    let x : ideal_or_real (it ()) rt = Real v in x
  else v

inline_for_extraction noextract
let is_safe (#safe:(i:regid -> GTot Type0)) (#it:squash model -> Type0)
  (#rt:Type0) (#i:regid) (k:ir safe it rt i)
  : Pure bool (requires True) (ensures fun b -> model ==> (b <==> safe i)) =
  if model then Ideal? (model_on k ())
  else false
