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
/// (why do we need a subregion for tables?)
/// 
let tls_region: tls_rgn = new_colored_region HH.root tls_color

let tls_tables_region: subrgn tls_region =
  new_region tls_region

// to be reviewed
let honest_region: subrgn tls_region = 
  new_region tls_region
