module Model.AEAD

module U8 = FStar.UInt8
module Seq = FStar.Seq
module SC = Spec.AEAD
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module G = FStar.Ghost
module F = Flags
module B = LowStar.Buffer
module MDM = FStar.Monotonic.DependentMap

open Declassify

noextract
inline_for_extraction
let entry_key (a: SC.supported_alg): Tot eqtype =
  SC.iv a

noextract
inline_for_extraction
let entry_value
  (a: SC.supported_alg)
  (phi: plain_pred)
  (iv: entry_key a)
: Tot Type0
= (cipher: SC.cipher a & (plain: SC.decrypted cipher { phi plain }))

noextract
inline_for_extraction
let table_inv
  (a: SC.supported_alg)
  (phi: plain_pred)
  (map: FStar.DependentMap.t (entry_key a) (MDM.opt (entry_value a phi)))
: Tot Type0
= True

let table
  (r: HST.erid)
  (a: SC.supported_alg)
  (phi: plain_pred)
: Tot Type0
= MDM.t r (entry_key a) (entry_value a phi) (table_inv a phi)

noeq
type state (a: SC.supported_alg) (phi: plain_pred) = {
  kv: SC.kv a;
  region: (if F.ideal_iv then HST.erid else unit);
  table: (if F.ideal_iv then table (region <: HST.erid) a phi else unit)
}

let state_kv
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi)
: Tot (SC.kv a)
= s.kv

let state_region
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi {Flags.ideal_iv == true} )
: Tot HST.erid
= s.region

let state_table
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi {Flags.ideal_iv == true})
: Tot (table (state_region s) a phi)
= s.table <: table (state_region s) a phi

let invariant (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0 =
  if F.ideal_iv
  then
    h `HS.contains` state_table s
  else
    True

let footprint #a #phi s = 
  if F.ideal_iv
  then
    B.loc_freed_mreference (state_table s)
  else
    B.loc_none

let invariant_loc_in_footprint #a #phi h s = ()

let frame_invariant #a #phi h s l h' = ()

let fresh_iv #a #phi h s iv = 
  F.ideal_iv == true ==> MDM.fresh (state_table s) iv h

let frame_fresh_iv #a #phi h s iv l h' = ()

let is_fresh_iv #a #phi s iv = 
  None? (MDM.lookup (state_table s) iv)

let encrypt #a #phi s iv plain = 
  let plain' = if F.ideal_AEAD then Seq.create (Seq.length plain) 0uy else plain in
  let cipher = SC.encrypt (state_kv s) iv Seq.empty plain' in
  if F.ideal_iv
  then begin
    let h = HST.get () in
    let tbl = state_table s in
    MDM.extend tbl iv (| cipher, plain |);
    let h' = HST.get () in
    B.modifies_loc_regions_intro (Set.singleton (HS.frameOf tbl)) h h' ;
    B.modifies_loc_addresses_intro (HS.frameOf tbl) (Set.singleton (HS.as_addr tbl)) B.loc_none h h'
  end;
  cipher

let decrypt #a #phi s iv cipher = 
  if F.ideal_AEAD
  then begin
    match MDM.lookup (state_table s) iv with
    | None -> None
    | Some (| cipher' , plain |) ->
      if cipher = cipher'
      then Some plain
      else None
  end else
    match SC.decrypt (state_kv s) iv Seq.empty cipher with
    | None -> None
    | Some plain -> Some plain

let create r #a k phi = 
  if F.ideal_iv
  then begin
    HST.recall_region r;
    HST.witness_region r;
    let tbl : table r a phi = MDM.alloc #(entry_key a) #(entry_value a phi) #(table_inv a phi) #r () in
    {kv = k; region = r; table = tbl}
  end else
    {kv = k; region = (); table = ()}

let free #a #phi s = 
  () // we cannot rfree the table, because it is not mm
