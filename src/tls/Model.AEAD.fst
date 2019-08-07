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

noextract
inline_for_extraction
let entry (a: SC.supported_alg): Tot eqtype =
  [@inline_let]
  let t = SC.iv a in
  Crypto.Util.IntCast.seq_sec8_has_eq ();
  t

let table
  (a: SC.supported_alg)
  (kv: SC.kv a)
  (phi: plain_pred)
: Tot Type0
= MDM.t HS.root (entry a) (fun iv -> (cipher: SC.cipher a & (plain: SC.decrypted cipher { phi plain }))) (fun _ -> True)

noeq
type state (a: SC.supported_alg) (phi: plain_pred) = {
  kv: SC.kv a;
  table: (if F.ideal_iv then table a kv phi else unit)
}

let state_kv
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi)
: Tot (SC.kv a)
= s.kv

let state_table
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi)
: Pure (table a (state_kv s) phi)
  (requires (Flags.ideal_iv == true))
  (ensures (fun _ -> True))
= s.table <: table a (state_kv s) phi

let invariant (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0 =
  if F.ideal_iv
  then
    h `HS.contains` state_table s
  else
    True

let footprint
  #a #phi s
= if F.ideal_iv
  then
    B.loc_mreference (state_table s)
  else
    B.loc_none

let invariant_loc_in_footprint
  #a #phi h s
= ()

let frame_invariant
  #a #phi h s l h'
= if F.ideal_iv
  then
    B.modifies_mreference_elim (state_table s) l h h' // FIXME: WHY WHY WHY do I need to call this lemma by hand?
  else
    ()

let fresh_iv
  #a #phi h s iv
= F.ideal_iv == true ==> MDM.fresh (state_table s) iv h

let frame_fresh_iv
  #a #phi h s iv l h'
= ()

let is_fresh_iv
  #a #phi s iv
= None? (MDM.lookup (state_table s) iv)

let encrypt
  #a #phi s iv plain
= let plain' = if F.ideal_AEAD then Seq.create (Seq.length plain) (Crypto.Util.IntCast.to_sec8 0uy) else plain in
  let cipher = SC.encrypt (state_kv s) iv Seq.empty plain' in
  if F.ideal_iv
  then begin
    let h = HST.get () in
    let tbl = state_table s in
    MDM.extend tbl iv (| cipher, plain |);
    let h' = HST.get () in
    B.modifies_loc_regions_intro (Set.singleton (HS.frameOf tbl)) h h' ;
    B.modifies_loc_addresses_intro (HS.frameOf tbl) (Set.singleton (HS.as_addr tbl)) B.loc_none h h' ;
    assume (HST.equal_domains h h') // TODO: fix FStar.Monotonic.DependentMap
  end;
  cipher

let decrypt
  #a #phi s iv cipher
= if F.ideal_AEAD
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
