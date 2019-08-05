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

friend Lib.IntTypes // because Spec.uint8 is a secret integer type but miTLS is using FStar UInt8

noextract
inline_for_extraction
let entry (a: SC.supported_alg): Tot eqtype =
  [@inline_let]
  let t = SC.iv a in
  t

let table
  (a: SC.supported_alg)
  (kv: SC.kv a)
  (phi: plain_pred)
: Tot Type0
= MDM.t HS.root (entry a) (fun iv -> (plain: SC.plain a { phi plain })) (fun _ -> True)

noeq
type state (a: SC.supported_alg) (phi: plain_pred) = {
  kv: SC.kv a;
  table: (if F.ideal_AEAD then table a kv phi else unit)
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
  (requires (Flags.ideal_AEAD == true))
  (ensures (fun _ -> True))
= s.table <: table a (state_kv s) phi

let invariant (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0 =
  if F.ideal_AEAD
  then
    h `HS.contains` state_table s
  else
    True

let footprint
  #a #phi s
= if F.ideal_AEAD
  then
    B.loc_mreference (state_table s)
  else
    B.loc_none

let frame_invariant
  #a #phi h s l h'
= if F.ideal_AEAD
  then
    B.modifies_mreference_elim (state_table s) l h h' // FIXME: WHY WHY WHY do I need to call this lemma by hand?
  else
    ()

let encrypt
  #a #phi s iv plain
= if F.ideal_AEAD
  then begin
    let h = HST.get () in
    let tbl = state_table s in
    assume (~ (MDM.defined tbl iv h)); // cryptographic assumption
    MDM.extend tbl iv plain;
    let h' = HST.get () in
    B.modifies_loc_regions_intro (Set.singleton (HS.frameOf tbl)) h h' ;
    B.modifies_loc_addresses_intro (HS.frameOf tbl) (Set.singleton (HS.as_addr tbl)) B.loc_none h h' ;
    Seq.create (SC.cipher_length plain) 0uy
  end else
    SC.encrypt (state_kv s) iv Seq.empty plain

let decrypt
  #a #phi s iv cipher
= if F.ideal_AEAD
  then begin
    match MDM.lookup (state_table s) iv with
    | None -> None
    | Some plain -> Some plain
  end else
    match SC.decrypt (state_kv s) iv Seq.empty cipher with
    | None -> None
    | Some plain -> Some plain
