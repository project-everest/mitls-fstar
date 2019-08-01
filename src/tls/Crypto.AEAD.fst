module Crypto.AEAD

module U8 = FStar.UInt8
module Seq = FStar.Seq
module EC = EverCrypt.AEAD
module SC = Spec.AEAD
module B = LowStar.Buffer
module E = EverCrypt
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module EE = EverCrypt.Error
module G = FStar.Ghost
module MDM = FStar.Monotonic.DependentMap
module F = Flags

noextract
inline_for_extraction
let entry (a: SC.supported_alg): Tot eqtype =
  [@inline_let]
  let t = SC.iv a & SC.cipher a in
  assume (hasEq t);
  t

inline_for_extraction
let table
  (a: SC.supported_alg)
  (kv: SC.kv a)
  (phi: plain_pred)
: Tot Type0
= MDM.t HS.root (entry a) (fun (iv, cipher) -> (plain: SC.plain a { phi plain /\ SC.encrypt kv iv Seq.empty plain == cipher })) (fun _ -> True)

noeq
type state (a: SC.supported_alg) (phi: plain_pred) = {
  ec: (if F.model then unit else B.pointer (EC.state_s a));
  kv: (if F.model then SC.kv a else G.erased (SC.kv a));
  table: (if F.ideal_AEAD then table a kv phi else unit)
}

inline_for_extraction
let state_ec
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi { F.model == false })
: Tot (B.pointer (EC.state_s a))
= s.ec

let state_kv
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi)
: GTot (SC.kv a)
= if F.model then s.kv else G.reveal s.kv

let invariant (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0 =
  if F.model
  then
    if F.ideal_AEAD
    then
      h `HS.contains` (s.table <: table a s.kv phi)
    else
      True
  else
    EC.invariant h (state_ec s) /\
    EC.as_kv (B.deref h (state_ec s)) == state_kv s

let footprint (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot B.loc =
  if F.model
  then
    if F.ideal_AEAD
    then
      B.loc_mreference (s.table <: table a (s.kv) phi)
    else
      B.loc_none
  else
    EC.footprint h (state_ec s)

let frame_invariant
  #a #phi h s l h'
= if F.model
  then
    if F.ideal_AEAD
    then assume (invariant h' s) // MDM still uses very old modifies clauses
    else ()
  else begin
    assume (EC.as_kv (B.deref h' (state_ec s)) == state_kv s);
    EC.frame_invariant l (state_ec s) h h'
  end

let encrypt
  #a #phi s plain plain_len cipher
= let iv_len = 12ul in
  let iv = B.sub cipher 0ul iv_len in
  // E.random_sample iv_len iv;
  let ad = B.sub iv 0ul 0ul in
  let ad_len = 0ul in
  let cipher' = B.sub cipher iv_len plain_len in
  let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
  assume (F.model == false);
  let res = EC.encrypt
    #(G.hide a)
    s.ec
    iv
    iv_len
    ad
    ad_len
    plain
    plain_len
    cipher'
    tag'
  in
  let h' = HST.get () in
  assume (EC.as_kv (B.deref h' (state_ec s)) == state_kv s);
  res

let decrypt
  #a #phi s cipher cipher_len plain
= let iv_len = 12ul in
  let iv = B.sub cipher 0ul iv_len in
  let ad = B.sub iv 0ul 0ul in
  let ad_len = 0ul in
  let plain_len = cipher_len `U32.sub` tag_len a `U32.sub` iv_len in
  let cipher' = B.sub cipher iv_len plain_len in
  let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
  assume (F.model == false);
  let res = EverCrypt.AEAD.decrypt
    #(G.hide a)
    s.ec
    iv
    iv_len
    ad
    ad_len
    cipher'
    plain_len
    tag'
    plain
  in
  let h' = HST.get () in
  assume (EC.as_kv (B.deref h' (state_ec s)) == state_kv s);
  res
