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
module F = Flags
module Model = Model.AEAD

noeq
inline_for_extraction
type cstate
  (a: SC.supported_alg) (phi: plain_pred)
= {
  ec: B.pointer (EC.state_s a);
  kv: G.erased (SC.kv a);
  fp: G.erased B.loc;
}

let state (a: SC.supported_alg) (phi: plain_pred) =
  if F.model
  then Model.state a phi
  else cstate a phi

inline_for_extraction
let state_ec
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi { F.model == false })
: Tot (B.pointer (EC.state_s a))
= (s <: cstate a phi).ec

let state_kv
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi)
: GTot (SC.kv a)
= if F.model then Model.state_kv (s <: Model.state a phi) else G.reveal (s <: cstate a phi).kv

let invariant (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0 =
  if F.model
  then
    Model.invariant h (s <: Model.state a phi)
  else
    EC.invariant h (state_ec s) /\
    EC.footprint h (state_ec s) == Ghost.reveal (s <: cstate a phi).fp /\
    EC.as_kv (B.deref h (state_ec s)) == state_kv s

let footprint (#a: SC.supported_alg) (#phi: plain_pred) (s: state a phi) : GTot B.loc =
  if F.model
  then
    Model.footprint (s <: Model.state a phi)
  else
    Ghost.reveal (s <: cstate a phi).fp

let frame_invariant
  #a #phi h s l h'
= if F.model
  then
    Model.frame_invariant h (s <: Model.state a phi) l h'
  else begin
    assume (EC.as_kv (B.deref h' (state_ec s)) == state_kv s); // TODO: add to EverCrypt
    EC.frame_invariant l (state_ec s) h h'
  end

#push-options "--z3rlimit 16"

let encrypt
  #a #phi s plain plain_len cipher
= let iv = B.sub cipher 0ul iv_len in
  // E.random_sample iv_len iv; // TODO
  let ad = B.sub iv 0ul 0ul in
  let ad_len = 0ul in
  let cipher' = B.sub cipher iv_len plain_len in
  let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
  assume (F.model == false);
  let res = EC.encrypt
    #(G.hide a)
    (state_ec s)
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
  assume (EC.as_kv (B.deref h' (state_ec s)) == state_kv s); // TODO: add to EverCrypt
  assert (B.as_seq h' (B.gsub cipher iv_len (B.len cipher `U32.sub` iv_len)) `Seq.equal` Seq.append (B.as_seq h' cipher') (B.as_seq h' tag'));
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
  let h = HST.get () in
  let res = EverCrypt.AEAD.decrypt
    #(G.hide a)
    (state_ec s)
    iv
    iv_len
    ad
    ad_len
    cipher'
    plain_len
    tag'
    plain
  in
  assert (B.as_seq h (B.gsub cipher iv_len (B.len cipher `U32.sub` iv_len)) `Seq.equal` Seq.append (B.as_seq h cipher') (B.as_seq h tag'));
  let h' = HST.get () in
  assume (EC.as_kv (B.deref h' (state_ec s)) == state_kv s); // TODO: add to Evercrypt
  res

#pop-options
