module Crypto.AEAD

module U8 = FStar.UInt8
module Seq = FStar.Seq
module EC = EverCrypt.AEAD
module SC = Spec.Agile.AEAD
module B = LowStar.Buffer
module E = EverCrypt
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module EE = EverCrypt.Error
module G = FStar.Ghost
module F = Flags
module Model = Model.AEAD
module MU = Model.Utils

open Declassify

noeq
inline_for_extraction
type cstate
  (a: SC.supported_alg) (phi: plain_pred)
= {
  ec: B.pointer (EC.state_s a);
  kv: G.erased (SC.kv a);
  fp: G.erased B.loc;
}

let mphi (phi: plain_pred) : Tot (Model.plain_pred) =
  phi

let state (a: SC.supported_alg) (phi: plain_pred) =
  if F.model
  then Model.state a (mphi phi)
  else cstate a phi

inline_for_extraction
noextract
let state_m
  (#a: SC.supported_alg) (#phi: plain_pred) (s: state a phi { F.model == true })
: Tot (Model.state a (mphi phi))
= s

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
= if F.model then Model.state_kv (state_m s) else G.reveal (s <: cstate a phi).kv

unfold
let invariant' (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0 =
  if F.model
  then
    Model.invariant h (state_m s)
  else
    EC.invariant h (state_ec s) /\
    EC.footprint h (state_ec s) == Ghost.reveal (s <: cstate a phi).fp /\
    EC.freeable h (state_ec s) /\
    EC.as_kv (B.deref h (state_ec s)) == state_kv s

let invariant = invariant'

let footprint (#a: SC.supported_alg) (#phi: plain_pred) (s: state a phi) : GTot B.loc =
  if F.model
  then
    Model.footprint (state_m s)
  else
    Ghost.reveal (s <: cstate a phi).fp

let frame_invariant
  #a #phi h s l h'
= if F.model
  then
    Model.frame_invariant h (state_m s) l h'
  else begin
    EC.frame_invariant l (state_ec s) h h'
  end

let fresh_iv
  #a #phi h s iv
= F.model == true ==> Model.fresh_iv h (state_m s) iv

let frame_fresh_iv
  #a #phi h s iv l h'
= if F.model
  then Model.frame_fresh_iv h (state_m s) iv l h'

let is_fresh_iv
  #a #phi s iv
= let h = HST.get () in
  let iv_s = MU.get_buffer iv iv_len in
  let h1 = HST.get () in
  frame_invariant h s B.loc_none h1;
  let res = Model.is_fresh_iv (state_m s) iv_s in
  frame_fresh_iv h s iv_s B.loc_none h1 ;
  res

// TODO: move to EverCrypt.AEAD
noextract
inline_for_extraction
let tag_len : (x: SC.alg) -> Tot (y: U32.t { U32.v y == SC.tag_length x }) =
  let open SC in
  function
  | AES128_CCM8       ->  8ul
  | AES256_CCM8       ->  8ul
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 16ul
  | CHACHA20_POLY1305 -> 16ul
  | AES128_CCM        -> 16ul
  | AES256_CCM        -> 16ul

#push-options "--z3rlimit 16"

let encrypt #a #phi s plain plain_len cipher = 
  let h0 = HST.get () in
  let iv = B.sub cipher 0ul iv_len in
  if F.model
  then begin
    let s : Model.state a (mphi phi) = s in
    let iv_s = MU.get_buffer iv iv_len in
    let plain_s = MU.get_buffer plain plain_len in
    let cipher_tag_len = plain_len `U32.add` tag_len a in
    let cipher_tag' = B.sub cipher iv_len cipher_tag_len in
    let h1 = HST.get () in
    Model.frame_invariant h0 s B.loc_none h1;
    Model.frame_fresh_iv h0 s iv_s B.loc_none h1;
    let cipher_s = Model.encrypt s iv_s plain_s in
    let h2 = HST.get () in
    MU.put_buffer cipher_tag' cipher_tag_len cipher_s;
    let h3 = HST.get () in
    Model.frame_invariant h2 s (B.loc_buffer cipher_tag') h3
  end else begin
    // E.random_sample iv_len iv; // TODO
    let ad = B.sub iv 0ul 0ul in
    let ad_len = 0ul in
    let cipher' = B.sub cipher iv_len plain_len in
    let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
    let _ = EC.encrypt
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
    assert (B.as_seq h' (B.gsub cipher iv_len (B.len cipher `U32.sub` iv_len)) `Seq.equal` Seq.append (B.as_seq h' cipher') (B.as_seq h' tag'))
  end

let decrypt #a #phi s cipher cipher_len plain = 
  let h0 = HST.get () in
  let iv = B.sub cipher 0ul iv_len in
  let plain_len = cipher_len `U32.sub` tag_len a `U32.sub` iv_len in
  if F.model = true
  then begin
    let s : Model.state a (mphi phi) = s in
    let iv_s = MU.get_buffer iv iv_len in
    let cipher_tag_len = cipher_len `U32.sub` iv_len in
    let cipher_tag = B.sub cipher iv_len cipher_tag_len in
    let cipher_tag_s = MU.get_buffer cipher_tag cipher_tag_len in
    let h1 = HST.get () in
    Model.frame_invariant h0 s B.loc_none h1;
    match Model.decrypt s iv_s cipher_tag_s with
    | None -> EE.AuthenticationFailure
    | Some plain_s ->
      let h2 = HST.get () in
      MU.put_buffer plain plain_len plain_s;
      let h3 = HST.get () in
      Model.frame_invariant h2 s (B.loc_buffer plain) h3;
      EE.Success
  end else begin
    let ad = B.sub iv 0ul 0ul in
    let ad_len = 0ul in
    let cipher' = B.sub cipher iv_len plain_len in
    let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
    let h = HST.get () in
    let res = EC.decrypt
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
    res
  end

#pop-options

let create r #a k phi = 
  if F.model
  then
    let kv = MU.get_buffer k (U32.uint_to_t (SC.key_length a)) in
    let res = Model.create r kv (mphi phi) <: Model.state a (mphi phi) in
    Some res
  else begin
    let h0 = HST.get () in
    let dst : B.pointer (B.pointer_or_null (EC.state_s a)) = B.mmalloc r B.null 1ul in // I could also allocate it onto a fresh stack frame, but it's useless here
    let h1 = HST.get () in
    let res =
      match EC.create_in r dst k with
      | EE.UnsupportedAlgorithm ->
        B.free dst;
        None
      | EE.Success ->
        let h2 = HST.get () in
        let b : B.pointer (EC.state_s a) = B.index dst 0ul in
        let s : state a phi = {ec = b; kv = G.hide (B.as_seq h0 k); fp = G.hide (EC.footprint h2 b)} <: cstate a phi in        
        B.free dst;
        let h3 = HST.get () in
        frame_invariant h2 s (B.loc_addr_of_buffer dst) h3;
        Some s
    in
    let h4 = HST.get () in
    B.modifies_only_not_unused_in B.loc_none h0 h4;
    res
  end

let free #a #phi s = 
  if F.model
  then Model.free (state_m s)
  else EC.free #(G.hide a) (state_ec s)
