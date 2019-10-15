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
  (a: SC.supported_alg)
= {
  ec: B.pointer (EC.state_s a);
  kv: G.erased (SC.kv a);
  fp: G.erased B.loc;
}

let mphi (phi: plain_pred) : Tot (Model.plain_pred) =
  phi

noeq
inline_for_extraction
type state (a: SC.supported_alg) (phi: plain_pred) =
  // trick for extraction instead of using refinement
  | Created: (log: (if F.model then Model.state a phi else squash False)) -> state a phi
  | Coerced: (st: cstate a) -> state a phi

let safe #a #phi s =
  if F.model then Created? s else false

noextract
let log (#a: _) (#phi: _) (s: state a phi { safe s }) : Tot (Model.state a phi)
= Created?.log s

let state_kv
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi)
: GTot (SC.kv a)
= if safe s
  then Model.state_kv (log s)
  else match s with
  | Coerced st -> G.reveal st.kv

unfold
let invariant' (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0 =
  if safe s
  then Model.invariant h (log s)
  else match s with
  | Coerced st ->
    EC.invariant h st.ec /\
    EC.footprint h st.ec == Ghost.reveal st.fp /\
    EC.freeable h st.ec /\
    EC.as_kv (B.deref h st.ec) == state_kv s

let invariant = invariant'

let footprint (#a: SC.supported_alg) (#phi: plain_pred) (s: state a phi) : GTot B.loc =
  if safe s
  then Model.footprint (log s)
  else match s with
  | Coerced st -> Ghost.reveal st.fp

let invariant_loc_in_footprint #a #phi s m = ()

let frame_invariant
  #a #phi h s l h'
= if safe s
  then Model.frame_invariant h (log s) l h'
  else match s with
  | Coerced st -> EC.frame_invariant l st.ec h h'

let sample a k =
  Random.sample_secret_buffer (U32.uint_to_t (SC.key_length a)) k

let coerce r a k phi = 
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
        let s : state a phi = Coerced ({ec = b; kv = G.hide (B.as_seq h0 k); fp = G.hide (EC.footprint h2 b)}) in        
        B.free dst;
        let h3 = HST.get () in
        frame_invariant h2 s (B.loc_addr_of_buffer dst) h3;
        Some s
    in
    let h4 = HST.get () in
    B.modifies_only_not_unused_in B.loc_none h0 h4;
    res

let create r a k phi = 
    sample a k;
    let kv = MU.get_buffer k (U32.uint_to_t (SC.key_length a)) in
    let res = Created (Model.create r kv (mphi phi) <: Model.state a (mphi phi)) in
    res

let fresh_iv
  #a #phi h s iv
= safe s ==> Model.fresh_iv h (log s) iv

let frame_fresh_iv
  #a #phi h s iv l h'
= if safe s
  then Model.frame_fresh_iv h (log s) iv l h'
  else ()

let is_fresh_iv
  #a #phi s iv
= if safe s
  then
    let log = log s in
    let h = HST.get () in
    let iv_s = MU.get_buffer iv iv_len in
    let h1 = HST.get () in
    frame_invariant h s B.loc_none h1;
    let res = Model.is_fresh_iv log iv_s in
    frame_fresh_iv h s iv_s B.loc_none h1;
    res
  else true

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
  if safe s then
    let s = log s in
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
  else match s with
  | Coerced st ->
    // E.random_sample iv_len iv; // TODO
    let ad = B.sub iv 0ul 0ul in
    let ad_len = 0ul in
    let cipher' = B.sub cipher iv_len plain_len in
    let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
    let _ = EC.encrypt
      #(G.hide a)
      st.ec
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

let decrypt #a #phi s cipher cipher_len plain = 
  let h0 = HST.get () in
  let iv = B.sub cipher 0ul iv_len in
  let plain_len = cipher_len `U32.sub` tag_len a `U32.sub` iv_len in
  if safe s then
    let s = log s in
    let iv_s = MU.get_buffer iv iv_len in
    let cipher_tag_len = cipher_len `U32.sub` iv_len in
    let cipher_tag = B.sub cipher iv_len cipher_tag_len in
    let cipher_tag_s = MU.get_buffer cipher_tag cipher_tag_len in
    let h1 = HST.get () in
    Model.frame_invariant h0 s B.loc_none h1;
    begin match Model.decrypt s iv_s cipher_tag_s with
    | None -> EE.AuthenticationFailure
    | Some plain_s ->
      let h2 = HST.get () in
      MU.put_buffer plain plain_len plain_s;
      let h3 = HST.get () in
      Model.frame_invariant h2 s (B.loc_buffer plain) h3;
      EE.Success
    end
  else match s with
  | Coerced st ->
    let ad = B.sub iv 0ul 0ul in
    let ad_len = 0ul in
    let cipher' = B.sub cipher iv_len plain_len in
    let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
    let h = HST.get () in
    let res = EC.decrypt
      #(G.hide a)
      st.ec
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

#pop-options

let free #a #phi s = 
  if safe s
  then Model.free (log s)
  else match s with
  | Coerced st ->
    EC.free #(G.hide a) st.ec
