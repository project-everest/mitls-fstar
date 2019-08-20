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
module Cast = Crypto.Util.IntCast
module MU = Model.Utils

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
  (fun x -> phi (Cast.to_seq_uint8 x))

let state (a: SC.supported_alg) (phi: plain_pred) =
  if F.model
  then Model.state a (mphi phi)
  else cstate a phi

inline_for_extraction
noextract
let state_m
  (#a: SC.supported_alg) (#phi: plain_pred) (s: state a phi { F.model == true })
: Tot (Model.state a (mphi phi))
= (s <: Model.state a (mphi phi))

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
  let res = Model.is_fresh_iv (state_m s) (Cast.to_seq_sec8 iv_s) in
  frame_fresh_iv h s (Cast.to_seq_sec8 iv_s) B.loc_none h1 ;
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

inline_for_extraction
noextract
val encrypt'
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (plain: EC.plain_p a)
  (plain_len: U32.t {U32.v plain_len == B.length plain})
  (cipher: EC.cipher_p a) // cipher == iv ++ cipher ++ tag (see EverCrypt.AEAD.encrypt_st)
  // FIXME: for now we assume that cipher already contains some iv, but at some point
  // we should have `encrypt` randomly generate it and write it into cipher
: HST.Stack unit
  (requires (fun h ->
    invariant h s /\
    B.live h plain /\
    B.live h cipher /\
    phi (Cast.to_seq_uint8 (B.as_seq h plain)) /\
    B.loc_disjoint (footprint s) (B.loc_buffer plain) /\
    B.loc_disjoint (footprint s) (B.loc_buffer cipher) /\
    B.disjoint plain cipher /\
    B.length cipher == B.length plain + iv_length + SC.tag_length a /\
    (F.ideal_iv == true ==> fresh_iv h s (B.as_seq h (B.gsub cipher 0ul iv_len)))
  ))
  (ensures (fun h _ h' ->
      // FIXME: currently we assume iv already in cipher,
      // at some point it should be randomly generated here
      let iv = B.gsub cipher 0ul iv_len in
      let cipher' = B.gsub cipher iv_len (B.len cipher `U32.sub` iv_len) in
      B.modifies (B.loc_union (footprint s) (B.loc_buffer cipher')) h h' /\
      invariant h' s /\
      (F.ideal_AEAD == false ==> SC.encrypt (state_kv s) (B.as_seq h iv) Seq.empty (B.as_seq h plain) `Seq.equal` B.as_seq h' cipher')
  ))

let encrypt'
  #a #phi s plain plain_len cipher
= let h0 = HST.get () in
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
    Model.frame_invariant h2 s (B.loc_buffer cipher_tag') h3;
    ()
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
    assert (B.as_seq h' (B.gsub cipher iv_len (B.len cipher `U32.sub` iv_len)) `Seq.equal` Seq.append (B.as_seq h' cipher') (B.as_seq h' tag'));
    ()
  end

inline_for_extraction
noextract
val decrypt'
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (cipher: EC.cipher_p a) // cipher == iv ++ cipher ++ tag (see EverCrypt.AEAD.decrypt_st)
  (cipher_len: U32.t { U32.v cipher_len == B.length cipher })
  (plain: EC.plain_p a)
: HST.Stack EE.error_code
  (requires (fun h ->
    invariant h s /\
    B.live h plain /\
    B.live h cipher /\
    B.length cipher == B.length plain + iv_length + SC.tag_length a /\
    B.loc_disjoint (footprint s) (B.loc_buffer plain) /\
    B.loc_disjoint (footprint s) (B.loc_buffer cipher) /\
    B.disjoint plain cipher
  ))
  (ensures (fun h res h' ->
    let iv' = B.gsub cipher 0ul iv_len in
    let cipher' = B.gsub cipher iv_len (cipher_len `U32.sub` iv_len) in
    match res with
    | EE.Success ->
      B.modifies (B.loc_union (footprint s) (B.loc_buffer plain)) h h' /\
      invariant h' s /\ (
        if F.ideal_AEAD
        then phi (Cast.to_seq_uint8 (B.as_seq h' plain))
        else SC.decrypt (state_kv s) (B.as_seq h iv') Seq.empty (B.as_seq h cipher') == Some (B.as_seq h' plain)
      )
    | EE.AuthenticationFailure ->
      B.modifies (B.loc_union (footprint s) (B.loc_buffer plain)) h h' /\
      invariant h' s /\
      (F.ideal_AEAD == false ==> SC.decrypt (state_kv s) (B.as_seq h iv') Seq.empty (B.as_seq h cipher') == None)
    | _ -> False
  ))

let decrypt'
  #a #phi s cipher cipher_len plain
= let h0 = HST.get () in
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

let encrypt
  #a #phi s plain plain_len cipher
= let h = HST.get () in
  Cast.live_to_buf_sec8 plain h;
  Cast.live_to_buf_sec8 cipher h;
  Cast.to_seq_uint8_to_seq_sec8 (B.as_seq h plain);
  Cast.as_seq_to_buf_sec8 plain h;
  Cast.loc_buffer_to_buf_sec8 plain;
  Cast.loc_buffer_to_buf_sec8 cipher;
  Cast.to_seq_sec8_as_seq_gsub h cipher 0ul iv_len;
  let _ = encrypt' s (Cast.to_buf_sec8 plain) plain_len (Cast.to_buf_sec8 cipher) in
  let h' = HST.get () in
  Cast.to_seq_sec8_as_seq_gsub h' cipher iv_len plain_len;
  Cast.to_seq_sec8_as_seq_gsub h' cipher (iv_len `U32.add` plain_len) (tag_len a);
  Cast.to_seq_sec8_as_seq_gsub h' cipher iv_len (B.len cipher `U32.sub` iv_len);
  Cast.loc_buffer_gsub_to_buf_sec8 cipher iv_len (B.len cipher `U32.sub` iv_len);
  ()

let decrypt
  #a #phi s cipher cipher_len plain
= let h = HST.get () in
  Cast.live_to_buf_sec8 plain h;
  Cast.live_to_buf_sec8 cipher h;
  Cast.loc_buffer_to_buf_sec8 plain;
  Cast.loc_buffer_to_buf_sec8 cipher;
  let res = decrypt' s (Cast.to_buf_sec8 cipher) cipher_len (Cast.to_buf_sec8 plain) in
  let h' = HST.get () in
  Cast.to_seq_sec8_as_seq_gsub h cipher 0ul iv_len;
  Cast.to_seq_sec8_as_seq_gsub h cipher iv_len (cipher_len `U32.sub` iv_len);
  Cast.to_seq_uint8_to_seq_sec8 (B.as_seq h' plain);
  Cast.as_seq_to_buf_sec8 plain h';
  res

#pop-options

let create
  r #a k phi
= if F.model
  then
    let kv = MU.get_buffer k (U32.uint_to_t (SC.key_length a)) in
    let kv = Cast.to_seq_sec8 kv in
    let res = Model.create r kv (mphi phi) <: Model.state a (mphi phi) in
    Some res
  else begin
    let h0 = HST.get () in
    let dst : B.pointer (B.pointer_or_null (EC.state_s a)) = B.mmalloc r B.null 1ul in // I could also allocate it onto a fresh stack frame, but it's useless here
    let h1 = HST.get () in
    Cast.live_to_buf_sec8 k h1;
    let res =
      match EC.create_in r dst (Cast.to_buf_sec8 k) with
      | EE.UnsupportedAlgorithm ->
        B.free dst;
        None
      | EE.Success ->
        let h2 = HST.get () in
        let b : B.pointer (EC.state_s a) = B.index dst 0ul in
        let s : state a phi = {ec = b; kv = G.hide (Cast.to_seq_sec8 (B.as_seq h0 k)); fp = G.hide (EC.footprint h2 b)} <: cstate a phi in
        Cast.as_seq_to_buf_sec8 k h1;
        B.free dst;
        let h3 = HST.get () in
        frame_invariant h2 s (B.loc_addr_of_buffer dst) h3;
        Some s
    in
    let h4 = HST.get () in
    B.modifies_only_not_unused_in B.loc_none h0 h4;
    res
  end

let free
  #a #phi s
= if F.model
  then Model.free (state_m s)
  else EC.free #(G.hide a) (state_ec s)
