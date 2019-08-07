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

let invariant (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0 =
  if F.model
  then
    Model.invariant h (state_m s)
  else
    EC.invariant h (state_ec s) /\
    EC.footprint h (state_ec s) == Ghost.reveal (s <: cstate a phi).fp /\
    EC.as_kv (B.deref h (state_ec s)) == state_kv s

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
    assume (EC.as_kv (B.deref h' (state_ec s)) == state_kv s); // TODO: add to EverCrypt
    EC.frame_invariant l (state_ec s) h h'
  end

noextract
let rec get_buffer
  (#t: Type)
  (b: B.buffer t)
  (len: U32.t)
: HST.Stack (Seq.seq t)
  (requires (fun h ->
    F.model == true /\
    B.live h b /\
    len == B.len b
  ))
  (ensures (fun h s h' ->
    B.modifies B.loc_none h h' /\
    s `Seq.equal` B.as_seq h b
  ))
  (decreases (U32.v len))
= if len = 0ul
  then Seq.empty
  else
    let x = B.index b 0ul in
    let len' = len `U32.sub` 1ul in
    let b' = B.sub b 1ul len' in
    let s = get_buffer b' len' in
    Seq.cons x s

noextract
let rec put_buffer
  (#t: Type)
  (b: B.buffer t)
  (len: U32.t)
  (s: Seq.seq t)
: HST.Stack unit
  (requires (fun h ->
    F.model == true /\
    B.live h b /\
    len == B.len b /\
    Seq.length s == B.length b
  ))
  (ensures (fun h _ h' ->
    B.modifies (B.loc_buffer b) h h' /\
    B.as_seq h' b `Seq.equal` s
  ))
= if len = 0ul
  then ()
  else begin
    let b0 = B.sub b 0ul 1ul in
    B.upd b0 0ul (Seq.head s);
    let len' = len `U32.sub` 1ul in
    let b' = B.sub b 1ul len' in
    put_buffer b' len' (Seq.tail s);
    let h' = HST.get () in
    assert (B.as_seq h' b `Seq.equal` Seq.append (B.as_seq h' b0) (B.as_seq h' b'))
  end

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
: HST.Stack EE.error_code
  (requires (fun h ->
    invariant h s /\
    B.live h plain /\
    B.live h cipher /\
    phi (Cast.to_seq_uint8 (B.as_seq h plain)) /\
    B.loc_disjoint (footprint s) (B.loc_buffer plain) /\
    B.loc_disjoint (footprint s) (B.loc_buffer cipher) /\
    B.disjoint plain cipher /\
    B.length cipher == B.length plain + iv_length + SC.tag_length a
  ))
  (ensures (fun h res h' -> 
    match res with
    | EE.InvalidKey ->
      B.modifies B.loc_none h h' // TODO: should be False, need to fix EverCrypt
    | EE.Success ->
      // FIXME: currently we assume iv already in cipher,
      // at some point it should be randomly generated here
      let iv = B.gsub cipher 0ul iv_len in
      let cipher' = B.gsub cipher iv_len (B.len cipher `U32.sub` iv_len) in
      B.modifies (B.loc_union (footprint s) (B.loc_buffer cipher')) h h' /\
      invariant h' s /\
      (F.ideal_AEAD == false ==> SC.encrypt (state_kv s) (B.as_seq h iv) Seq.empty (B.as_seq h plain) `Seq.equal` B.as_seq h' cipher')
    | _ -> False
  ))

let encrypt'
  #a #phi s plain plain_len cipher
= let h0 = HST.get () in
  let iv = B.sub cipher 0ul iv_len in
  if F.model
  then begin
    let s : Model.state a (mphi phi) = s in
    let iv_s = get_buffer iv iv_len in
    let plain_s = get_buffer plain plain_len in
    let cipher_tag_len = plain_len `U32.add` tag_len a in
    let cipher_tag' = B.sub cipher iv_len cipher_tag_len in
    let h1 = HST.get () in
    Model.frame_invariant h0 s B.loc_none h1;
    let cipher_s = Model.encrypt s iv_s plain_s in
    let h2 = HST.get () in
    put_buffer cipher_tag' cipher_tag_len cipher_s;
    let h3 = HST.get () in
    Model.frame_invariant h2 s (B.loc_buffer cipher_tag') h3;
    EE.Success
  end else begin
    // E.random_sample iv_len iv; // TODO
    let ad = B.sub iv 0ul 0ul in
    let ad_len = 0ul in
    let cipher' = B.sub cipher iv_len plain_len in
    let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
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
    | EE.InvalidKey ->
      B.modifies B.loc_none h h' // TODO: should be False, need to fix EverCrypt
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
    let iv_s = get_buffer iv iv_len in
    let cipher_tag_len = cipher_len `U32.sub` iv_len in
    let cipher_tag = B.sub cipher iv_len cipher_tag_len in
    let cipher_tag_s = get_buffer cipher_tag cipher_tag_len in
    let h1 = HST.get () in
    Model.frame_invariant h0 s B.loc_none h1;
    match Model.decrypt s iv_s cipher_tag_s with
    | None -> EE.AuthenticationFailure
    | Some plain_s ->
      let h2 = HST.get () in
      put_buffer plain plain_len plain_s;
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
    assume (EC.as_kv (B.deref h' (state_ec s)) == state_kv s); // TODO: add to Evercrypt
    res
  end

let to_seq_sec8_as_seq_gsub (h: HS.mem) (b: B.buffer U8.t) (off: U32.t) (len: U32.t { U32.v off + U32.v len <= B.length b }) : Lemma
    (Cast.to_seq_sec8 (B.as_seq h (B.gsub b off len)) == B.as_seq h (B.gsub (Cast.to_buf_sec8 b) off len))
= Cast.gsub_to_buf_sec8 b off len;
  Cast.as_seq_to_buf_sec8 (B.gsub b off len) h

let loc_buffer_gsub_to_buf_sec8 (b: B.buffer U8.t) (off: U32.t) (len: U32.t { U32.v off + U32.v len <= B.length b }) : Lemma
  (B.loc_buffer (B.gsub (Cast.to_buf_sec8 b) off len) == B.loc_buffer (B.gsub b off len))
= Cast.gsub_to_buf_sec8 b off len;
  Cast.loc_buffer_to_buf_sec8 (B.gsub b off len)

let encrypt
  #a #phi s plain plain_len cipher
= let h = HST.get () in
  Cast.live_to_buf_sec8 plain h;
  Cast.live_to_buf_sec8 cipher h;
  Cast.to_seq_uint8_to_seq_sec8 (B.as_seq h plain);
  Cast.as_seq_to_buf_sec8 plain h;
  Cast.loc_buffer_to_buf_sec8 plain;
  Cast.loc_buffer_to_buf_sec8 cipher;
  let res = encrypt' s (Cast.to_buf_sec8 plain) plain_len (Cast.to_buf_sec8 cipher) in
  let h' = HST.get () in
  to_seq_sec8_as_seq_gsub h cipher 0ul iv_len;
  to_seq_sec8_as_seq_gsub h' cipher iv_len plain_len;
  to_seq_sec8_as_seq_gsub h' cipher (iv_len `U32.add` plain_len) (tag_len a);
  to_seq_sec8_as_seq_gsub h' cipher iv_len (B.len cipher `U32.sub` iv_len);
  loc_buffer_gsub_to_buf_sec8 cipher iv_len (B.len cipher `U32.sub` iv_len);
  res

let decrypt
  #a #phi s cipher cipher_len plain
= let h = HST.get () in
  Cast.live_to_buf_sec8 plain h;
  Cast.live_to_buf_sec8 cipher h;
  Cast.loc_buffer_to_buf_sec8 plain;
  Cast.loc_buffer_to_buf_sec8 cipher;
  let res = decrypt' s (Cast.to_buf_sec8 cipher) cipher_len (Cast.to_buf_sec8 plain) in
  let h' = HST.get () in
  to_seq_sec8_as_seq_gsub h cipher 0ul iv_len;
  to_seq_sec8_as_seq_gsub h cipher iv_len (cipher_len `U32.sub` iv_len);
  Cast.to_seq_uint8_to_seq_sec8 (B.as_seq h' plain);
  Cast.as_seq_to_buf_sec8 plain h';
  res

#pop-options
