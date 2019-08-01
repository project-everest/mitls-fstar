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

type plain_pred = (plain: Seq.seq SC.uint8) -> Tot Type0

// inline_for_extraction
let ideal: bool = false

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

inline_for_extraction
noeq
type state (a: SC.supported_alg) (phi: plain_pred) = {
  ec: B.pointer (EC.state_s a);
  kv: Ghost.erased (SC.kv a);
  table: (if ideal then table a (Ghost.reveal kv) phi else unit)
}

let invariant (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0 =
  EC.invariant h s.ec /\
  EC.as_kv (B.deref h s.ec) == G.reveal s.kv /\
  (
    if ideal
    then B.loc_disjoint (EC.footprint h s.ec) (B.loc_mreference (s.table <: table a (G.reveal s.kv) phi)) /\ h `HS.contains` (s.table <: table a (G.reveal s.kv) phi)
    else True
  )

let footprint (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot B.loc =
  EC.footprint h s.ec `B.loc_union` (if ideal then B.loc_mreference (s.table <: table a (G.reveal s.kv) phi) else B.loc_none)

let encrypted (#a: SC.supported_alg) (#phi: plain_pred) (s: state a phi) (cipher: SC.cipher a) : GTot Type0 =
  if ideal
  then
    Seq.length cipher >= 12 + SC.tag_length a /\ (
    let iv = Seq.slice cipher 0 12 in
    let cipher' = Seq.slice cipher 12 (Seq.length cipher) in
    HST.witnessed (MDM.defined (s.table <: table a (G.reveal s.kv) phi) (iv, cipher'))
  )
  else
    True

noextract
inline_for_extraction
let tag_len: SC.alg -> Tot U32.t =
  let open SC in
  function
  | AES128_CCM8       ->  8ul
  | AES256_CCM8       ->  8ul
  | AES128_GCM        -> 16ul
  | AES256_GCM        -> 16ul
  | CHACHA20_POLY1305 -> 16ul
  | AES128_CCM        -> 16ul
  | AES256_CCM        -> 16ul

let encrypt
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (plain: EC.plain_p a)
  (plain_len: U32.t {U32.v plain_len == B.length plain})
  (cipher: EC.cipher_p a) // cipher == iv ++ cipher ++ tag (see EverCrypt.AEAD.encrypt_st)
: HST.Stack EE.error_code
  (requires (fun h ->
    invariant h s /\
    B.live h plain /\
    B.live h cipher /\
    phi (B.as_seq h plain) /\
    B.loc_disjoint (footprint h s) (B.loc_buffer plain) /\
    B.loc_disjoint (footprint h s) (B.loc_buffer cipher) /\
    B.disjoint plain cipher /\
    B.length cipher == B.length plain + 12 + SC.tag_length a
  ))
  (ensures (fun h res h' -> 
    match res with
    | EE.InvalidKey ->
      B.modifies B.loc_none h h'
    | EE.Success ->
      footprint h' s == footprint h s /\
      B.modifies (B.loc_union (footprint h s) (B.loc_buffer cipher)) h h' /\
      invariant h' s
    | _ -> False
  ))
= let iv_len = 12ul in
  let iv = B.sub cipher 0ul iv_len in
  // E.random_sample iv_len iv;
  let ad = B.sub iv 0ul 0ul in
  let ad_len = 0ul in
  let cipher' = B.sub cipher iv_len plain_len in
  let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
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
  assume (EC.as_kv (B.deref h' s.ec) == G.reveal s.kv);
  res

let decrypt
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (#s: state a phi) // key
  (cipher: EC.cipher_p a) // cipher == iv ++ cipher ++ tag (see EverCrypt.AEAD.encrypt_st)
  (cipher_len: U32.t { U32.v cipher_len == B.length cipher })
  (plain: EC.plain_p a)
: HST.Stack EE.error_code
  (requires (fun h ->
    invariant h s /\
    B.live h plain /\
    B.live h cipher /\
    B.length cipher == B.length plain + 12 + SC.tag_length a /\
    B.loc_disjoint (footprint h s) (B.loc_buffer plain) /\
    B.loc_disjoint (footprint h s) (B.loc_buffer cipher) /\
    B.disjoint plain cipher
  ))
  (ensures (fun h res h' ->
    match res with
    | EE.InvalidKey ->
      B.modifies B.loc_none h h'
    | EE.Success
    | EE.AuthenticationFailure ->
      B.modifies (B.loc_union (footprint h s) (B.loc_buffer plain)) h h' /\
      footprint h' s == footprint h s /\
      invariant h' s
    | _ -> False
  ))
= let iv_len = 12ul in
  let iv = B.sub cipher 0ul iv_len in
  let ad = B.sub iv 0ul 0ul in
  let ad_len = 0ul in
  let plain_len = cipher_len `U32.sub` tag_len a `U32.sub` iv_len in
  let cipher' = B.sub cipher iv_len plain_len in
  let tag' = B.sub cipher (iv_len `U32.add` plain_len) (tag_len a) in
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
  assume (EC.as_kv (B.deref h' s.ec) == G.reveal s.kv);
  res
