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

type plain_pred = (plain: Seq.seq SC.uint8) -> Tot Type0

inline_for_extraction
val state (a: SC.supported_alg) (phi: plain_pred) : Tot Type0

val state_kv
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi)
: GTot (SC.kv a)

val invariant (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0

val footprint (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot B.loc

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

val encrypt
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

val decrypt
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
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
