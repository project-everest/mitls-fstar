module Crypto.AE
include Crypto.AEAD

module U8 = FStar.UInt8
module Seq = FStar.Seq
module SC = Spec.Agile.AEAD
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module EE = EverCrypt.Error
module G = FStar.Ghost
module F = Flags

open Declassify

val encrypt
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (plain: plain_p a)
  (plain_len: U32.t {U32.v plain_len == B.length plain})
  (cipher: cipher_p a) // cipher == iv ++ cipher ++ tag (see EverCrypt.AEAD.encrypt_st)
: HST.Stack unit
  (requires fun h ->
    invariant h s /\
    B.live h plain /\
    B.live h cipher /\
    (F.ideal_AEAD == true ==> phi (B.as_seq h plain)) /\
    B.loc_disjoint (footprint s) (B.loc_buffer plain) /\
    B.loc_disjoint (footprint s) (B.loc_buffer cipher) /\
    B.disjoint plain cipher /\
    B.length cipher == B.length plain + iv_length + SC.tag_length a
    // This is the only difference wrt Crypto.AEAD.encrypt, because
    // the IV is sampled randomly 
    //(F.ideal_iv == true ==> fresh_iv h s (B.as_seq h (B.gsub cipher 0ul iv_len)))
  )
  (ensures fun h _ h' ->
      let iv = B.gsub cipher 0ul iv_len in
      let cipher' = B.gsub cipher iv_len (B.len cipher `U32.sub` iv_len) in
      B.modifies (B.loc_union (footprint s) (B.loc_buffer cipher)) h h' /\
      invariant h' s /\
      (F.ideal_AEAD == false ==> 
       SC.encrypt (state_kv s) (B.as_seq h' iv) Seq.empty (B.as_seq h plain) `Seq.equal`
       B.as_seq h' cipher')
  )

// decrypt is unchanged from Crypto.AEAD.decrypt
