module Crypto.AEAD

module U8 = FStar.UInt8
module Seq = FStar.Seq
module EC = EverCrypt.AEAD
module SC = Spec.AEAD
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module EE = EverCrypt.Error
module G = FStar.Ghost
module F = Flags

open Declassify

type plain_pred = (plain: Seq.seq U8.t) -> Tot Type0

inline_for_extraction
val state (a: SC.supported_alg) (phi: plain_pred) : Tot Type0

val state_kv
  (#a: SC.supported_alg) (#phi: plain_pred)
  (s: state a phi)
: GTot (SC.kv a)

val invariant (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi) : GTot Type0

val footprint (#a: SC.supported_alg) (#phi: plain_pred) (s: state a phi) : GTot B.loc

val frame_invariant
  (#a: SC.supported_alg) (#phi: plain_pred) (h: HS.mem) (s: state a phi)
  (l: B.loc) (h' : HS.mem)
: Lemma
  (requires B.modifies l h h' /\ B.loc_disjoint l (footprint s) /\ invariant h s)
  (ensures  invariant h' s)

inline_for_extraction
let iv_len = 12ul

inline_for_extraction
noextract
let iv_length = 12

inline_for_extraction
noextract
let plain_p (a: SC.supported_alg): Type0 =
  p:B.buffer U8.t { B.length p <= SC.max_length a }

inline_for_extraction
noextract
let cipher_p (a: SC.supported_alg): Type0 =
  p:B.buffer U8.t { B.length p + SC.tag_length a <= SC.max_length a }

val fresh_iv
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (h: HS.mem)
  (s: state a phi) // key
  (iv: SC.iv a)
: GTot Type0

val frame_fresh_iv
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (h: HS.mem)
  (s: state a phi) // key
  (iv: SC.iv a)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires 
    invariant h s /\
    B.modifies l h h' /\
    B.loc_disjoint l (footprint s)
  )
  (ensures fresh_iv h' s iv <==> fresh_iv h s iv)

noextract
val is_fresh_iv
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (iv: B.buffer U8.t)
: HST.Stack bool
  (requires fun h -> 
    Flags.ideal_iv == true /\
    invariant h s /\
    B.live h iv /\
    B.len iv == iv_len
  )
  (ensures fun h res h' ->
    B.modifies B.loc_none h h' /\
    (res == true <==> fresh_iv h s (B.as_seq h iv))
  )

val encrypt
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (plain: plain_p a)
  (plain_len: U32.t {U32.v plain_len == B.length plain})
  (cipher: cipher_p a) // cipher == iv ++ cipher ++ tag (see EverCrypt.AEAD.encrypt_st)
  // FIXME: for now we assume that cipher already contains some iv, but at some point
  // we should have `encrypt` randomly generate it and write it into cipher
: HST.Stack unit
  (requires fun h ->
    invariant h s /\
    B.live h plain /\
    B.live h cipher /\
    phi (B.as_seq h plain) /\
    B.loc_disjoint (footprint s) (B.loc_buffer plain) /\
    B.loc_disjoint (footprint s) (B.loc_buffer cipher) /\
    B.disjoint plain cipher /\
    B.length cipher == B.length plain + iv_length + SC.tag_length a /\
    (F.ideal_iv == true ==> fresh_iv h s (B.as_seq h (B.gsub cipher 0ul iv_len)))
  )
  (ensures fun h _ h' ->
      // FIXME: currently we assume iv already in cipher,
      // at some point it should be randomly generated here
      let iv = B.gsub cipher 0ul iv_len in
      let cipher' = B.gsub cipher iv_len (B.len cipher `U32.sub` iv_len) in
      B.modifies (B.loc_union (footprint s) (B.loc_buffer cipher')) h h' /\
      invariant h' s /\
      (F.ideal_AEAD == false ==> 
       SC.encrypt (state_kv s) (B.as_seq h iv) Seq.empty (B.as_seq h plain) `Seq.equal` 
       B.as_seq h' cipher')
  )

val decrypt
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi) // key
  (cipher: cipher_p a) // cipher == iv ++ cipher ++ tag (see EverCrypt.AEAD.decrypt_st)
  (cipher_len: U32.t { U32.v cipher_len == B.length cipher })
  (plain: plain_p a)
: HST.Stack EE.error_code
  (requires fun h ->
    invariant h s /\
    B.live h plain /\
    B.live h cipher /\
    B.length cipher == B.length plain + iv_length + SC.tag_length a /\
    B.loc_disjoint (footprint s) (B.loc_buffer plain) /\
    B.loc_disjoint (footprint s) (B.loc_buffer cipher) /\
    B.disjoint plain cipher
  )
  (ensures fun h res h' ->
    let iv' = B.gsub cipher 0ul iv_len in
    let cipher' = B.gsub cipher iv_len (cipher_len `U32.sub` iv_len) in
    match res with
    | EE.Success ->
      B.modifies (B.loc_union (footprint s) (B.loc_buffer plain)) h h' /\
      invariant h' s /\ (
        if F.ideal_AEAD
        then phi (B.as_seq h' plain)
        else SC.decrypt (state_kv s) (B.as_seq h iv') Seq.empty (B.as_seq h cipher') == Some (B.as_seq h' plain)
      )
    | EE.AuthenticationFailure ->
      B.modifies (B.loc_union (footprint s) (B.loc_buffer plain)) h h' /\
      invariant h' s /\
      (F.ideal_AEAD == false ==> 
       SC.decrypt (state_kv s) (B.as_seq h iv') Seq.empty (B.as_seq h cipher') == None)
    | _ -> False
  )

val create
  (r: HS.rid)
  (#a: SC.supported_alg)
  (k: B.buffer U8.t) // contains the key
  (phi: plain_pred)
: HST.ST (option (state a phi))
  (requires fun h ->
    HST.is_eternal_region r /\
    B.live h k /\
    B.length k == SC.key_length a
  )
  (ensures fun h res h' ->
    B.modifies B.loc_none h h' /\
    begin match res with
    | None -> True // supported_alg is not enough to ensure that EverCrypt.AEAD.create_in will succeed (cf. EverCrypt.AEAD.fst: Vale with bad config)
    | Some s ->
      B.fresh_loc (footprint s) h h' /\
      B.loc_includes (B.loc_region_only true r) (footprint s) /\
      invariant h' s /\
      state_kv s == B.as_seq h k
    end
  )

val free
  (#a: SC.supported_alg)
  (#phi: plain_pred)
  (s: state a phi)
: HST.ST unit
  (requires fun h -> invariant h s)
  (ensures  fun h _ h' -> B.modifies (footprint s) h h')
