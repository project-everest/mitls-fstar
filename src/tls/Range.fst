module Range

(* This module defines all range computations for the lengths of
   plaintext messages exchanged over TLS, in order to construct
   length-hiding authenticated encryption. *)
open Platform
open Platform.Bytes
open TLSConstants
open TLSInfo
open CoreCrypto

(* ranges *)
type range = r:(nat * nat) { fst r <= snd r }
type Within (n:nat) (r:range) = fst r <= n /\ n <= snd r
type Wider (r1:range) (r2:range) = fst r1 <= fst r2 /\ snd r2 <= snd r1
type rbytes (r:range) = b:bytes { Within (length b) r }

let point (n:nat) : range = (n,n)
let zero = point 0

val sum: range -> range -> Tot range
let sum (l0,h0) (l1,h1) = (l0 + l1, h0 + h1)

let aeAlg (i:id{is_AEAD i.aeAlg}) = AEAD._0 i.aeAlg

(* Length of IV for a non-AEAD cipher *)
val ivSize: i:id{~(is_AEAD i.aeAlg)} -> Tot nat
let ivSize i =
    let authEnc = i.aeAlg in
    match authEnc with
    | MACOnly _ | MtE (Stream _) _ -> 0
    | MtE (Block alg) _ -> blockSize alg

(* Mandatory fixed padding for a cipher *)
val fixedPadSize: id -> Tot nat
let fixedPadSize i =
#if TLSExt_extendedPadding
    if TLSExtensions.hasExtendedPadding id then 2
    else
#endif
        let authEnc = i.aeAlg in
        match authEnc with
        | MACOnly _ | AEAD _ _ | MtE (Stream _) _ -> 0
        | MtE (Block _) _ -> 1 // 1 byte for GenericBlockCipher.padding_length

(* Maximal padding length for a cipher *)
// Note that the 1-byte padding length is included here, i.e. block ciphers can
// use at most 255 bytes of padding, plus 1 byte to encode the length
val maxPadSize: id -> Tot nat
let maxPadSize i =
#if TLSExt_extendedPadding
    if TLSExtensions.hasExtendedPadding id then fragmentLength
    else
#endif
        let authEnc = i.aeAlg in
        match authEnc with
        | MACOnly _ | AEAD _ _ | MtE (Stream _) _ -> 0
        | MtE (Block alg) _ ->
            match i.pv with
            | SSL_3p0 -> blockSize alg
            | TLS_1p0 | TLS_1p1 | TLS_1p2 -> 256


(* Minimal padding length for a given plaintext length (in bytes) *)
val minimalPadding: id -> nat -> Tot nat
let minimalPadding i len =
    let authEnc = i.aeAlg in
    match authEnc with
    | MACOnly _ | AEAD _ _ | MtE (Stream _) _ -> fixedPadSize i
    | MtE (Block alg) _ ->
        let bs = blockSize alg in
        let lp = len % bs in
        let p = bs - lp in
#if TLSExt_extendedPadding
        let fp = fixedPadSize e in
        let p = if p < fp then p + bs else p in
#endif
        p

#if TLSExt_extendedPadding
let alignedRange i (r:range) =
    let l,h = r in
    let authEnc = i.aeAlg in
    match authEnc with
    | MACOnly _ | AEAD _ _ | MtE (Stream _) _ ->
        let mp = minimalPadding e h in
        (l,h+mp)
    | MtE (Block _) _ ->
        let macLen = macSize (macAlg_of_id i) in
        let prePad = h + macLen in
        let mp = minimalPadding i prePad in
        (l,h+mp))

let extendedPad (id:id) (r:range) (plen:nat) =
    let rg = alignedRange id r in
    let fp = fixedPadSize id in
    let _,h = r in
    let padlen = h - plen - fp in
    let pad = createBytes padlen 0 in
    TLSConstants.vlbytes fp pad
#endif

(* Sanity check *)
val minimalPadding_at_least_fixedPadSize: i:id -> len:nat ->
    Lemma (fixedPadSize i <= minimalPadding i len)
let minimalPadding_at_least_fixedPadSize _ _ = ()

val minMaxPad: id -> Tot range
let minMaxPad i = (fixedPadSize i, maxPadSize i)

type valid_clen (i:id) (clen:nat) =
     (is_AEAD i.aeAlg ==>
        0 <= clen - aeadRecordIVSize (aeAlg i) - aeadTagSize (aeAlg i) - fixedPadSize i
      /\ clen - aeadRecordIVSize (aeAlg i) - aeadTagSize (aeAlg i) - maxPadSize i <= max_TLSPlaintext_fragment_length)
   /\ (~(is_AEAD i.aeAlg) ==>
        0 <= clen - ivSize i - macSize (macAlg_of_id i) - fixedPadSize i
      /\ clen - ivSize i - macSize (macAlg_of_id i) - maxPadSize i <= max_TLSPlaintext_fragment_length)

//Is there a nice way to avoid writing implicit arguments for pairs and the superfluous refinement 0 <= max?
(* cipherRangeClass: given a ciphertext length, how long can the plaintext be? *)
val cipherRangeClass: i:id -> clen:nat -> Pure range
  (requires valid_clen i clen)
  (ensures fun (r:range) ->
       (is_AEAD i.aeAlg ==>
         Let (clen - aeadRecordIVSize (aeAlg i) - aeadTagSize (aeAlg i) - fixedPadSize i) (fun min ->
         Let (clen - aeadRecordIVSize (aeAlg i) - aeadTagSize (aeAlg i) - maxPadSize i)   (fun max ->
         0 <= max 
         /\ (  (0 < min /\ r == MkTuple2 #nat #nat min max) 
            \/ (min <= 0 /\ r == MkTuple2 #nat #nat 0 max)))))
     /\ (~(is_AEAD i.aeAlg) ==>
         Let (clen - ivSize i - macSize (macAlg_of_id i) - fixedPadSize i) (fun max ->
         Let (clen - ivSize i - macSize (macAlg_of_id i) - maxPadSize i)   (fun min ->
           0 <= max 
         /\ ((0 < min /\ max < max_TLSPlaintext_fragment_length /\ r == MkTuple2 #nat #nat min max)
          \/ (0 < min /\ max >= max_TLSPlaintext_fragment_length /\ r == MkTuple2 #nat #nat min max_TLSPlaintext_fragment_length)
          \/ (min <= 0 /\ max < max_TLSPlaintext_fragment_length /\ r == MkTuple2 #nat #nat 0 max)
          \/ (min <= 0 /\ max >= max_TLSPlaintext_fragment_length /\ r == MkTuple2 #nat #nat 0 max_TLSPlaintext_fragment_length))))) )
let cipherRangeClass i clen =
    let authEnc = i.aeAlg in
    match authEnc with
    | MACOnly _
    | MtE (Stream _) _
    | MtE (Block _ ) _ ->
        let ivL = ivSize i in
        let macLen = macSize (macAlg_of_id i) in
        let minPad, maxPad = minMaxPad i in
        let max = clen - ivL - macLen - minPad in
        let min = clen - ivL - macLen - maxPad in
        if min < 0 then
            (0,max)
        else
          if max < max_TLSPlaintext_fragment_length then
            (min,max)
          else
            (min, max_TLSPlaintext_fragment_length)
    | AEAD aeadAlg _ ->
        let ivL = aeadRecordIVSize aeadAlg in
        let tagL = aeadTagSize aeadAlg in
        let minPad, maxPad = minMaxPad i in
        let max = clen - ivL - tagL - minPad in
        let min = clen - ivL - tagL - maxPad in
        if min < 0 then
            (0,max)
        else
            (min,max)

(* Sanity check *)
val cipherRangeClass_width: i:id ->
    clen:nat{valid_clen i clen} ->
    Lemma (snd (cipherRangeClass i clen) - fst (cipherRangeClass i clen) <= maxPadSize i - fixedPadSize i)
let cipherRangeClass_width i clen = ()

(* targetLength: given a plaintext range, what would be the length of the ciphertext? *)
// TLS 1.2 RFC: For CBC, the encrypted data length is one more than the sum of
// block_length, TLSPlaintext.length, mac_length, and padding_length
val targetLength : i:id -> r:range -> Pure nat
  (requires
    snd r <= max_TLSPlaintext_fragment_length
    /\ (~(is_AEAD i.aeAlg) ==>
        snd r - fst r <= maxPadSize i - minimalPadding i (snd r + macSize (macAlg_of_id i)))
    /\ (is_AEAD i.aeAlg ==> fst r = snd r))
  (ensures (fun clen -> valid_clen i clen /\ Wider (cipherRangeClass i clen) r))
let targetLength i r =
    let l,h = r in
    let authEnc = i.aeAlg in
    match authEnc with
    | MACOnly _
    | MtE (Stream _) _
    | MtE (Block _) _ ->
        let ivL = ivSize i in
        let macLen = macSize (macAlg_of_id i) in
        let prePad = h + macLen in
        let padLen = minimalPadding i prePad in
        let clen = ivL + prePad + padLen in
        clen
    | AEAD aeadAlg _ ->
        let ivL = aeadRecordIVSize aeadAlg in
        let tagL = aeadTagSize aeadAlg in
        let fp = fixedPadSize i in
        let clen = ivL + h + fp + tagL in
        clen

(*
This is the high-level spec for targetLength (for non-AEAD ciphers):

forall i. forall r. forall x in r. exists plen.
    minimalPadding i (x + macLen) <= plen <= maxPadSize i
    /\ targetLength i r = ivSize i + x + macLen i + plen

Because how minimalPadding is defined, we don't require the lower bound
  minimalPadding i (l + macLen i) - minimalPadding i (h + macLen i) <= h - l
This always holds when l <= h
*)
(* Sanity check *)
val targetLength_spec_nonAEAD: i:id{~(is_AEAD i.aeAlg)}
  -> r:range{
      snd r <= max_TLSPlaintext_fragment_length
      /\ (~(is_AEAD i.aeAlg) ==>
          snd r - fst r <= maxPadSize i - minimalPadding i (snd r + macSize (macAlg_of_id i)))
      /\ (is_AEAD i.aeAlg ==> fst r = snd r)}
  -> x:nat{Within x r} 
  -> Lemma (Let (targetLength i r) (fun clen ->
           Let (clen - x - macSize (macAlg_of_id i) - ivSize i) (fun plen ->
             minimalPadding i (x + macSize (macAlg_of_id i)) <= plen
           /\ plen <= maxPadSize i
           /\ clen == ivSize i + x + macSize (macAlg_of_id i) + plen)))
let targetLength_spec_nonAEAD i r x = ()

(* Sanity check *)
val targetLength_spec_AEAD: i:id{is_AEAD i.aeAlg}
  -> r:range{fst r = snd r /\ snd r <= max_TLSPlaintext_fragment_length}
  -> x:nat{Within x r} ->
  Lemma (Let (targetLength i r) (fun clen ->
         Let (fixedPadSize i) (fun plen ->
           minimalPadding i (x + aeadTagSize (aeAlg i)) <= plen
         /\ plen <= maxPadSize i
         /\ clen == aeadRecordIVSize (aeAlg i) + x + aeadTagSize (aeAlg i) + plen)))
let targetLength_spec_AEAD i r x = ()

(* Sanity check *)
val targetLength_at_most_max_TLSCipher_fragment_length: i:id 
  -> r:range{
      snd r <= max_TLSPlaintext_fragment_length
      /\ (~(is_AEAD i.aeAlg) ==>
          snd r - fst r <= maxPadSize i - minimalPadding i (snd r + macSize (macAlg_of_id i)))
      /\ (is_AEAD i.aeAlg ==> fst r = snd r)}
  -> Lemma (targetLength i r <= max_TLSCipher_fragment_length)
let targetLength_at_most_max_TLSCipher_fragment_length i r = ()

val targetLength_converges: i:id
  -> r:range{
      snd r <= max_TLSPlaintext_fragment_length
      /\ (~(is_AEAD i.aeAlg) ==>
          snd r - fst r <= maxPadSize i - minimalPadding i (snd r + macSize (macAlg_of_id i)))
      /\ (is_AEAD i.aeAlg ==> fst r = snd r)}
  -> Lemma (targetLength i r = targetLength i (cipherRangeClass i (targetLength i r)))
let targetLength_converges i r = ()

val rangeClass: i:id -> r:range -> r':range
  { snd r <= max_TLSPlaintext_fragment_length
    /\ ((~(is_AEAD i.aeAlg) 
       /\ snd r - fst r <= maxPadSize i - minimalPadding i (snd r + macSize (macAlg_of_id i)))
    \/ (is_AEAD i.aeAlg /\ fst r = snd r))
    /\ r' = cipherRangeClass i (targetLength i r) }
let rangeClass (i:id) (r:range) =
    if is_MACOnly i.aeAlg && not(is_SSL_3p0 i.pv) then
        Error.unexpected "[rangeClass] given an invalid algorithm identifier"
    else
        if (snd r <= max_TLSPlaintext_fragment_length &&
            (not(is_AEAD i.aeAlg) && snd r - fst r <= maxPadSize i - minimalPadding i (snd r + macSize (macAlg_of_id i))
            || (is_AEAD i.aeAlg && fst r = snd r)))
        then
            let tlen = targetLength i r in
            match i.aeAlg with
            | MACOnly _
            | MtE (Stream _) _
            | MtE (Block _) _ ->
                let ivL = ivSize i in
                let macLen = macSize (macAlg_of_id i) in
                let minPad, maxPad = minMaxPad i in
                let max = tlen - ivL - macLen - minPad in
                if tlen <= max_TLSCipher_fragment_length then
                    cipherRangeClass i tlen
                else
                    //Unreachable when snd r <= max_TLSPlaintext_fragment_length (see lemma below)
                    Error.unexpected "[rangeClass] given an invalid plaintext length."
            | AEAD _ _ -> cipherRangeClass i tlen
        else
            Error.unexpected "[rangeClass] given an invalid range."


let fragment_range: range = (0,max_TLSPlaintext_fragment_length)
type frange = rg:range { Wider fragment_range rg }
