module Range

(* This module defines all range computations for the lengths of
   plaintext messages exchanged over TLS, in order to construct
   length-hiding authenticated encryption. *)

open FStar.Bytes
open TLSConstants
open TLSInfo

module AE = AEADProvider

let hashLen = Hashing.tagLen

#reset-options "--initial_fuel 0 --initial_ifuel 1 --max_fuel 0 --max_ifuel 2"

type id2 = i:id { ID12? i } // gradually adding TLS 1.3...

(* ranges *)
type range = r:(nat * nat) { fst r <= snd r }
let within (n:nat) (r:range) = fst r <= n && n <= snd r
let wider (r1:range) (r2:range) = fst r1 <= fst r2 && snd r2 <= snd r1
type rbytes (r:range) = b:bytes {within (length b) r}

let point (n:nat) : range = (n,n)
let zero = point 0

val sum: range -> range -> Tot range
let sum (l0,h0) (l1,h1) = (l0 + l1, h0 + h1)
let aeAlg (i:id{~(PlaintextID? i) /\ AEAD? (aeAlg_of_id i)}) = AEAD?._0 (aeAlg_of_id i)

(* Length of IV for a non-AEAD cipher *)
val ivSize: i:id{~(PlaintextID? i) /\ ~(AEAD? (aeAlg_of_id i))} -> Tot nat
let ivSize i =
  let authEnc = aeAlg_of_id i in
  match authEnc with
  | MACOnly _ | MtE (Stream _) _ -> 0
  | MtE (Block alg) _ -> CoreCrypto.blockSize alg

(* Mandatory fixed padding for a cipher *)
val fixedPadSize: id -> Tot nat
let fixedPadSize i =
  if PlaintextID? i then 0
  else
    let authEnc = aeAlg_of_id i in
    match authEnc with
    | MACOnly _ | AEAD _ _ | MtE (Stream _) _ -> 0
    | MtE (Block _) _ -> 1 // 1 byte for GenericBlockCipher.padding_length

(* Maximal padding length for a cipher *)
// Note that the 1-byte padding length is included here, i.e. block ciphers can
// use at most 255 bytes of padding, plus 1 byte to encode the length
val maxPadSize: id2 -> Tot nat
let maxPadSize i =
  let authEnc = aeAlg_of_id i in
  match authEnc with
    | MACOnly _ | AEAD _ _ | MtE (Stream _) _ -> 0
    | MtE (Block alg) _ ->
        lemma_MtE i; lemma_ID12 i;
        match pv_of_id i with
          | SSL_3p0 -> CoreCrypto.blockSize alg
          | TLS_1p0 | TLS_1p1 | TLS_1p2 -> 256

(* Minimal padding length for a given plaintext length (in bytes) *)
val minimalPadding: id -> nat -> Tot nat
let minimalPadding i len =
  if PlaintextID? i then 0
  else
    let authEnc = aeAlg_of_id i in
    match authEnc with
    | MACOnly _ | AEAD _ _ | MtE (Stream _) _ -> fixedPadSize i
    | MtE (Block alg) _ ->
      let bs = CoreCrypto.blockSize alg in
      let lp = len % bs in
      bs - lp

(* Sanity check *)
#set-options "--initial_ifuel 2"
val minimalPadding_at_least_fixedPadSize: i:id -> len:nat ->
  Lemma (fixedPadSize i <= minimalPadding i len)
let minimalPadding_at_least_fixedPadSize _ _ = ()

val minMaxPad: id2 -> Tot range
#set-options "--initial_ifuel 2"
let minMaxPad i = (fixedPadSize i, maxPadSize i)
#set-options "--initial_ifuel 1"

// ADL: beware of this definition, for MtE padding it only requires
// clen - ivSize i - macSize (macAlg_of_id i) - maxPadSize i <= max_TLSPlaintext_fragment_length
// rather than the expected:
// clen - ivSize i - macSize (macAlg_of_id i) - fixedPadSize i <= max_TLSPlaintext_fragment_length
// valid_clen i c doesn't imply that the plaintext after decrypting c will be shorter than max_TLSPlaintext_fragment_length
let valid_clen (i:id) (clen:nat) =
 (if PlaintextID? i then
    0 <= clen && clen <= max_TLSPlaintext_fragment_length
  else if ID13? i then
    begin
    lemma_ID13 i;
    let tlen = CoreCrypto.aeadTagSize (aeAlg i) in
    clen - tlen >= 0 &&
    clen - tlen <= max_TLSCiphertext_fragment_length_13
    end
  else // ID12? i
    begin
    if AEAD? (aeAlg_of_id i) then
      let tlen = CoreCrypto.aeadTagSize (aeAlg i) in
      clen - AE.explicit_iv_length i - tlen >= 0 &&
      clen - AE.explicit_iv_length i - tlen <= max_TLSPlaintext_fragment_length
    else if MtE? (aeAlg_of_id i) then
      clen - ivSize i - UInt32.v (macSize (macAlg_of_id i)) - fixedPadSize i >= 0 &&
      clen - ivSize i - UInt32.v (macSize (macAlg_of_id i)) - maxPadSize i <= max_TLSPlaintext_fragment_length
    else // MACOnly
      let MACOnly h = aeAlg_of_id i in
      clen - UInt32.v (hashLen h) >= 0 &&
      clen - UInt32.v (hashLen h) <= max_TLSPlaintext_fragment_length
    end)

let min0 (i:int) : Tot (n:nat) = if i >= 0 then i else 0
let minP (n:int) : Tot (m:int{m <= n /\ m <= max_TLSPlaintext_fragment_length}) =
  if n >= max_TLSPlaintext_fragment_length then max_TLSPlaintext_fragment_length
  else n

#reset-options "--z3rlimit 30 --initial_fuel 1 --initial_ifuel 1 --max_fuel 1 --max_ifuel 1"
(* cipherRangeClass: given a ciphertext length, how long can the plaintext be? *)
val cipherRangeClass: i:id2 -> clen:nat -> Pure range
  (requires valid_clen i clen)
  (ensures fun r ->
    let (min, max) : range =
      match aeAlg_of_id i with
      | AEAD a _ ->
        let x = clen - AE.explicit_iv_length i - CoreCrypto.aeadTagSize a in (x,x)
      | MtE enc _ ->
        let m0 = clen - ivSize i - UInt32.v (macSize (macAlg_of_id i)) - maxPadSize i in
        let m1 = clen - ivSize i - UInt32.v (macSize (macAlg_of_id i)) - fixedPadSize i in
        (min0 m0, minP m1)
      | MACOnly h ->
        let x = clen - UInt32.v (hashLen h) in (x,x) in
    0 <= min /\ max <= max_TLSPlaintext_fragment_length /\ r == (min, max))

let cipherRangeClass i clen =
  match aeAlg_of_id i with
  | MACOnly h ->
    let hLen = hashLen h in
    let minmax = clen - UInt32.v hLen in
    minmax, minmax
  | MtE _ _ ->
    let ivL = ivSize i in
    let macLen = macSize (macAlg_of_id i) in
    let minPad, maxPad = minMaxPad i in
    let max = clen - ivL - UInt32.v macLen - minPad in
    let min = clen - ivL - UInt32.v macLen - maxPad in
    min0 min, minP max
  | AEAD aeadAlg _ ->
    let ivL = AE.explicit_iv_length i in
    let tagL = CoreCrypto.aeadTagSize aeadAlg in
    let minmax = clen - ivL - tagL in
    minmax, minmax


val cipherRangeClass_width: i:id2 ->
  clen:nat{valid_clen i clen} ->
  Lemma (snd (cipherRangeClass i clen) - fst (cipherRangeClass i clen) <= maxPadSize i - fixedPadSize i)
#set-options "--initial_ifuel 2"
let cipherRangeClass_width i clen = ()

(* targetLength: given a plaintext range, what would be the length of the ciphertext? *)
// TLS 1.2 RFC: For CBC, the encrypted data length is one more than the sum of
// block_length, TLSPlaintext.length, mac_length, and padding_length
val targetLength : i:id2 -> r:range -> Pure nat
  (requires
    fst r >= 0 /\ snd r <= max_TLSPlaintext_fragment_length /\
    (match aeAlg_of_id i with
    | MACOnly hash -> snd r - fst r <= maxPadSize i - minimalPadding i (snd r + UInt32.v (hashLen hash))
    | MtE a _ -> snd r - fst r <= maxPadSize i - minimalPadding i (snd r + UInt32.v (macSize (macAlg_of_id i)))
    | AEAD _ _ -> fst r = snd r))
  (ensures (fun clen ->
    valid_clen i clen /\
    wider (cipherRangeClass i clen) r))

#reset-options "--z3rlimit 30 --initial_fuel 1 --initial_ifuel 1 --max_fuel 4 --max_ifuel 4"
let targetLength i (l,h) =
  match aeAlg_of_id i with
  | MACOnly hash ->
    cut(l <= h); cut(l >= 0);
    cut(h <= max_TLSPlaintext_fragment_length);
    let hLen = hashLen hash in
    cut(UInt32.v hLen >= 0);
    let prePad = h + UInt32.v hLen in
    cut(prePad >= h); cut(prePad >= 0);
    let padLen = minimalPadding i prePad in
    prePad + padLen
  | MtE _ _ ->
    let ivL = ivSize i in
    cut(ivL >= 0);
    let macLen = macSize (macAlg_of_id i) in
    cut(UInt32.v macLen >= 0);
    let prePad = h + UInt32.v macLen in
    let padLen = minimalPadding i prePad in
    minimalPadding_at_least_fixedPadSize i prePad;
    let clen = ivL + UInt32.v macLen + padLen + h in
    cut(clen - ivL - UInt32.v macLen - maxPadSize i <= h);
    cut(h <= max_TLSPlaintext_fragment_length);
    cut(clen - ivL - UInt32.v macLen >= fixedPadSize i + l);
    cut(l >= 0);
    cut(clen - ivL - UInt32.v macLen - fixedPadSize i >= 0);
    cut(valid_clen i clen);
    clen
  | AEAD aeadAlg _ ->
    cut(AEAD? (aeAlg_of_id i));
    let ivL = AE.explicit_iv_length i in
    cut(ivL >= 0);
    let tagL = CoreCrypto.aeadTagSize aeadAlg in
    cut(tagL >= 0);
    let fp = fixedPadSize i in
    cut(fp = 0);
    let clen = ivL + h + fp + tagL in
    cut(clen - ivL - tagL - fp = h);
    cut(h >= 0);
    cut(h <= max_TLSPlaintext_fragment_length);
    cut(clen - ivL - tagL - fp <= max_TLSPlaintext_fragment_length);
    clen

(* This is the high-level spec for targetLength (for non-AEAD ciphers):

   forall i. forall r. forall x in r. exists plen.
     minimalPadding i (x + macLen) <= plen <= maxPadSize i
     /\ targetLength i r = ivSize i + x + macLen i + plen

   Because how minimalPadding is defined, we don't require the lower bound
   minimalPadding i (l + macLen i) - minimalPadding i (h + macLen i) <= h - l
   This always holds when l <= h
*)

(* Sanity check
  val targetLength_spec_nonAEAD: i:id2{~(AEAD? (aeAlg_of_id i))}
  -> r:range{
      snd r <= max_TLSPlaintext_fragment_length
      /\ (~(AEAD? (aeAlg_of_id i)) ==>
   	snd r - fst r <= maxPadSize i - minimalPadding i (snd r + macSize (macAlg_of_id i)))
     /\ (AEAD? (aeAlg_of_id i) ==> fst r = snd r)}
  -> x:nat{within x r}
  -> Lemma (let clen = targetLength i r in
   	let plen = clen - x - macSize (macAlg_of_id i) - ivSize i in
   	minimalPadding i (x + macSize (macAlg_of_id i)) <= plen
   	/\ plen <= maxPadSize i
   	/\ clen = ivSize i + x + macSize (macAlg_of_id i) + plen)
  #set-options "--initial_ifuel 2"
  let targetLength_spec_nonAEAD i r x = ()
*)

(* Sanity check
  val targetLength_spec_AEAD: i:id2{AEAD? (aeAlg_of_id i)}
  -> r:range{fst r = snd r /\ snd r <= max_TLSPlaintext_fragment_length}
  -> x:nat{within x r} ->
  Lemma (let clen = targetLength i r in
   	   let plen = fixedPadSize i in
   	   minimalPadding i (x + aeadTagSize (aeAlg i)) <= plen
   	   /\ plen <= maxPadSize i
   	   /\ clen = AE.explicit_iv_length i + x + aeadTagSize (aeAlg i) + plen)
  let targetLength_spec_AEAD i r x = ()
*)

#reset-options
#set-options "--initial_fuel 0 --initial_ifuel 2 --max_fuel 0 --max_ifuel 2"

val targetLength_at_most_max_TLSCiphertext_fragment_length: i:id2
   -> r:range{
       snd r <= max_TLSPlaintext_fragment_length /\
       (match aeAlg_of_id i with
       | MACOnly hash -> snd r - fst r <= maxPadSize i - minimalPadding i (snd r + UInt32.v (hashLen hash))
       | MtE a _ -> snd r - fst r <= maxPadSize i - minimalPadding i (snd r + UInt32.v (macSize (macAlg_of_id i)))
       | AEAD _ _ -> fst r = snd r)}
   -> Lemma (targetLength i r <= max_TLSCiphertext_fragment_length)
#set-options "--z3rlimit 60"
//without hints, this next query succeeds in around 19s on a powerful desktop; that's too close the default 20s timeout for CI
//with hints, it takes about 3.5s on the same machine. So, for CI with hints, the 60s timeouts is very generous but harmless
//At least with the long timeout it should work reliably with or without hints
let targetLength_at_most_max_TLSCiphertext_fragment_length i r = ()

#set-options "--z3rlimit 100 --initial_fuel 1 --initial_ifuel 1 --max_fuel 2 --max_ifuel 2 --admit_smt_queries true"
val targetLength_converges: i:id2
  -> r:range{
      snd r <= max_TLSPlaintext_fragment_length /\
      (match aeAlg_of_id i with
      | MACOnly hash -> snd r - fst r <= maxPadSize i - minimalPadding i (snd r + UInt32.v (hashLen hash))
      | MtE a _ -> snd r - fst r <= maxPadSize i - minimalPadding i (snd r + UInt32.v (macSize (macAlg_of_id i)))
      | AEAD _ _ -> fst r = snd r)}
  -> Lemma (targetLength i r = targetLength i (cipherRangeClass i (targetLength i r)))
// SZ: This used to be slow without hints, see Issue #164
let targetLength_converges i r = 
  lemma_MtE i; lemma_ID12 i;
  match aeAlg_of_id i with
  | MACOnly hash -> ()
  | MtE a _ -> ()
  | AEAD _ _ -> ()

#reset-options "--initial_fuel 0 --initial_ifuel 1 --max_fuel 0 --max_ifuel 1"
val rangeClass: i:id2 -> r:range -> HyperStack.All.ML (r':range
  { snd r <= max_TLSPlaintext_fragment_length
    /\ ((~(AEAD? (aeAlg_of_id i))
       /\ snd r - fst r <= maxPadSize i - minimalPadding i (snd r + UInt32.v (macSize (macAlg_of_id i))))
    \/ (AEAD? (aeAlg_of_id i) /\ fst r = snd r))
    /\ r' = cipherRangeClass i (targetLength i r) })
let rangeClass i (r:range) =
    if MACOnly? (aeAlg_of_id i) && not(SSL_3p0? (pv_of_id i)) then
        Error.unexpected "[rangeClass] given an invalid algorithm identifier"
    else
        if (snd r <= max_TLSPlaintext_fragment_length &&
            (not(AEAD? (aeAlg_of_id i)) && snd r - fst r <= maxPadSize i - minimalPadding i (snd r + UInt32.v (macSize (macAlg_of_id i)))
            || (AEAD? (aeAlg_of_id i) && fst r = snd r)))
        then
            let tlen = targetLength i r in
            match (aeAlg_of_id i) with
            | MACOnly _
            | MtE (Stream _) _
            | MtE (Block _) _ ->
                let ivL = ivSize i in
                let macLen = UInt32.v (macSize (macAlg_of_id i)) in
                let minPad, maxPad = minMaxPad i in
                let max = tlen - ivL - macLen - minPad in
                if tlen <= max_TLSCiphertext_fragment_length then
                    cipherRangeClass i tlen
                else
                    //Unreachable when snd r <= max_TLSPlaintext_fragment_length (see lemma below)
                    Error.unexpected "[rangeClass] given an invalid plaintext length."
            | AEAD _ _ -> cipherRangeClass i tlen
        else
            Error.unexpected "[rangeClass] given an invalid range."


// in encryptor logs, we do not precisely keep track of written ranges
let fragment_range: range = (0,max_TLSPlaintext_fragment_length)

// for writers, we keep track of actual ranges
// and we require point ranges when padding is not available.
type frange (i:id) = rg:range{
  wider fragment_range rg /\
  ((ID12? i /\ lhae (aeAlg_of_id i))
  \/ ID13? i
  \/ fst rg = snd rg)
}

// we don't need the index for point ranges (e.g. non-appdata traffic)
type frange_any = rg:range { wider fragment_range rg /\ fst rg = snd rg }
