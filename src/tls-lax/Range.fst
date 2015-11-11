(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Range

open Platform.Bytes
open TLSConstants
open TLSInfo
open CoreCrypto

type range = nat * nat 
type rbytes = bytes 

let sum (l0,h0) (l1,h1) =
  let l = l0 + l1 in
  let h = h0 + h1 in
  (l,h)

let ivSize (e:id) =
    let authEnc = e.aeAlg in
    match authEnc with
    | MACOnly _ -> 0
    | MtE encAlg _ ->
        (match encAlg with
        | Stream RC4_128 -> 0
        | Block alg -> blockSize alg)
    | AEAD _ _ -> Platform.Error.unexpected "[ivSize] invoked on wrong ciphersuite"

let fixedPadSize id =
#if TLSExt_extendedPadding
    if TLSExtensions.hasExtendedPadding id then
        2
    else
#endif
        let authEnc = id.aeAlg in
        match authEnc with
        | MACOnly _ | AEAD _ _ -> 0
        | MtE enc _ ->
            match enc with
            | Stream RC4_128 -> 0
            | Block _ -> 1
    
    
let maxPadSize id =
#if TLSExt_extendedPadding
    if TLSExtensions.hasExtendedPadding id then  
        fragmentLength
    else
#endif
        let authEnc = id.aeAlg in
        match authEnc with
        | MACOnly _ | AEAD _ _ -> 0
        | MtE enc _  ->
                match enc with
                | Stream _ -> 0
                | Block alg ->
                    match id.pv with
                    | SSL_3p0 -> blockSize alg
                    | TLS_1p0 | TLS_1p1 | TLS_1p2 -> 256

let minimalPadding e len =
    let authEnc = e.aeAlg in
    match authEnc with
    | MACOnly _ | AEAD _ _  -> fixedPadSize e
    | MtE enc _  ->
        match enc with
        | Stream _ -> fixedPadSize e
        | Block alg ->
            let bs = blockSize alg in
            let lp = (len % bs) in 
            let p = bs - lp in
#if TLSExt_extendedPadding
            let fp = fixedPadSize e in
            let p =
                if p < fp then
                    p + bs
                else
                    p in
#endif
            if p < 0 then
                Platform.Error.unreachable ""
            else p

#if TLSExt_extendedPadding
let alignedRange e (rg:range) =
    let (l,h) = rg in
    let authEnc = e.aeAlg in
    match authEnc with
    | MtE enc mac ->
        (match enc with
        | Stream _ ->
            let mp = minimalPadding e h in
            (l,h+mp)
        | Block _ ->
        let (l,h) = rg in
        let macLen = macSize (macAlg_of_id e) in
        let prePad = h + macLen in
        let mp = minimalPadding e prePad in
        (l,h+mp))
    | MACOnly _ | AEAD _ _ ->
        let mp = minimalPadding e h in
        (l,h+mp)

let extendedPad (id:id) (rg:range) (plen:nat) =
    let rg = alignedRange id rg in
    let fp = fixedPadSize id in
    let (_,h) = rg in
    let padlen = h - plen - fp in
    let pad = createBytes padlen 0 in
    TLSConstants.vlbytes fp pad
#endif

//@ From plaintext range to ciphertext length 
let targetLength e (rg:range) =
    let (_,h) = rg in
    let authEnc = e.aeAlg in
    match authEnc with
    | MACOnly ha | MtE (Stream _) ha 
    | MtE (Block _) ha ->
        let macLen = macSize (macAlg_of_id e) in
        let ivL = ivSize e in
        let prePad = h + macLen in
        let padLen = minimalPadding e prePad in
        let res = ivL + prePad + padLen in
        if res > max_TLSCipher_fragment_length then
            Platform.Error.unexpected "[targetLength] given an invalid input range."
        else
            res
    | AEAD aeadAlg _ ->
        let ivL = aeadRecordIVSize aeadAlg in
        let tagL = aeadTagSize aeadAlg in
        let fp = fixedPadSize e in // 0, by refinement
        let res = ivL + h + fp + tagL in
        if res > max_TLSCipher_fragment_length then
            Platform.Error.unexpected "[targetLength] given an invalid input range."
        else
            res


let minMaxPad (i:id) =
    let maxPad = maxPadSize i in
    let fp = fixedPadSize i in
    (fp,maxPad) 

//@ From ciphertext length to (maximal) plaintext range
let cipherRangeClass (e:id) tlen =
    let authEnc = e.aeAlg in
    match authEnc with
    | MACOnly _ | MtE (Stream _) _ 
    | MtE (Block _ ) _ ->
        let macLen = macSize (macAlg_of_id e) in
        let ivL = ivSize e in
        let (minPad,maxPad) = minMaxPad e in
        let max = tlen - ivL - macLen - minPad in
        if max < 0 then
            Platform.Error.unexpected "[cipherRangeClass] the given tlen should be of a valid ciphertext"
        else
            let min = tlen - ivL - macLen - maxPad in
            if min < 0 then
                (0,max)
            else
                (min,max)
    | AEAD aeadAlg _ ->
        let ivL = aeadRecordIVSize aeadAlg in
        let tagL = aeadTagSize aeadAlg in
        let (minPad,maxPad) = minMaxPad e in
        let max = tlen - ivL - tagL - minPad in
        if max < 0 then
            Platform.Error.unexpected "[cipherRangeClass] the given tlen should be of a valid ciphertext"
        else
            let min = tlen - ivL - tagL - maxPad in
            if min < 0 then
                (0,max)
            else
                (min,max)

let rangeClass (e:id) (r:range) =
    let tlen = targetLength e r in
    cipherRangeClass e tlen
