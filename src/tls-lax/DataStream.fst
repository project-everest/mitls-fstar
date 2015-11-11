(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module DataStream
open TLSConstants
open TLSInfo
open Platform.Bytes
open Platform.Error
open TLSError
open Range

let min (a:nat) (b:nat) =
    if a <= b then a else b

let maxLHPad id len =
    let fs = TLSInfo.fragmentLength in
    let ps = maxPadSize id in
    let thisPad = min ps (fs-len) in
    let authEnc = id.aeAlg in
    match authEnc with
    | MtE encAlg macAlg ->
        (match encAlg with
        | Stream _ -> thisPad
        | Block alg ->
            let bs = blockSize alg in
            let ms = macSize (macAlg_of_id id) in
            let pl = fixedPadSize id in
            let overflow = (len + thisPad + ms + ps) % bs in
            if overflow > thisPad then
                thisPad
            else
                thisPad - overflow)
    | AEAD _ _ ->
        thisPad
    | _ -> unexpected "[maxLHPad] invoked on an invalid ciphersuite"

let splitRange ki r =
    let (l,h) = r in
    let si = epochSI(ki) in
    let cs = si.cipher_suite in
    let fs = TLSInfo.fragmentLength in
    let id = mk_id ki in
    let ps = maxPadSize id in
    if ps = 0 || l = h then
        // no LH to do
        if l<>h then
            unexpected "[splitRange] Incompatible range provided"
        else
            let len = min h fs in
            let r0 = (len,len) in
            let r1 = (l-len,h-len) in
            (r0,r1)
    else
        if l >= fs then
            let r0 = (fs,fs) in
            let r1 = (l-fs,h-fs) in
            (r0,r1)
        else
            let allPad = maxLHPad id l in
            let allPad = min allPad (h-l) in
            if l+allPad > fs then
                unexpected "[splitRange] Computing range over fragment size"
            else
                let r0 = (l,l+allPad) in
                let r1 = (0,h - (l+allPad)) in
                (r0,r1)

type stream = {sb: list cbytes}
type delta = {contents: rbytes}

let createDelta (ki:epoch) (s:stream) (r:range) (b:bytes) = {contents = b}
let deltaBytes  (ki:epoch) (s:stream) (r:range) (d:delta) = d.contents
let deltaPlain  (ki:epoch) (s:stream) (r:range) (b:rbytes) = {contents = b}
let deltaRepr   (ki:epoch) (s:stream) (r:range) (d:delta) = d.contents

// ghost
type es = | EmptyStream of epoch

let init (ki:epoch) = {sb = []}

//CF 14-07-15 why this hack, just for performance?  
let append (ki:epoch) (s:stream) (r:range) (d:delta) =
#if ideal
    let dc = d.contents in
    let c = cbytes dc in
    {sb = c :: s.sb}
#else
    s
#endif

let split (ki:epoch) (s:stream)  (r0:range) (r1:range) (d:delta) = 
  let (_,h0) = r0 in
  let (l1,_) = r1 in
  let len = length d.contents in
  let n = if h0 < (len - l1) then h0 else len - l1 in
  let (sb0,sb1) = Platform.Bytes.split d.contents n in
  ({contents = sb0},{contents = sb1})

#if ideal
let widen (ki:epoch) (s:stream) (r0:range) (r1:range) (d:delta) = let b = d.contents in {contents = b}
#endif
