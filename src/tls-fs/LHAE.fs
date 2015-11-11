(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module LHAE
//open Seq
open Bytes
open TLSConstants
open TLSInfo
open Error
open TLSError
open Range

type cipher = bytes

(***** keying *****) 

type LHAEKey =
    | MtEK of MAC.key * ENC.state
    | MACOnlyK of MAC.key
    | GCM of AEAD_GCM.state

type encryptor = LHAEKey
type decryptor = LHAEKey

let gen e =
    let a = e.aeAlg in
    match a with
    | MACOnly _ ->
        let mk = MAC.gen e in
        (MACOnlyK(mk), MACOnlyK(mk))
    | MtE(_,_)  ->
        let mk = MAC.gen e in
        let (ek,dk) = ENC.gen e in
        (MtEK(mk,ek),MtEK(mk,dk))
    | AEAD (_,_) ->  
        let (ek,dk) = AEAD_GCM.gen e in
        GCM(ek),GCM(dk)

let coerce e rw b =
    // precondition: b is of the right length, so no need for a runtime checks here.
    let a = e.aeAlg in
    match a with
    | MACOnly _ -> 
        let mk = MAC.coerce e b in
        MACOnlyK(mk)
    | MtE (encalg, macalg) ->
        let ms = macKeySize macalg in
        let es = encKeySize encalg in
        let (mkb,rest) = split b ms in
        let (ekb,ivb) = split rest es in
        let mk = MAC.coerce e mkb in
        let ek = ENC.coerce e rw ekb ivb in
        MtEK(mk,ek)
    | AEAD( encAlg, _ )->
        let es = aeadKeySize encAlg in
        let (ekb,ivb) = split b es in
        let ek = AEAD_GCM.coerce e rw ekb ivb in
        GCM(ek)
        

let leak e rw k =
    match k with
    | MACOnlyK(mk) -> MAC.leak e mk
    | MtEK (mk,ek) ->
        let (k,iv) = ENC.leak e rw ek in
        MAC.leak e mk @| k @| iv
    | GCM(s) ->
        AEAD_GCM.leak e rw s

(***** authenticated encryption *****)

let encrypt' (e:id) key data rg plain =
    let authEnc = e.aeAlg in
    match (authEnc,key) with
    | (MtE( encAlg ,_), MtEK (ka,ke)) ->
        (match encAlg with
        | Stream_RC4_128 -> // stream cipher
            let plain   = Encode.mac e ka data rg plain in
            let (l,h) = rg in
            if
#if TLSExt_extendedPadding
                (not (TLSExtensions.hasExtendedPadding e)) &&
#endif
                l <> h then
                unexpected "[encrypt'] given an invalid input range"
            else
                let (ke,res) = ENC.enc e ke data rg plain in
                (MtEK(ka,ke),res)
        | CBC_Stale(_) | CBC_Fresh(_) -> // block cipher
            let plain  = Encode.mac e ka data rg plain in
            let (ke,res) = ENC.enc e ke data rg plain in
            (MtEK(ka,ke),res))
    | (MACOnly _, MACOnlyK (ka)) ->
        let plain = Encode.mac e ka data rg plain in
        let (l,h) = rg in
        if l <> h then
            unexpected "[encrypt'] given an invalid input range"
        else
            let r = Encode.repr e data rg plain in
            (key,r)
    | (AEAD (encAlg, _), GCM(gcmState)) ->
        let (l,h) = rg in
        if
#if TLSExt_extendedPadding
            (not (TLSExtensions.hasExtendedPadding e)) &&
#endif
            l <> h then
            unexpected "[encrypt'] given an invalid input range"
        else
            let (newState,res) = AEAD_GCM.enc e gcmState data rg plain in
            (GCM(newState),res)
    | (_,_) -> unexpected "[encrypt'] incompatible ciphersuite-key given."
        
let mteKey (e:id) (rw:rw) ka ke = MtEK(ka,ke)
let gcmKey (e:id) (rw:rw) st = GCM(st)

let decrypt' e key data cipher =
    let cl = length cipher in
    // by typing, we know that cl <= max_TLSCipher_fragment_length
    let authEnc = e.aeAlg in
    match (authEnc,key) with
    | (MtE (encAlg, macAlg), MtEK (ka,ke)) ->
        let macSize = macSize macAlg in
        (match encAlg with
        | Stream_RC4_128 -> // stream cipher
            if cl < macSize then
                (*@ It is safe to return early, because we are branching
                    on public data known to the attacker *)
                let reason = perror __SOURCE_FILE__ __LINE__ "" in Error(AD_bad_record_mac, reason)
            else
                let rg = cipherRangeClass e cl in
                let (ke,plain) = ENC.dec e ke data cipher in
                let nk = mteKey e Reader ka ke in
                (match Encode.verify e ka data rg plain with
                | Error z -> Error z
                | Correct(aeplain) -> correct(nk,rg,aeplain))
        | CBC_Stale(alg) | CBC_Fresh(alg) -> // block cipher
            let ivL = ivSize e in
            let blockSize = blockSize alg in
            let fp = fixedPadSize e in
            if (cl - ivL < macSize + fp) || (cl % blockSize <> 0) then
                (*@ It is safe to return early, because we are branching
                    on public data known to the attacker *)
                let reason = perror __SOURCE_FILE__ __LINE__ "" in Error(AD_bad_record_mac, reason)
            else
                let rg = cipherRangeClass e cl in
                let (ke,plain) = ENC.dec e ke data cipher in
                let nk = mteKey e Reader ka ke in
                (match Encode.verify e ka data rg plain with
                | Error z -> Error z
                | Correct(aeplain) -> correct (nk,rg,aeplain)))
    | (MACOnly macAlg, MACOnlyK (ka)) ->
        let macSize = macSize macAlg in
        if cl < macSize then
            let reason = perror __SOURCE_FILE__ __LINE__ "" in Error(AD_bad_record_mac, reason)
        else
            let rg = cipherRangeClass e cl in
            let (plain,tag) = Encode.decodeNoPad_bytes e data rg cl cipher in
            (match Encode.verify_MACOnly e ka data rg cl plain tag with
            | Error(z) -> Error(z)
            | Correct(x) -> let rg,aeplain = x in correct (key,rg,aeplain))
    | (AEAD (encAlg, _) , GCM(gcmState)) ->
        let minLen = aeadRecordIVSize encAlg + aeadTagSize encAlg in
        if cl < minLen then
            let reason = perror __SOURCE_FILE__ __LINE__ "" in Error(AD_bad_record_mac, reason)
        else
            let rg = cipherRangeClass e cl in
            (match AEAD_GCM.dec e gcmState data rg cipher with
            | Error z -> Error z
            | Correct (res) ->
                let (newState,plain) = res in
                let nk = gcmKey e Reader newState in
                correct (nk,rg,plain))
    | (_,_) -> unexpected "[decrypt'] incompatible ciphersuite-key given."

#if ideal

type preds = | ENCrypted of id * LHAEPlain.adata * range * LHAEPlain.plain * cipher

type entry = id * LHAEPlain.adata * range * LHAEPlain.plain * ENC.cipher
let log = ref ([]: list<entry>) // for defining the ideal functionality for INT-CTXT

let rec cmem (e:id) (ad:LHAEPlain.adata) (c:ENC.cipher) (xs: list<entry>) = 
#if verify
  failwith "specification only" //MK seems pretty bad. CF 14-07-16 needs fixing
#else
  match xs with
  | (e',ad',r,p,c')::_ when e=e' && ad=ad' && c=c' -> let x = (r,p) in Some x
  | _::xs                  -> cmem e ad c xs 
  | []                     -> None
#endif
#endif

let encrypt (e:id) key data rg plain = 
  let (key,cipher) = encrypt' e key data rg plain in
#if ideal_F
  if safeId  e then
    log := (e,data,rg,plain,cipher)::!log
  else ()
#endif
#if ideal
  (* CF we do not log in all cases, as we do not have ENCrypted for MAC-only suites *)
  if safeId  e then
    log := (e,data,rg,plain,cipher)::!log
  else ();
#endif
  (key,cipher)

let decrypt (e:id) (key: LHAEKey) data (cipher: bytes) = 
  let err = (AD_bad_record_mac,"") in
#if ideal_F
  if safeId  e then
    match cmem e data cipher !log with
    | Some _ -> decrypt' e key data cipher
    | None   -> Error err
  else
#endif 
#if ideal
  if safeId  e then
    match cmem e data cipher !log with
    | Some x -> 
       let (r,p) = x in
       let p' = LHAEPlain.widen e data r p in
       let tlen = length cipher in
       let rg' = cipherRangeClass e tlen in
       correct (key,rg',p')
    | None   -> Error err
  else
#endif 
      decrypt' e key data cipher
