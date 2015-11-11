(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module LHAE

(* Implements Length-Hiding Authenticated Encryption
   for all "aeAlg" constructions: MtE, MacOnly, GCM;
   used by StatefulLHAE, parameterized by LHAEPlain. *)

open FStar.Seq

open Platform.Bytes
open Platform.Error

open TLSError
open TLSConstants
open TLSInfo
open Range

type cipher = b:bytes { length b <= max_TLSCipher_fragment_length }

(***** keying *****)

type LHAEKey (i:id) (rw:rw) =
    | MtEK of MAC.key i * ENC.state i rw
    | MACOnlyK of MAC.key i
    | GCM of AEAD_GCM.state i rw

type encryptor (i:id) = LHAEKey i Writer
type decryptor (i:id) = LHAEKey i Reader

(* 15-04-11 recheck usage of these functions *)

let keyDerivationIVSize = function
  | MtE(CBC_Stale(enc),mac)) -> blockSize enc
  | _                        -> 0

let keySize = function
  | MACOnly(mac)  -> macKeySize mac
  | MtE(enc,mac)  -> macKeySize mac + encKeySize enc + keyDerivationIVSize(MtE(enc,mac))
  | AEAD(enc,prf) -> AEADKeySize(enc) + AEADIVSize(enc)

type keyrepr i = lbytes (keySize i.aeAlg)

val gen:    i:id -> (encryptor i * decryptor i)
val coerce: i:id { ~(authId i) } -> rw:rw -> keyrepr i -> LHAEKey i rw
val leak:   i:id { ~(authId i) } -> rw:rw -> LHAEKey i rw -> keyrepr i

let gen e =
    let a = e.aeAlg in
    match a with
    | MACOnly _ ->
        let mk = MAC.gen e in
        (MACOnlyK mk, MACOnlyK mk)
    | MtE _ _  ->
        let mk = MAC.gen e in
        let (ek,dk) = ENC.gen e in
        (MtEK(mk,ek),MtEK(mk,dk))
    | AEAD _ _ ->
        let (ek,dk) = AEAD_GCM.gen e in
        GCM ek, GCM dk

let coerce e rw b =
    let a = e.aeAlg in
    match a with
    | MACOnly _ ->
        let mk = MAC.coerce e b in
        MACOnlyK(mk)
    | MtE encalg macalg ->
        let (mkb,rest) = split b (macKeySize macalg) in
        let (ekb,ivb) = split rest (encKeySize encalg) in
        let mk = MAC.coerce e mkb in
        let ek = ENC.coerce e rw ekb ivb in
        MtEK(mk,ek)
    | AEAD encAlg _ ->
        let (ekb,ivb) = split b (aeadKeySize encAlg) in
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

//?
//private val mteKey: i:id -> rw:rw -> (;i) MAC.key -> (;i,rw) ENC.state -> (;i,rw) LHAEKey
//private val gcmKey: i:id -> rw:rw -> (;i,rw) AEAD_GCM.state -> (;i,rw)LHAEKey
let mteKey (e:id) (rw:rw) ka ke = MtEK(ka,ke)
let gcmKey (e:id) (rw:rw) st = GCM(st)

(***** authenticated encryption *****)

// We have two variants for encryption and decryption:
// the first (primed) is concrete; the second is idealized at safe indexes,
// using either #ideal_F (filtering out non-cipher) or #ideal (decrypting just by lookup)

// could be modelled as a log
type Encrypted (i:id) (ad:LHAEPlain.data i) (c:cipher) =
    match i.aeAlg with
    | MtE(enc,mac)   -> exists p. ENC.Encrypted e ad c p
    | AEAD(aenc,mac) -> exists p. AEAD_GCM.Encrypted e ad c p
    | _              -> false

// TODO stateful
// TODO define entry
(*
type entry =
  i:id * ad:(;i) LHAEPlain.adata * rg:range *
  p:(;i,ad,rg) LHAEPlain.plain * c:ENC.cipher {ENCrypted(i,ad,c)}
private val log: entry list ref
private val cmem: i:id -> ad:(;i)LHAEPlain.adata -> c:cipher ->
  entry list -> res:(r:range * (;i,ad,r)LHAEPlain.plain) option {
    ( !rg,p. res = Some ((rg,p)) => (ENCrypted(i,ad,c) /\ rg = CipherRangeClass(i,Length(c))) ) /\
	( res = None => not ENCrypted(i,ad,c) )}
//CF 14-07-17 we effectively assume this non-trivial postcondition; TODO.
 *)

private val encrypt':
  i:id -> encryptor i -> ad:LHAEPlain.adata i -> rg:range -> p:LHAEPlain.plain i ad rg ->
  (encryptor i * c:cipher)
    { Seq.length c = TargetLength i rg  /\
      (safeId i ==> Encrypted i ad c) }

val encrypt :
  i:id -> encryptor i -> ad:LHAEPlain.adata i -> rg:range -> p:LHAEPlain.plain i ad rg ->
  (encryptor i * c:cipher)
    { Seq.Length c = TargetLength i rg /\
      (SafeId(i) => Encrypted i ad c) }

let encrypt' (e:id) key data rg plain =
    let authEnc = e.aeAlg in
    match (authEnc,key) with
    | (MtE encAlg _, MtEK (ka,ke)) ->
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
    | (AEAD encAlg _, GCM(gcmState)) ->
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


private val decrypt':
  i:id -> k:decryptor i -> ad:LHAEPlain.adata i ->
  c:cipher{ safeId i ==> Encrypted i ad c } ->
  ( ((;i) decryptor * rg:range * p:LHAEPlain.plain i ad rg)
      {rg = cipherRangeClass i (length c)}
  ) Result
(* TODO MK seems outdated: partial functional correctness when decrypting what we encrypted
  {
   !pl,p,tag,rg.
	(    Length(c) = EncryptedLength(i,rg)
	  /\ MACed(e,ad,pl,tag)
     /\ Encoded(e,ad,pl,tag,p)
     /\ ENCrypted(e,Length(c),StateID(e,Encryptor(k)),c,p)
   => ?k',r'. res = Correct((k',r',pl)) }
*)

val decrypt:
  i:id -> decryptor i -> ad:LHAEPlain.adata i ->
  c:cipher -> res:
  ( ((;i) decryptor *  rg:range * (;i,ad,rg) LHAEPlain.plain)
     {rg = cipherRangeClass i (length c)}
  ) Result
   {
     (safeId i ==>
        (forall p. ENC.Encrypted i ad c p <==> exists k r. res = Correct (k,r,p)))}

let decrypt' e key data cipher =
    let cl = length cipher in
    // by typing, we know that cl <= max_TLSCipher_fragment_length
    let authEnc = e.aeAlg in
    match (authEnc,key) with
    | (MtE encAlg macAlg, MtEK (ka,ke)) ->
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
    | (AEAD encAlg _ , GCM(gcmState)) ->
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

let rec cmem (e:id) (ad:LHAEPlain.adata) (c:ENC.cipher) (xs: list entry) =
#if verify
  failwith "specification only" //MK seems pretty bad. CF 14-07-16 needs fixing
#else
  match xs with
  | (e',ad',r,p,c')::_ when e=e' && ad=ad' && c=c' -> let x = (r,p) in Some x
  | _::xs                  -> cmem e ad c xs
  | []                     -> None
#endif
#endif

let encrypt (e:id) key ad rg plain =
  let (key,cipher) = encrypt' e key ad rg plain in
#if ideal_F
  if safeId  e then
    log := (e,ad,rg,plain,cipher)::!log
  else ()
#endif
#if ideal
  (* CF we do not log in all cases, as we do not have ENCrypted for MAC-only suites *)
  if safeId  e then
    log := (e,ad,rg,plain,cipher)::!log
  else ();
#endif
  (key,cipher)

let decrypt (e:id) (key: LHAEKey) ad (cipher: bytes) =
  let err = (AD_bad_record_mac,"") in
#if ideal_F
  if safeId  e then
    match cmem e ad cipher !log with
    | Some _ -> decrypt' e key ad cipher
    | None   -> Error err
  else
#endif
#if ideal
  if safeId  e then
    match cmem e ad cipher !log with
    | Some x ->
       let (r,p) = x in
       let p' = LHAEPlain.widen e ad r p in
       let tlen = length cipher in
       let rg' = cipherRangeClass e tlen in
       correct (key,rg',p')
    | None   -> Error err
  else
#endif
      decrypt' e key ad cipher
