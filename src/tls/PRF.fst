module PRF

(* 16-05-17 removed precompilation flags, commenting out ideal code still to be upgraded to F* *)

open FStar.Seq
open Platform.Bytes
open TLSConstants
open TLSInfo
open CoreCrypto

type repr = bytes
type ms = { bytes: repr }
type masterSecret = ms

(* ideal 
let sample (i:msId) = {bytes = Nonce.random 48}
*)

let coerce (i:msId) b = {bytes = b}
let leak (i:msId) ms = ms.bytes

(* Key Derivation *) 

let keyExtensionLength i =
    let op_Star x y = op_Multiply x y in
    match (aeAlg_of_id i) with
        | MtE _ _  ->
            let alg,ivm = encAlg_of_id i in
            let esize = encKeySize alg in
            let msize = macKeySize (macAlg_of_id i) in 
            (match alg,ivm with
                | Stream _,_ | Block _, Fresh -> 
                    2 * (esize + msize)
                | Block e, Stale -> 
                    let bsize = blockSize e in
                    2 * (esize + bsize + msize))
        | MACOnly (macAlg) ->
            let msize = macKeySize (macAlg_of_id i) in 
            2 * msize
        (* AEAD currently not fully implemented or verified *)               
        | AEAD cAlg _  ->
            let aksize = AEADProvider.key_length i in
            let ivsize = AEADProvider.salt_length i in
            2 * (aksize + ivsize)


// This code is complex because we need to reshuffle the raw key materials  
let deriveRawKeys (i:id) (ms:ms)  =
    // we swap the CR and SR for this derivation
    let crand, srand = split i.csrConn 32 in
    let data = srand @| crand in
    let ae = (aeAlg_of_id i) in
    let len = keyExtensionLength i in
    let b = TLSPRF.kdf i.kdfAlg ms.bytes data len in
    match ae with
    | MACOnly macAlg ->
        let msize = macKeySize (macAlg_of_id i) in 
        let ck,sk = split b msize in
        (ck,sk) 
    | MtE encAlg macAlg ->
        let alg,ivm = encAlg_of_id i in
        let encKeySize = encKeySize alg in
        let macKeySize = macKeySize (macAlg_of_id i) in 
        (match alg,ivm with
        | Stream _,_ | Block _, Fresh ->
            let cmkb, b = split b macKeySize in
            let smkb, b = split b macKeySize in
            let cekb, b = split b encKeySize in
            let sekb, b = split b encKeySize in 
            let ck = (cmkb @| cekb) in
            let sk = (smkb @| sekb) in
            (ck,sk)
        | Block alg, Stale ->
            let cmkb, b = split b macKeySize in
            let smkb, b = split b macKeySize in
            let cekb, b = split b encKeySize in
            let sekb, b = split b encKeySize in 
            let ivsize = blockSize alg in
            let civb, sivb = split b ivsize in
            let ck = (cmkb @| cekb @| civb) in
            let sk = (smkb @| sekb @| sivb) in
            (ck,sk))
    (* AEAD currently not fully implemented or verified *)
    | AEAD encAlg prf ->
        let aksize = AEADProvider.key_length i in
        let ivsize = AEADProvider.salt_length i in
        let cekb, b = split b aksize in
        let sekb, b = split b aksize in
        let civb, sivb = split b ivsize in
        let ck = (cekb @| civb) in
        let sk = (sekb @| sivb) in
        (ck,sk)


type derived (i1:id) (i2:id) = StatefulLHAE.reader i1 * StatefulLHAE.writer i2 

noeq type state =
  | Init
  // 2017.05.21: Removed negotiatedExtensions. Replace args by mode?
  | Committed of protocolVersion * aeAlg (* * negotiatedExtensions *)
  | Derived: a:id -> b:id -> derived a b -> state
//  | Done 
//  | Wasted



(* ideal

type event = Mismatch of id

type kdentry = csRands * state 
let kdlog : ref<list<kdentry>> = ref [] 

let rec read csr (entries: list<kdentry>)  = 
  match entries with
  | []                                 -> Init 
  | (csr', s)::entries when (csr = csr') -> s
  | (csr', s)::entries                 -> read csr entries

let rec update csr s (entries: list<kdentry>) = 
  match entries with 
  | []                                  -> [(csr,s)]
  | (csr', s')::entries when (csr = csr') -> (csr,s)   :: entries 
  | (csr', s')::entries                 -> (csr', s'):: update csr s entries

//CF to circumvent an F7 limitation?
let commit csr pv a ext = Committed(pv,a,ext)
*)

//CF We could statically enforce the state machine.



let keyCommit (csr:csRands) (pv:protocolVersion) (a:aeAlg) (* (ext:negotiatedExtensions) *) : unit =
(* ideal
  match read csr !kdlog with 
  | Init -> 
      Pi.assume(keyCommit(csr,pv,a,ext));
      let state = commit csr pv a ext in
      kdlog := update csr state !kdlog
  | _    -> 
      FStar.Error.unexpected "prevented by freshness of the server random"
*)
  ()

let wrap (rdId:id) (wrId:id) r w = (r,w)
let wrap2 (a:id) (b:id) rw csr = Derived a b rw

let deriveKeys rdId wrId (ms:masterSecret) role  =
    let (ck,sk) = deriveRawKeys rdId ms in
    match role with 
    | Client ->
        (* TODO: fixme *)
        wrap rdId wrId (magic()) (magic())
(*      wrap rdId wrId 
          (StatefulLHAE.coerce rdId wrId Reader rdId sk)
          (StatefulLHAE.coerce wrId rdId Writer wrId ck) *)
    | Server ->
        (* TODO: fixme *)
        wrap rdId wrId (magic()) (magic())
(*      wrap rdId wrId
          (StatefulLHAE.coerce rdId Reader ck)
          (StatefulLHAE.coerce wrId Writer sk) *)

  
//CF We could merge the two keyGen.
let keyGenClient (rdId:id) (wrId:id) ms =   
(* ideal
    let pv = pv_of_id rdId in
    let aeAlg = rdId.aeAlg in
    let csr = rdId.csrConn in
    let ext = rdId.ext in
    Pi.assume(keyGenClient(csr,pv,aeAlg,ext));
    match read csr !kdlog with
    | Init ->
        // the server commits only on fresh SRs
        // hence we will never have matches_id(csr)
        Pi.assume(Mismatch(rdId));
        deriveKeys rdId wrId ms Client
    | Committed(pv',aeAlg',ext') when (pv=pv' && aeAlg=aeAlg' && ext=ext' && safeKDF(rdId)) -> 
        // we idealize the key derivation;
        // from this point AuthId and SafeId are fixed.
        let (myRead,peerWrite) = StatefulLHAE.GEN rdId in
        let (peerRead,myWrite) = StatefulLHAE.GEN wrId in
        let peer = wrap wrId rdId peerRead peerWrite in
        let state = wrap2 wrId rdId peer csr in
        (kdlog := update csr state !kdlog;
        (myRead,myWrite))
    | Committed(pv',aeAlg',ext') ->
        // we logically deduce not Auth for both indexes 
        deriveKeys rdId wrId ms Client
    | Derived(_,_,_) ->
        FStar.Error.unexpected "Excluded by usage restriction (affinity)"
*)
    deriveKeys rdId wrId ms Client

let keyGenServer (rdId:id) (wrId:id) ms =
(* ideal
    let csr = rdId.csrConn in
    match read csr !kdlog with  
    | Init -> 
        FStar.Error.unexpected "Excluded by usage restriction (affinity)"
    | Committed(pv',aeAlg',ext') -> 
        // when SafeKDF, the client keyGens only on fresh Ids,
        // hence we will never have AuthId(rdId) for this csr.
        //CF tricky case; revisit at some point.
        (Pi.assume(Mismatch(rdId));
        deriveKeys rdId wrId ms Server)
    | Derived(wrId',rdId',derived) when safeKDF(rdId)  ->
        // by typing the commitment, we know that rdId has matching csr pv aeAlg 
        if rdId = wrId'
        //CF was, to be discussed: 
        //CF if rdId.msId   = wrId'.msId &&  rdId.kdfAlg = wrId'.kdfAlg 
        //MK this looks so simple it may be just right! Maybe too good to be true?             
        then  
            derived // we benefit from the client's idealization
        else
            // we generate our own ideal keys; they will lead to a verifyData mismatch
            let (myRead,peerWrite) = StatefulLHAE.GEN rdId in
            let (peerRead,myWrite) = StatefulLHAE.GEN wrId in
            (myRead,myWrite)
    | Derived(wrId',rdId',derived)  ->
        // we logically deduce not Auth for both indexes
        deriveKeys rdId wrId ms Server
*)
    deriveKeys rdId wrId ms Server


(* VerifyData *) 

// Before TLS 1.3, the payload of finished messages is a MAC keyed
// with the master secret, thereby requiring a joint security assumption.
// 
// In TLS 1.3, the payload of finished messages is a MAC keyed with
// its own derived key, so we can use a plain-vanilla, single-shot
// INT-CMA assumption (and code similar to MAC.fst, except for the
// baroque selection of the MAC algorithm in TLSPRF).

type text = bytes // the hashed digest, aka data below
type tag = bytes  // the verifyData payload

(* ideal

type eventVD = MakeVerifyData of msId * Role * text * tag

type entry = msId * Role * text * tag
let log : ref<list<entry>> = ref []

let rec mem (i:msId) (r:Role) (t:text) (es:list<entry>) = 
  match es with
  | [] -> false 
  | (i',role,text,_)::es when (i=i' && r=role && text=t) -> true
  | (i',role,text,_)::es -> mem i r t es

let rec assoc (r:Role) (vd:tag) (es:list<entry>) =
  match es with
  | [] -> None
  | (i',role,text,tag)::es when (r=role && vd=tag) -> Some(i',text)
  | (i',role,text,_)::es -> assoc r vd es
*)

private let verifyData si ms role data = 
  TLSPRF.verifyData (vdAlg si) ms.bytes role data

let makeVerifyData si (ms:masterSecret) role data =
  let tag = verifyData si ms role data in
(* ideal
  //MK rename predicate and function
  //if safeVD si then
  let i = mk_msid si in
  let msdataoption = assoc role tag !log in
  let msdata = (i,data) in
  if msdataoption<>None && msdataoption<>Some(msdata) then
    failwith "collision"
  else
    Pi.assume(MakeVerifyData(i, role, data, tag));
    log := (i,role,data,tag)::!log;
*)
    tag

let checkVerifyData si ms role data (tag:bytes) =
  admit()
  (*
  let (computed:bytes) = verifyData si ms role data in
  equalBytes tag computed
  //#begin-ideal2
  #if ideal
  // we return "false" when concrete verification
  // succeeds but shouldn't according to the log 
  && ( safeVD si  = false || mem (mk_msid si) role data !log ) //MK: rename predicate and function
  //#end-ideal2
  #endif
*)


(* We do not support SSL3's ad hod certificate verify format:

let ssl_certificate_verify (si:sessionInfo) ms (algs:sigAlg) log =
  let s = ms.bytes in
  match algs with
  | CoreCrypto.RSASIG -> TLSPRF.ssl_verifyCertificate MD5 s log @| TLSPRF.ssl_verifyCertificate SHA1 s log 
  | CoreCrypto.DSA    -> TLSPRF.ssl_verifyCertificate SHA1 s log 
  | _                 -> FStar.Error.unexpected "[ssl_certificate_verify] invoked on a wrong signature algorithm"

*)
