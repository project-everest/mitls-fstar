module HandshakeLog
open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open FStar.Set  
open Platform.Error
open Platform.Bytes

open TLSConstants
open TLSInfo
open HandshakeMessages

abstract type hs_log = list hs_msg

val validLog: hs_log -> Tot bool
let validLog hsl = 
    match hsl with
    | [] -> true
    | [ClientHello ch] -> true
    | (ClientHello ch) :: (ServerHello sh) :: rest -> true
    | _ -> false

val getLogVersion: hsl:hs_log{validLog hsl} -> Tot (option protocolVersion)
let getLogVersion hsl =
    match hsl with
    | (ClientHello ch) :: (ServerHello sh) :: rest -> Some sh.sh_protocol_version
    | _ -> None

type log =
  | LOG: #region:rid -> 
         logref:rref region (|
              pv: option protocolVersion
            & (hsl:hs_log{validLog hsl})
            &   b: bytes {getLogVersion hsl = pv /\ handshakeMessagesBytes pv hsl = b}
         |) -> log 

val create: #reg:rid -> ST log
  (requires (fun h -> True))
  (ensures (fun h0 out h1 ->
    let LOG #r lr = out in
    fresh_region r h0 h1 /\
    extends r reg /\
    modifies (Set.singleton r) h0 h1 /\
    modifies_rref r !{as_ref lr} h0 h1))
let create #reg = 
    let hsl: hs_log = [] in
    let r = new_region reg in
    let lr = ralloc r (| None, hsl, empty_bytes|) in
    LOG #r lr

val append_log: l:log -> hm:hs_msg -> ST bytes
    (requires (fun h ->
	       let (|pv,hsl,lb|) = sel h l.logref in
	       validLog (List.Tot.append hsl [hm])))
    (ensures (fun h0 _ h1 ->
      let LOG #r lr = l in
      modifies (Set.singleton r) h0 h1
      /\ modifies_rref r !{as_ref lr} h0 h1))
let append_log (LOG #reg lref) hm = 
    let (| pv, hsl, lb |) = !lref in 
    let hsl' = FStar.List.Tot.append hsl [hm] in
    let pv = getLogVersion hsl' in
    let mb = handshakeMessageBytes pv hm in
    let lb' = lb @| mb in
    lref := (| pv, hsl', lb' |);
    mb

let op_At_At l h = append_log l h

val getMessages: log -> St hs_log
let getMessages (LOG #reg lref) = 
    let (| pv, hsl, lb |) = !lref in hsl

val getBytes: log -> St bytes 
let getBytes (LOG #reg lref) = 
    let (| pv, hsl, lb |) = !lref in lb

val getHash: log -> h:CoreCrypto.hash_alg -> St (b:bytes{length b = CoreCrypto.hashSize h})
let getHash (LOG #reg lref) h = 
    let (| pv, hsl, lb|) = !lref in 
    CoreCrypto.hash h lb

assume val checkLogSessionHash: hs_log -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
assume val checkLogClientFinished: hs_log -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
assume val checkLogServerFinished: hs_log -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
    
