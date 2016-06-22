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

val validLog: list hs_msg -> Tot bool
let validLog hsl = 
    match hsl with
    | [] -> true
    | [ClientHello ch] -> true
    | (ClientHello ch) :: (ServerHello sh) :: rest -> true
    | _ -> false

val getLogVersion: hsl:list hs_msg{validLog hsl} -> Tot (option protocolVersion)
let getLogVersion hsl =
    match hsl with
    | (ClientHello ch) :: (ServerHello sh) :: rest -> Some sh.sh_protocol_version
    | _ -> None

type log =
  | LOG: #region:rid -> 
         logref:rref region (pv:option protocolVersion & hsl:list hs_msg & b:bytes
                             {validLog hsl /\ getLogVersion hsl = pv /\ handshakeMessagesBytes pv hsl = b}) -> log 

val create: #reg:rid -> ST log
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let create #reg = 
    let hsl: list hs_msg = [] in
    let r = ralloc reg (|None,hsl,empty_bytes|) in
    LOG #reg r 

val append_log: l:log -> hm:hs_msg -> ST bytes
    (requires (fun h ->
	       let (|pv,hsl,lb|) = sel h l.logref in
	       validLog (List.Tot.append hsl [hm])))
    (ensures (fun h1 b h2 -> True))
let append_log (LOG #reg lref) hm = 
    let (|pv,hsl,lb|) = !lref in 
    let hsl' = FStar.List.Tot.append hsl [hm] in
    let pv = getLogVersion hsl' in
    let mb = handshakeMessageBytes pv hm in
    let lb' = lb @| mb in
    lref := (|pv,hsl',lb'|);
    mb

let op_At_At l h = append_log l h

val getMessages: log -> ST (list hs_msg)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let getMessages (LOG #reg lref) = 
    let (|pv,hsl,lb|) = !lref in hsl

val getBytes: log -> ST bytes 
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let getBytes (LOG #reg lref) = 
    let (|pv,hsl,lb|) = !lref in lb


val getHash: log -> ST bytes 
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let getHash (LOG #reg lref) = 
    let (|pv,hsl,lb|) = !lref in 
    CoreCrypto.hash CoreCrypto.SHA256 lb

assume val checkLogSessionHash:    list hs_msg -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
assume val checkLogClientFinished: list hs_msg -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
assume val checkLogServerFinished: list hs_msg -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
    
