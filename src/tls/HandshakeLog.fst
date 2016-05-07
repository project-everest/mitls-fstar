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

type log =
     | LOG: pv: protocolVersion -> #region:rid -> rref region (hsl:list hs_msg & b:bytes{b = handshakeMessagesBytes pv hsl}) -> log 

val init: pv:protocolVersion -> reg:rid -> log 
let init pv reg = 
    let hsl: list hs_msg = [] in
    let r = ralloc reg (|hsl,empty_bytes|) in
    LOG pv #reg r 

val append_log: log -> hs_msg -> bytes
let append_log (LOG pv #reg lref) hm = 
    let mb = handshakeMessageBytes pv hm in
    let (|hsl,lb|) = !lref in 
    let hsl' = FStar.List.Tot.append hsl [hm] in
    let lb' = lb @| mb in
    lref := (|hsl',lb'|);
    mb

let op_At_At l h = append_log l h

val getMessages: log -> ST (list hs_msg)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let getMessages (LOG pv #reg lref) = 
    let (|hsl,lb|) = !lref in hsl

val getBytes: log -> ST bytes 
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let getBytes (LOG pv #reg lref) = 
    let (|hsl,lb|) = !lref in lb

assume val checkLogSessionHash: list hs_msg -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
assume val checkLogClientFinished: list hs_msg -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
assume val checkLogServerFinished: list hs_msg -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
    