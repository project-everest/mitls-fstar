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
     | LOG: #region:rid -> hsl:rref region (list hs_msg) -> pv:protocolVersion -> rref region bytes -> log // bytes = handshakeMessagesBytes pv hsl

val init: reg:rid -> pv:protocolVersion -> log
let init reg pv = 
    let r = ralloc reg empty_bytes in
    let l: list hs_msg = [] in
    let lr = ralloc reg l in
    LOG #reg lr pv r

val append_log: log -> (hs_msg * bytes) -> unit
let append_log (LOG #reg hsl pv lref) (hm,b) = 
    lref := !lref @| b;
    hsl := FStar.List.Tot.append !hsl [hm]

let op_At_At l h = append_log l h

val getMessages: log -> ST (list hs_msg)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

let getMessages (LOG #reg hsl pv lref) = !hsl

val getBytes: log -> ST bytes 
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let getBytes (LOG #reg #hsl pv lref) = !lref

assume val checkLogSessionHash: list hs_msg -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
assume val checkLogClientFinished: list hs_msg -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
assume val checkLogServerFinished: list hs_msg -> csr:csRands -> pv:protocolVersion -> cs:cipherSuite -> negotiatedExtensions -> bool
    