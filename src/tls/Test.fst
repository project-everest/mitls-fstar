module Test

open Platform.Bytes

open TLSConstants
open TLSInfo
open Range
open DataStream
open TLS

let fragment_1 i (b:bytes { length b <= max_TLSPlaintext_fragment_length }) : fragment i (point (length b)) = 
  let rg : frange i = point(length b) in 
  appFragment i rg b 

// move to Bytes
let sub (buffer:bytes) (first:nat) (len:nat { first + len <= length buffer }) = 
  let before, now = split buffer first in 
  let now, after = split buffer len in 
  now 

val write_all': c:Connection.connection -> i:id -> buffer:bytes -> sent:nat {sent <= length buffer} -> St ioresult_w 
let rec write_all' c i buffer sent =  
  if sent = length buffer then Written 
  else 
  let size = min (length buffer - sent) max_TLSPlaintext_fragment_length in
  let payload = sub buffer sent size in
  let rg : frange i = point(length payload) in
  let f : fragment i rg = fragment_1 i payload in
  match assume false; write c f with
  | Written -> write_all' c i buffer (sent+size)
  | r       -> r 

let write_all c i b = write_all' c i b 0

let client (here:Connection.c_rgn) tcp config_1 (request:bytes) =
  let c = connect here tcp config_1 in
  // nothing sent yet, except possibly for TCP
  // we write in cleartext until we have the 0RTT index.
  match read c noId with
  //    ClientHello
  //      + KeyShare             -------->
  //                                                  ServerHello
  //                                                   + KeyShare
  //                                         {EncryptedExtensions}
  //                                         {CertificateRequest*}
  //                                        {ServerConfiguration*}
  //                                                {Certificate*}
  //                                          {CertificateVerify*}
  //                             <--------              {Finished}
  //   {Certificate*}
  //   {CertificateVerify*}
  //   {Finished}                -------->
  | Complete ->
  let i = currentId c Writer in
  let f0 = fragment_1 i request  in 
  match write c f0 with 
  //   [Request]                 -------->
  | Written ->
  match read c i with 
  //                             <--------      [Application Data]
  | Read (Data g0) -> 
  let _ = writeCloseNotify c in
  //   [CloseNotify]             -------->
  match read c i with 
  //                             <--------           [CloseNotify] 
  | Read Close -> appBytes g0 
  // At this point, if authId i, I know that 
  // (1) my peer's writer view is exactly ( Data g0 ; Close ), 
  // (2) my peer's reader view is exactly ( Data f0 ; Close ).

  // it seems convenient to have complete return i.
  // the client need not be aware of the handshake epoch.
  // should connect read to completion?

  // we have exactly the same code for 1.2 and 1.3 1RTT 
  // (even with falseStart)

let server (here:Connection.c_rgn) tcp config_1 (respond: (bytes -> bytes)) =
  let c = accept here tcp config_1 in
  match read c noId with
  | Complete i ->
  let i = currentId c Reader in 
  match read c i with 
  | Read (Data f0) -> 
  let response = fragment_1 i (respond (appBytes f0)) in
  match write c response with
  | Written  -> 
  match read c i with 
  | Read Close -> ()
  // At this point, if authId i, I know that 
  // (1) my peer's writer view is exactly ( Data f0 ; Close )
  // but not what my peer has read, unless the app semantics says so.


(* Notes towards a second example: RPC *)

let N = 100000

type request = rbytes (0,N)

