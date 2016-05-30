module Test

open Platform.Bytes

open TLSConstants
open TLSInfo
open Range
open DataStream
open TLS

let fragment_1 i (b:bytes) =
  assume(length b <= max_TLSPlaintext_fragment_length);
  let rg : frange i = point(length b) in 
  appFragment i rg b 

let client (here:rid) tcp config_1 (request:bytes) =
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

let server (here:rid) tcp config_1 (respond: (bytes -> bytes)) =
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
