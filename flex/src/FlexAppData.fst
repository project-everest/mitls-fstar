(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.ApplicationData


open Platform.Log
open Platform.Bytes
open Platform.Error

open MiTLS.TLSConstants

open FlexTLS.Types
open FlexTLS.Constants
open FlexTLS.Record
open FlexTLS.State



/// <summary>
/// Receive application data from network stream
/// </summary>
/// <param name="st"> State of the current connection </param>
/// <returns> Updated state * Application data bytes received </returns>

let receive (st:state) : state * bytes =
  Log.logInfo("# APPLICATION DATA : FlexAppData.receive");
  let ct,pv,len,_ = FlexRecord.parseFragmentHeader st in
  match ct with
  | Application_data ->
    FlexRecord.getFragmentContent(st,ct,len)
  | _ ->
    let _,b = FlexRecord.getFragmentContent (st, ct, len) in
    failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected content type : %A\n Payload (%d Bytes) : %s" ct len (Bytes.hexString(b))))

/// <summary>
/// Forward application data to the network stream
/// </summary>
/// <param name="stin"> State of the current connection on the incoming side </param>
/// <param name="stout"> State of the current connection on the outgoing side </param>
/// <param name="fp"> Optional fragmentation policy applied to the message </param>
/// <returns> Updated incoming state * Updated outgoing state * forwarded application data bytes </returns>
let forward (stin:state, stout:state, ?fp:fragmentationPolicy) : state * state * bytes =
  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let stin,appb = FlexAppData.receive(stin) in
  let stout = FlexAppData.send(stout,appb,fp) in
  stin,stout,appb

/// <summary>
/// Send the HTTP application data
/// </summary>
/// <param name="st"> State of the current connection </param>
/// <param name="data"> String to send as HTTP </param>
/// <returns> Updated state <returns>
let send_http(st:state, data:string) : state =
  FlexAppData.send(st, sprintf "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: %d\r\n\r\n%s" (Core.String.length data) data)

/// <summary>
/// Send an application data HTTP GET request
/// </summary>
/// <param name="st"> State of the current connection </param>
/// <returns> Updated state <returns>
let send_http_get(st:state) : state =
  FlexAppData.send_http(st,"GET /")

/// <summary>
/// Send the HTTP application data banner for FlexTLS
/// </summary>
/// <param name="st"> State of the current connection </param>
/// <returns> Updated state <returns>
let send_http_banner(st:state) : state =
  FlexAppData.send_http(st,"You just received Application data from FlexTLS!\r\n")

/// <summary>
/// Send application data as an encoded string to network stream
/// </summary>
/// <param name="st"> State of the current connection </param>
/// <param name="data"> Application data as encoded string </param>
/// <param name="fp"> Optional fragmentation policy applied to the message </param>
/// <returns> Updated state </returns>
let send(st:state, data:string, ?encoding:System.Text.Encoding, ?fp:fragmentationPolicy) : state =
  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let encoding = defaultArg encoding System.Text.Encoding.ASCII in
  let payload = abytes(encoding.GetBytes(data)) in
  FlexAppData.send(st,payload,fp)

/// <summary>
/// Send application data as raw bytes to network stream
/// </summary>
/// <param name="st"> State of the current connection </param>
/// <param name="data"> Application data as raw bytes </param>
/// <param name="fp"> Optional fragmentation policy applied to the message </param>
/// <returns> Updated state </returns>
let send(st:state, data:bytes, ?fp:fragmentationPolicy) : state =
  Log.logInfo("# APPLICATION DATA : FlexAppData.send");
  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let buf = st.write.appdata_buffer @| data in
  let st = FlexState.updateOutgoingAppDataBuffer st buf in
  FlexRecord.send(st,Application_data,fp)
