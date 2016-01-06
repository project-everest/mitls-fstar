(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.Alert


open Platform.Log

open MiTLS.Bytes
open MiTLS.Alert
open MiTLS.Error
open MiTLS.TLSError
open MiTLS.TLSConstants

open FlexTLS.Types
open FlexTLS.Constants
open FlexTLS.State
open FlexTLS.Record



/// <summary>
/// Receive an Alert message from the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <returns> Updated state * parsed alert description * alert bytes </returns>
let receive (st:state) : state * alertDescription * bytes =
  Log.logInfo("# ALERT : FlexTLS.Alert.receive");
  let buf = st.read.alert_buffer in
  if length buf < 2 then
    let ct,pv,len,_ = FlexTLS.Record.parseFragmentHeader st in
    match ct with
    | Alert ->
      let st,b = FlexTLS.Record.getFragmentContent (st, ct, len) in
      let buf = buf @| b in
      let st = FlexTLS.State.updateIncomingAlertBuffer st buf in
      FlexTLS.Alert.receive st
    | Handshake ->
      let st,b = FlexTLS.Record.getFragmentContent (st, ct, len) in
      let buf = buf @| b in
      let st = FlexTLS.State.updateIncomingHSBuffer st buf in
      let _,hst,payload,_ = FlexHandshake.FlexHandshake.receive st in
      failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected handshake message: %A with payload %s" hst (Bytes.hexString(payload))))

    | _ ->
      let _,b = FlexTLS.Record.getFragmentContent (st, ct, len) in
      failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected content type: %A\n Payload (%d Bytes) : %s" ct len (Bytes.hexString(b))))
  else
    let alb,rem = Bytes.split buf 2 in
    match Alert.parseAlert alb with
    | Error(ad,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
    | Correct(ad) ->
      let st = FlexTLS.State.updateIncomingAlertBuffer st rem in
      Log.logInfo(sprintf "--- Description : %A" ad);
      Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(alb)));
      (st,ad,alb)

/// <summary>
/// Forward an Alert message received from a network stream
/// </summary>
/// <param name="stin"> State of the current Handshake on the incoming side </param>
/// <param name="stout"> State of the current Handshake on the outgoing side </param>
/// <param name="?fp"> Optional fragmentation policy applied to the message </param>
/// <returns> Updated incoming state * Updated outgoing state * forwarded alert bytes </returns>
let forward (stin:state) (stout:state) (*?*)(fp:fragmentationPolicy) : state * state * bytes =
  Log.logInfo("# ALERT : FlexTLS.Alert.forward");
  // let fp = defaultArg fp FlexTLS.Constants.defaultFragmentationPolicy in
  let stin,ad,alb = FlexTLS.Alert.receive(stin) in
  let stout   = FlexTLS.Alert.send(stout,alb,fp) in
  Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(alb)));
  stin,stout,alb

/// <summary>
/// Send an Alert message to the network stream from an Alert Description
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="ad"> Alert description union type already parsed </param>
/// <param name="?fp"> Optional fragmentation policy applied to the message </param>
/// <returns> Updated state </returns>
let send (st:state) (ad:alertDescription) (*?*)(fp:fragmentationPolicy) : state =
  // let fp = defaultArg fp FlexTLS.Constants.defaultFragmentationPolicy in
  FlexTLS.Alert.send(st, alertBytes ad, fp)

/// <summary>
/// Send an Alert message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="payload"> Alert bytes </param>
/// <param name="?fp"> Optional fragmentation policy applied to the message </param>
/// <returns> Updated state </returns>
let send (st:state) (payload:bytes) (*?*)(fp:fragmentationPolicy) : state =
  Log.logInfo("# ALERT : FlexTLS.Alert.send");
  // let fp = defaultArg fp FlexTLS.Constants.defaultFragmentationPolicy in
  let buf = st.write.alert_buffer @| payload in
  let st = FlexTLS.State.updateOutgoingAlertBuffer st buf in
  let _ =
    if length payload = 2 then
      match Alert.parseAlert payload with
      | Error(ad,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
      | Correct(ad) -> Log.logInfo(sprintf "--- Description : %A" ad)
    else ()
  in
  Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(payload)));
  FlexTLS.Record.send(st,Alert,fp)
