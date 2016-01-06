(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.Message.ServerHelloDone


open Platform.Log
open Platform.Bytes
open Platform.Error

open MiTLS.HandshakeMessages

open FlexTLS.Types
open FlexTLS.Constants
open FlexTLS.Handshake



/// <summary>
/// Receive a ServerHelloDone message from the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <returns> Updated state * FServerHelloDone message record </returns>
let receive (st:state) : state * FServerHelloDone =
  Log.logInfo("# SERVER HELLO DONE : FlexServerHelloDone.receive");
  let st,hstype,payload,to_log = FlexHandshake.receive(st) in
  match hstype with
  | HT_server_hello_done  ->
    if length payload <> 0 then
      failwith (perror __SOURCE_FILE__ __LINE__ "payload has not length zero")
    else
      let fshd: FServerHelloDone = {payload = to_log} in
      Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(payload)));
      st,fshd
  | _ -> failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected handshake type: %A" hstype))

/// <summary>
/// Prepare ServerHelloDone message bytes that will not be sent to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <returns> FServerHelloDone message bytes * Updated state * FServerHelloDone message record </returns>
let prepare () : FServerHelloDone =
  let payload = HandshakeMessages.serverHelloDoneBytes in
  let fshd: FServerHelloDone = { payload = payload } in
  fshd

/// <summary>
/// Send a ServerHelloDone message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * FServerHelloDone message record </returns>
let send (st:state, (*?*)fp:fragmentationPolicy) : state * FServerHelloDone =
  Log.logInfo("# SERVER HELLO DONE : FlexServerHelloDone.send");
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let fshd = FlexServerHelloDone.prepare() in
  let st = FlexHandshake.send(st,fshd.payload,fp) in
  st,fshd
