(* Copyright (C) 2012--2016 Microsoft Research and INRIA *)

module MiTLS.FlexTLS.Message.Finished
open MiTLS


open MiTLS.Log
open MiTLS.Platform.Bytes
open MiTLS.Platform.Error

open MiTLS.TLSInfo
open MiTLS.TLSConstants
open MiTLS.HandshakeMessages

open MiTLS.FlexTLS.Types
open MiTLS.FlexTLS.Constants
open MiTLS.FlexTLS.State
open MiTLS.FlexTLS.Handshake
open MiTLS.FlexTLS.Secrets



/// Access the log
let log = Log.retrieve "FlexTLS.Log.General"

/// <summary>
/// Receive a Finished message from the network stream and check the verify_data on demand
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="nsc"> NextSecurityContext embedding required parameters </param>
/// <param name="role"> Optional role used to compute an eventual verify data </param>
/// <returns> Updated state * FFinished message record </returns>
let receive (st:state) (nsc:nextSecurityContext) (*?*)(role:Role) : state * FFinished =
  match role with
  | Some(role) ->
    FlexFinished.receive st nsc.si.protocol_version nsc.si.cipher_suite (*verify_data=*)(FlexSecrets.makeVerifyData nsc.si nsc.secrets.ms role st.hs_log))
  | None ->
    FlexFinished.receive st nsc.si.protocol_version nsc.si.cipher_suite

/// <summary>
/// Receive a Finished message from the network stream and check the verify_data on demand
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="pv"> Protocol Version </param>
/// <param name="cs"> Ciphersuite </param>
/// <param name="verify_data"> Optional verify_data to compare to received payload </param>
/// <returns> Updated state * FFinished message record </returns>
let receive (st:state) (pv:ProtocolVersion) (cs:cipherSuite) (*?*)(verify_data:bytes) : state * FFinished =
  Log.write log Info "TLS Message" "# FINISHED : FlexFinished.receive";
  let st,hstype,payload,to_log = FlexHandshake.receive st in
  match hstype with
  | HT_finished  ->
    // check that the received payload has a correct length
    let expected_vd_length =
      match pv with
      | TLS_1p2   -> (TLSConstants.verifyDataLen_of_ciphersuite cs) = (Bytes.length payload)
      | _         -> 12 = (Bytes.length payload)
    in
    if not expected_vd_length then 
      failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "unexpected payload length %d" (Bytes.length payload)))
    else
      // check the verify_data if the user provided one
      (match verify_data with
      | None ->
        Log.write log Debug "Warning" (sprintf "--- Verify data not checked")
      | Some(verify_data) ->
        Log.write log Debug "Field" (sprintf "--- Expected data : %A" (Bytes.hexString verify_data));
        Log.write log Debug "Field" (sprintf "--- Verify data: %A" (Bytes.hexString payload));
        if not (verify_data = payload) then failwith "Verify data do not match"
      );
      // no verify_data provided OR expected verify_data matches payload
      let st = FlexState.updateIncomingVerifyData st payload in
      let ff = { verify_data = payload;
                 payload = to_log;
               } in
      Log.write log Debug "Payload" (sprintf "%A" (Bytes.hexString ff.payload));
      st,ff
  | _ -> failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected handshake type: %A" hstype))

/// <summary>
/// Prepare a Finished message from the verify_data that will not be sent to the network
/// </summary>
/// <param name="verify_data"> Verify_data that will be used to generate the finished message </param>
/// <returns> Finished message bytes *  FFinished message record </returns>
let prepare (verify_data:bytes) : bytes * FFinished =
  let payload = HandshakeMessages.messageBytes HT_finished verify_data in
  let ff = { verify_data = verify_data;
             payload = payload;
           }
  in
  payload,ff

/// <summary>
/// Overload : Send a Finished message from the network stream and check the verify_data on demand
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="ff"> Optional finished message record including the payload to be used </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * FFinished message record </returns>
let send (st:state) (ff:FFinished) (*?*)(fp:fragmentationPolicy) : state * FFinished =
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  FlexFinished.send st ff.verify_data fp

/// <summary>
/// Send a Finished message from the verify_data and send it to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="role"> Role necessary to compute the verify data </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * FFinished message record </returns>
let send (st:state) (nsc:nextSecurityContext) (role:Role) (*?*)(fp:fragmentationPolicy) : state * FFinished =
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let verify_data = FlexSecrets.makeVerifyData nsc.si nsc.secrets.ms role st.hs_log in
  FlexFinished.send st verify_data fp

/// <summary>
/// Send a Finished message from the network stream and check the verify_data on demand
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="verify_data"> Verify_data that will be used </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * FFinished message record </returns>
let send (st:state) (verify_data:bytes) (*?*)(fp:fragmentationPolicy) : state * FFinished =
  Log.write log Info "TLS Message" "# FINISHED : FlexFinished.send";
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let payload,ff = FlexFinished.prepare verify_data in
  Log.write log Debug "" (sprintf "--- Verify data : %A" (Bytes.hexString ff.verify_data));
  let st = FlexState.updateOutgoingVerifyData st verify_data in
  let st = FlexHandshake.send st payload fp in
  st,ff
