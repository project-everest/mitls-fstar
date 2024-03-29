(* Copyright (C) 2012--2016 Microsoft Research and INRIA *)

module MiTLS.FlexTLS.Message.ClientHello
open MiTLS


open MiTLS.Log
open MiTLS.Platform.Bytes
open MiTLS.Platform.Error

open MiTLS.TLSInfo
open MiTLS.TLSConstants
open MiTLS.TLSExtensions
open MiTLS.HandshakeMessages

open MiTLS.FlexTLS.Types
open MiTLS.FlexTLS.Constants
open MiTLS.FlexTLS.State
open MiTLS.FlexTLS.Handshake


/// Access the log
let log = Log.retrieve "FlexTLS.Log.General"

/// <summary>
/// Extract the ciphersuites from a FClientHello message record
/// </summary>
/// <param name="ch"> FClientHello message record </param>
/// <returns> Ciphersuites </returns>
let getCiphersuites (ch:FClientHello) =
  match ch.ciphersuites with
  | None ->
    (match FlexConstants.names_of_cipherSuites TLSInfo.defaultConfig.ciphersuites with
      | Error(x,y) -> failwith "Cannot extract ciphersuites from the default config"
      | Correct(css) -> css)
  | Some(ciphersuites) -> ciphersuites

/// <summary>
/// Extract the protocol version from a FClientHello message record
/// </summary>
/// <param name="ch"> FClientHello message record </param>
/// <returns> Protocol version </returns>
let getPV (ch:FClientHello) =
  match ch.pv with
  | None -> TLSInfo.defaultConfig.maxVer
  | Some(pv) -> pv

/// <summary>
/// Extract the compression list from a FClientHello message record
/// </summary>
/// <param name="ch"> FClientHello message record </param>
/// <returns> List of client supported compressions </returns>
let getCompressions (ch:FClientHello) =
  match ch.comps with
  | None -> TLSInfo.defaultConfig.compressions
  | Some(l) -> l

/// <summary>
/// Extract the extension list from a FClientHello message record
/// </summary>
/// <param name="ch"> FClientHello message record </param>
/// <returns> List of client extensions </returns>
let getExt (ch:FClientHello) =
  match ch.ext with
  | None -> []
  | Some(l) -> l

/// <summary>
/// Extract the session id from a FClientHello message record
/// </summary>
/// <param name="ch"> FClientHello message record </param>
/// <returns> Session ID, or an empty byte array if None</returns>
let getSID (ch:FClientHello) =
  match ch.sid with
  | None -> empty_bytes
  | Some(sid) -> sid

/// <summary>
/// Update channel's Epoch Init Protocol version to the one chosen by the user if we are in an InitEpoch, else do nothing
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="fch"> Client hello message containing the desired protocol version </param>
/// <returns> Updated state of the handshake </returns>
let fillStateEpochInitPvIFIsEpochInit (st:state) (fch:FClientHello) : state =
  if TLSInfo.isInitEpoch st.read.epoch then
    let st = FlexState.updateIncomingRecordEpochInitPV st (getPV fch) in
    let st = FlexState.updateOutgoingRecordEpochInitPV st (getPV fch) in
    st
  else
    st


/// <summary>
/// Receive a ClientHello message from the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="checkVD"> Flag to enable or ignore the check on the verify data if the renegotiation indication is in the client extension list </param>
/// <returns> Updated state * Next security context in negotiation * FClientHello message record </returns>
let receive (st:state) (*?*)(checkVD:bool) : state * nextSecurityContext * FClientHello =
  Log.write log Info "" "# CLIENT HELLO : FlexClientHello.receive";
  //  let checkVD = defaultArg checkVD true in
  let st = FlexState.resetHandshakeLog st in
  let st,hstype,payload,to_log = FlexHandshake.receive st in
  match hstype with
  | HT_client_hello  -> (
    match parseClientHello payload with
    | Error (ad,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
    | Correct (pv,cr,sid,clientCipherSuites,cm,cextL) ->
      let csnames = 
        match FlexConstants.names_of_cipherSuites clientCipherSuites with
        | Error(_,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
        | Correct(ciphersuites) -> ciphersuites
      in
      let cextL =
        match parseClientExtensions cextL clientCipherSuites with
        | Error(ad,x) -> []
        | Correct(extL)->
        if checkVD then
          if TLSExtensions.checkClientRenegotiationInfoExtension ({TLSInfo.defaultConfig with safe_renegotiation = true}) extL st.read.verify_data then
            extL
          else
            failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Check for renegotiation verify data failed" ))
        else extL
      in
      let fch = { FlexConstants.nullFClientHello with
                  pv = Some(pv);
                  rand = cr;
                  sid = Some(sid);
                  ciphersuites = Some(csnames);
                  comps = Some(cm);
                  ext = Some(cextL);
                  payload = to_log; 
                }
      in
      let si  = { FlexConstants.nullSessionInfo with
                  init_crand = cr; 
                }
      in
      let nsc = { FlexConstants.nullNextSecurityContext with
                  si = si;
                  crand = cr;
                }
      in
      let st = fillStateEpochInitPvIFIsEpochInit st fch in
      Log.write log Debug "Field" (sprintf "--- Protocol Version : %A" (getPV fch));
      Log.write log Debug "Field" (sprintf "--- Sid : %s" (Bytes.hexString(getSID fch)));
      Log.write log Debug "Field" (sprintf "--- Client Random : %s" (Bytes.hexString(fch.rand)));
      Log.write log Debug "Field" (sprintf "--- Ciphersuites : %A" (getCiphersuites fch));
      Log.write log Debug "Field" (sprintf "--- Compressions : %A" (getCompressions fch));
      Log.write log Debug "Field" (sprintf "--- Extensions : %A" (getExt fch));
      Log.write log Debug "Payload" (sprintf "%s" (Bytes.hexString payload));
      (st,nsc,fch))
    | _ -> failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected handshake type: %A" hstype))

/// <summary>
/// Prepare ClientHello message bytes that will not be sent to the network stream
/// </summary>
/// <param name="cfg"> Desired config </param>
/// <param name="crand"> Client random value </param>
/// <param name="csid"> Client desired sid </param>
/// <param name="cExtL"> Client list of extension </param>
/// <returns> FClientHello message record </returns>
let prepare (pv:ProtocolVersion) (csnames:list<cipherSuiteName>) (comps:list<Compression>) (crand:bytes) (csid:bytes) (cExtL:list<clientExtension>) : FClientHello =
  let exts = clientExtensionsBytes cExtL in
  let css = TLSConstants.cipherSuites_of_nameList csnames in
  let payload = HandshakeMessages.clientHelloBytes2 pv css comps crand csid exts in
  { pv = Some(pv); ciphersuites = Some(csnames); comps = Some(comps); rand = crand; sid = Some(csid); ext = Some(cExtL); payload = payload }

/// <summary>
/// Send ClientHello message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="fch"> Desired client hello </param>
/// <param name="cfg"> Desired config </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * Next security context in negotiation * FClientHello message record </returns>
let send (st:state) (*?*)(fch:FClientHello) (*?*)(cfg:config) (*?*)(fp:fragmentationPolicy) : state * nextSecurityContext * FClientHello =
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  //  let fch = defaultArg fch FlexConstants.nullFClientHello in
  //  let cfg = defaultArg cfg defaultConfig in
  let crand =
    if fch.rand = empty_bytes then (Nonce.mkHelloRandom (getPV fch)) else fch.rand
  in
  let st = fillStateEpochInitPvIFIsEpochInit st fch in
  let extl =
    match fch.ext with
    | Some(extl) -> extl
    | None ->
      let shadow_ci = { role = Client;
                        id_rand = fch.rand;
                        id_in =  st.read.epoch;
                        id_out = st.write.epoch}
      in
      TLSExtensions.prepareClientExtensions cfg shadow_ci st.write.verify_data
  in
  let st,fch = FlexClientHello.send st (getPV fch) (getCiphersuites fch) (getCompressions fch) crand (getSID fch) extl fp in
  let ext_offers =
    match TLSExtensions.getOfferedDHGroups (getExt fch) with
    | None -> []
    | Some(gl) ->
    let ffdh g = FFDH({group = g; x = empty_bytes; gx = empty_bytes; gy = empty_bytes}) in
    List.map dh13 gl
  in
  let si  = { FlexConstants.nullSessionInfo with init_crand = crand } in
  let nsc = { FlexConstants.nullNextSecurityContext with
              si = si;
              crand = fch.rand;
              offers = ext_offers;
            }
  in
  st,nsc,fch

/// <summary>
/// Send ClientHello message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="fch"> Desired client hello </param>
/// <param name="cfg"> Desired config </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * Next security context in negotiation * FClientHello message record </returns>
let send (st:state) (pv:ProtocolVersion) (css:list<cipherSuiteName>) (comps:list<Compression>) (crand:bytes) (csid:bytes) (cExtL:list<clientExtension>) (*?*)(fp:fragmentationPolicy) : state * FClientHello =
  Log.write log Info "TLS Message" "# CLIENT HELLO : FlexClientHello.send";
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let st = FlexState.resetHandshakeLog st in
  let fch = FlexClientHello.prepare pv css comps crand csid cExtL in
  let st = FlexHandshake.send st fch.payload fp in
  Log.write log Debug "Field" (sprintf "--- Protocol Version : %A" (getPV fch));
  Log.write log Debug "Field" (sprintf "--- Sid : %s" (Bytes.hexString (getSID fch)));
  Log.write log Debug "Field" (sprintf "--- Client Random : %s" (Bytes.hexString fch.rand));
  Log.write log Debug "Field" (sprintf "--- Ciphersuites : %A" (getCiphersuites fch));
  Log.write log Debug "Field" (sprintf "--- Compressions : %A" (getCompressions fch));
  Log.write log Debug "Field" (sprintf "--- Extensions : %A" (getExt fch));
  st,fch
