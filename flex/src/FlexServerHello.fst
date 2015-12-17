(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.Message.ServerHello


open Platform.Log
open Platform.Bytes
open Platform.Error

open MiTLS.TLSInfo
open MiTLS.TLSConstants
open MiTLS.TLSExtensions
open MiTLS.HandshakeMessages

open FlexTypes
open FlexConstants
open FlexState
open FlexHandshake



/// <summary>
/// Extract the ciphersuite from a FServerHello message record
/// </summary>
/// <param name="fsh"> FServerHello message record </param>
/// <returns> Ciphersuite </returns>
let getCiphersuite (fsh:FServerHello) =
    match fsh.ciphersuite with
    | None ->
        (match FlexConstants.names_of_cipherSuites TLSInfo.defaultConfig.ciphersuites with
        | Error(x,y) -> failwith "Cannot extract ciphersuites from the default config"
        | Correct(css) -> css.Head)
    | Some(ciphersuite) -> ciphersuite

/// <summary>
/// Extract the protocol version from a FServerHello message record
/// </summary>
/// <param name="fsh"> FServerHello message record </param>
/// <returns> Protocol version </returns>
let getPV (fsh:FServerHello) =
    match fsh.pv with
    | None -> TLSInfo.defaultConfig.maxVer
    | Some(pv) -> pv

/// <summary>
/// Extract the extension list from a FServerHello message record
/// </summary>
/// <param name="fsh"> FServerHello message record </param>
/// <returns> List of server extensions </returns>
let getExt (fsh:FServerHello) =
    match fsh.ext with
    | None -> []
    | Some(l) -> l

/// <summary>
/// Extract the session id from a FServerHello message record
/// </summary>
/// <param name="fsh"> FServerHello message record </param>
/// <returns> Session ID, or an empty byte array if None</returns>
let getSID (fsh:FServerHello) =
    match fsh.sid with
    | None -> empty_bytes
    | Some(sid) -> sid

/// <summary>
/// Update channel's Epoch Init Protocol version to the one chosen by the user if we are in an InitEpoch, else do nothing
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="fsh"> FServerHello message record </param>
/// <returns> Updated state </returns>
let fillStateEpochInitPvIFIsEpochInit (st:state) (fsh:FServerHello) : state =
    if TLSInfo.isInitEpoch st.read.epoch then
        let st = FlexState.updateIncomingRecordEpochInitPV st (getPV fsh) in
        let st = FlexState.updateOutgoingRecordEpochInitPV st (getPV fsh) in
        st
    else
        st

/// <summary>
/// Module receiving, sending and forwarding TLS Server Hello messages.
/// </summary>
type FlexServerHello =
    class

    /// <summary>
    /// Receive a ServerHello message from the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <param name="fch"> FClientHello containing the client extensions </param>
    /// <param name="nsc"> Optional Next security context being negotiated </param>
    /// <returns> Updated state * Updated next security context * FServerHello message record </returns>
    static member receive (st:state, fch:FClientHello, ?nsc:nextSecurityContext, ?checkVD:bool, ?isResuming:bool) : state * nextSecurityContext * FServerHello =
        let nsc = defaultArg nsc FlexConstants.nullNextSecurityContext in
        let checkVD = defaultArg checkVD true in
        let isResuming = defaultArg isResuming false in
        let st,fsh,negExts = FlexServerHello.receive(st,(FlexClientHello.getExt fch), checkVD = checkVD, isResuming = isResuming) in
        let si  = { nsc.si with
                    init_srand = fsh.rand;
                    protocol_version = getPV fsh;
                    sessionID = getSID fsh;
                    cipher_suite = cipherSuite_of_name (getCiphersuite fsh);
                    compression = fsh.comp;
                    extensions = negExts;
                  }
        in
        let secrets =
            match getNegotiatedDHGroup negExts with
            | None -> nsc.secrets
            | Some(group) ->
                let kex =
                    match List.tryFind
                        (fun x -> match x with
                        | DH13(off) -> off.group = group
                        | _ -> false) nsc.offers with
                    | None -> DH13 ({group = group; x = empty_bytes; gx = empty_bytes; gy = empty_bytes})
                    | Some(kex) -> kex
                in
                {nsc.secrets with kex = kex}
        in
        let nsc = { nsc with
                    si = si;
                    srand = fsh.rand;
                    secrets = secrets;
                  }
        in
        st,nsc,fsh

    /// <summary>
    /// Receive a ServerHello message from the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <returns> Updated state * Updated next security context * FServerHello message record * Negotiated extensions </returns>
    static member receive (st:state, cextL:list<clientExtension>, ?checkVD:bool, ?isResuming:bool) : state * FServerHello * negotiatedExtensions =
        LogManager.GetLogger("file").Info("# SERVER HELLO : FlexServerHello.receive");
        let checkVD = defaultArg checkVD true in
        let isResuming = defaultArg isResuming false in
        let st,hstype,payload,to_log = FlexHandshake.receive(st) in
        match hstype with
        | HT_server_hello  ->
            (match parseServerHello payload with
            | Error (ad,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
            | Correct (pv,sr,sid,cs,cm,sexts) ->
                let csname = match TLSConstants.name_of_cipherSuite cs with
                    | Error(_,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
                    | Correct(cs) -> cs
                in
                let sextL =
                    match parseServerExtensions sexts with
                    | Error(ad,x) -> []
                    | Correct(sextL)->
                        if (not checkVD) || TLSExtensions.checkServerRenegotiationInfoExtension ({TLSInfo.defaultConfig with safe_renegotiation = true}) sextL st.write.verify_data st.read.verify_data then
                            sextL
                        else
                            failwith (perror __SOURCE_FILE__ __LINE__ "Check for renegotiation verify data failed")
                in
                let negExts =
                    match negotiateClientExtensions cextL sextL isResuming cs with
                    | Error(ad,x) -> failwith x
                    | Correct(exts) -> exts
                in
                let fsh = { pv = Some(pv);
                            rand = sr;
                            sid = Some(sid);
                            ciphersuite = Some(csname);
                            comp = cm;
                            ext = Some(sextL);
                            payload = to_log;
                          }
                in
                let st = fillStateEpochInitPvIFIsEpochInit st fsh in
                LogManager.GetLogger("file").Debug(sprintf "--- Protocol Version : %A" (getPV fsh));
                LogManager.GetLogger("file").Debug(sprintf "--- Sid : %s" (Bytes.hexString(getSID fsh)));
                LogManager.GetLogger("file").Debug(sprintf "--- Server Random : %s" (Bytes.hexString(fsh.rand)));
                LogManager.GetLogger("file").Info(sprintf "--- Ciphersuite : %A" (getCiphersuite fsh));
                LogManager.GetLogger("file").Debug(sprintf "--- Compression : %A" fsh.comp);
                LogManager.GetLogger("file").Debug(sprintf "--- Extensions : %A" (getExt fsh));
                LogManager.GetLogger("file").Debug(sprintf "--- Payload : %s" (Bytes.hexString(payload)));
                st,fsh,negExts
            )
        | _ -> failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected handshake type: %A" hstype))

    /// <summary>
    /// Prepare a ServerHello message that will not be sent to the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <param name="si"> Session Info of the currently negotiated next security context </param>
    /// <param name="cextL"> Client extensions list </param>
    /// <param name="cfg"> Optional Configuration of the server </param>
    /// <param name="verify_datas"> Optional verify data for client and server in case of renegotiation </param>
    /// <returns> Updated state * Updated negotiated session informations * FServerHello message record </returns>
    static member prepare (si:SessionInfo, sExtL:list<serverExtension>) : FServerHello =
        let ext = serverExtensionsBytes sExtL in
        let csname = match TLSConstants.name_of_cipherSuite si.cipher_suite with
            | Error(_,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
            | Correct(cs) -> cs
        in
        let payload = HandshakeMessages.serverHelloBytes si si.init_srand ext in
        let fsh = { pv = Some(si.protocol_version);
                    rand = si.init_srand;
                    sid = Some(si.sessionID);
                    ciphersuite = Some(csname);
                    comp = si.compression;
                    ext = Some(sExtL);
                    payload = payload;
                  }
        in
        fsh

    /// <summary>
    /// Send a ServerHello message to the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <param name="fch"> FClientHello message record containing client extensions </param>
    /// <param name="nsc"> Optional Next security context being negotiated </param>
    /// <param name="fsh"> Optional FServerHello message record </param>
    /// <param name="cfg"> Optional Server configuration if differs from default </param>
    /// <param name="fp"> Optional fragmentation policy at the record level </param>
    /// <returns> Updated state * Updated next security context * FServerHello message record </returns>
    static member send (st:state, fch:FClientHello, ?nsc:nextSecurityContext, ?fsh:FServerHello, ?cfg:config, ?fp:fragmentationPolicy) : state * nextSecurityContext * FServerHello =
        let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
        let nsc = defaultArg nsc FlexConstants.nullNextSecurityContext in
        let fsh = defaultArg fsh FlexConstants.nullFServerHello in
        let cfg = defaultArg cfg defaultConfig in

        let st,si,fsh = FlexServerHello.send(st,nsc.si,(getPV fsh),(FlexClientHello.getCiphersuites fch),(FlexClientHello.getCompressions fch),(FlexClientHello.getExt fch),fsh,cfg,fp=fp) in
        let nsc = { nsc with
                    si = si;
                    srand = fsh.rand;
                  }
        in
        st,nsc,fsh

    /// <summary>
    /// Send a ServerHello message to the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <param name="si"> Session Info of the currently negotiated next security context </param>
    /// <param name="cextL"> Client extensions list </param>
    /// <param name="cfg"> Optional Configuration of the server </param>
    /// <param name="fp"> Optional fragmentation policy at the record level </param>
    /// <returns> Updated state * Updated negotiated session information * FServerHello message record </returns>
    static member send (st:state, si:SessionInfo, cpv: ProtocolVersion, csuites:list<cipherSuiteName>, ccomps:list<Compression>, cextL:list<clientExtension>, ?fsh:FServerHello, ?cfg:config, ?fp:fragmentationPolicy) : state * SessionInfo * FServerHello =
        let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
        let cfg = defaultArg cfg defaultConfig in
        let fsh = defaultArg fsh FlexConstants.nullFServerHello in
        let srand =
            if fsh.rand = empty_bytes then
                (Nonce.mkHelloRandom si.protocol_version)
            else
                fsh.rand
        in

        // Check if the user gave us a session to resume, otherwise try to negotiate something sensible
        let si,sExtL =
            if si.sessionID = empty_bytes then
                // Protocol version
                let pv =
                    match fsh.pv with
                    | None -> minPV cpv cfg.maxVer
                    | Some(pv) -> pv
                in
                if (geqPV pv cfg.minVer) = false then
                    failwith (perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
                else

                // SessionID
                let sid =
                    match fsh.sid with
                    | None -> Nonce.random 32
                    | Some(sid) -> sid
                in

                // Ciphersuite
                let nCs =
                    match fsh.ciphersuite with
                    | None ->
                        (match Handshake.negotiate (cipherSuites_of_nameList csuites) cfg.ciphersuites with
                        | Some(nCs) -> nCs
                        | None -> failwith (perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation"))
                    | Some(ciphersuite) -> TLSConstants.cipherSuite_of_name ciphersuite
                in

                // Compression
                let nCm = NullCompression in

                // Extensions
                let (sExtL, nExtL) =
                    match fsh.ext with
                    | None ->
                        negotiateServerExtensions cextL cfg nCs (st.read.verify_data,st.write.verify_data) false
                    | Some(sExtL) ->
                        match negotiateClientExtensions cextL sExtL false nCs with
                        | Error(x,y) -> sExtL,FlexConstants.nullNegotiatedExtensions
                        | Correct(nExtL) -> sExtL,nExtL
                in

                let si = { si with
                            client_auth      = cfg.request_client_certificate;
                            sessionID        = sid;
                            protocol_version = pv;
                            cipher_suite     = nCs;
                            compression      = nCm;
                            extensions       = nExtL;
                            init_srand       = srand;
                            }
                in
                si,sExtL
            else
                let (sExtL, nExtL) = negotiateServerExtensions cextL cfg si.cipher_suite (st.read.verify_data,st.write.verify_data) true in
                si,sExtL
        in

        let st,fsh = FlexServerHello.send(st,si,sExtL,fp) in
        st,si,fsh

    /// <summary>
    /// Send a ServerHello message to the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <param name="si"> Session Info of the currently negotiated next security context </param>
    /// <param name="fp"> Optional fragmentation policy at the record level </param>
    /// <returns> Updated state * FServerHello message record </returns>
    static member send (st:state, si:SessionInfo, sExtL:list<serverExtension>, ?fp:fragmentationPolicy) : state * FServerHello =
        LogManager.GetLogger("file").Info("# SERVER HELLO : FlexServerHello.send");
        let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in

        let fsh = FlexServerHello.prepare(si,sExtL) in
        let st = FlexHandshake.send(st,fsh.payload,fp) in

        let ext = serverExtensionsBytes sExtL in
        LogManager.GetLogger("file").Debug(sprintf "--- Protocol Version : %A" (getPV fsh));
        LogManager.GetLogger("file").Debug(sprintf "--- Sid : %s" (Bytes.hexString(getSID fsh)));
        LogManager.GetLogger("file").Debug(sprintf "--- Server Random : %s" (Bytes.hexString(fsh.rand)));
        LogManager.GetLogger("file").Info(sprintf  "--- Ciphersuite : %A" (getCiphersuite fsh));
        LogManager.GetLogger("file").Debug(sprintf "--- Compression : %A" fsh.comp);
        LogManager.GetLogger("file").Debug(sprintf "--- Extensions : %A" (getExt fsh));
        st,fsh

    end
