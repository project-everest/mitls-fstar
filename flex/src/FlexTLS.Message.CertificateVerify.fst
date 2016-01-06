(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.Message.CertificateVerify


open Platform.Log
open Platform.Bytes
open Platfrom.Error

open MiTLS.TLSInfo
open MiTLS.TLSConstants
open MiTLS.HandshakeMessages

open FlexTLS.Types
open FlexTLS.Constants
open FlexTLS.Handshake



/// <summary>
/// Overload : Receive a CertificateVerify message from the network stream and check the log on demand
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="nsc"> Next security context to be updated </param>
/// <param name="fcreq"> FCertificateRequest previously used in the handshake that contains allowed signature and hash algorithms </param>
/// <returns> Updated state * Certificate Verify message </returns>
let receive (st:state) (nsc:nextSecurityContext) (fcreq:FCertificateRequest) (*?*)(check_log:bool) : state * FCertificateVerify =
  //  let checkLog = defaultArg check_log true in
  FlexCertificateVerify.receive(st,nsc,fcreq.sigAlgs,checkLog)

/// <summary>
/// Overload : Receive a CertificateVerify message from the network stream and check the log on demand
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="nsc"> Next security context to be updated </param>
/// <param name="algs"> Signature and hash algorithms allowed and usually provided by a Certificate Request </param>
/// <returns> Updated state * Certificate Verify message </returns>
let receive (st:state) (nsc:nextSecurityContext) (algs:list<Sig.alg>) (*?*)(check_log:bool) : state * FCertificateVerify =
  //  let checkLog = defaultArg check_log true in
  FlexCertificateVerify.receive(st,nsc.si,algs,check_log=checkLog,ms=nsc.secrets.ms)

/// <summary>
/// Receive a CertificateVerify message from the network stream and check the log on demand
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="si"> Session info being negotiated in the next security context </param>
/// <param name="algs"> Signature and hash algorithms allowed and usually provided by a Certificate Request </param>
/// <param name="ms"> Optional master secret that has to be provided to check the log if protocol version is SSL3 </param>
/// <returns> Updated state * Certificate Verify message </returns>
let receive (st:state) (si:SessionInfo) (algs:list<Sig.alg>) (*?*)(check_log:bool) (*?*)(ms:bytes) : state * FCertificateVerify =
  Log.logInfo("# CERTIFICATE VERIFY : FlexCertificateVerify.receive");
  //  let ms = defaultArg ms empty_bytes in
  let checkLog = if (defaultArg check_log true) then Some(st.hs_log) else None in
  let st,hstype,payload,to_log = FlexHandshake.receive(st) in
  match hstype with
  | HT_certificate_verify ->
    let alg,signature =
      match parseDigitallySigned algs payload si.protocol_version with
      | Correct(alg,signature) ->
        (match checkLog with
        | Some(expected) ->
          (match si.protocol_version with
          | TLS_1p3 ->
            (match Cert.get_chain_public_signing_key si.serverID alg with
            | Error(ad,x) -> failwith x
            | Correct(vkey) ->
              if Sig.verify alg vkey expected signature then
                (alg,signature)
              else
                failwith (perror __SOURCE_FILE__ __LINE__ "Signature does not match !"))
          | TLS_1p2 | TLS_1p1 | TLS_1p0 ->
            (match Cert.get_chain_public_signing_key si.clientID alg with
            | Error(ad,x) -> failwith x
            | Correct(vkey) ->
              if Sig.verify alg vkey expected signature then
                (alg,signature)
              else
                failwith (perror __SOURCE_FILE__ __LINE__ "Signature does not match !"))
          | SSL_3p0 ->
            let ms =
              if ms = empty_bytes then
                failwith (perror __SOURCE_FILE__ __LINE__ "Master Secret cannot be empty")
              else
                PRF.coerce (mk_msid si) ms
            in
            let (sigAlg,_) = alg in
            let alg = (sigAlg,NULL) in
            let expected = PRF.ssl_certificate_verify si ms sigAlg expected in
            (match Cert.get_chain_public_signing_key si.clientID alg with
            | Error(ad,x) -> failwith x
            | Correct(vkey) ->
              if Sig.verify alg vkey expected signature then
                (alg,signature)
              else
                failwith (perror __SOURCE_FILE__ __LINE__ "Signature does not match !"))
          )
        | None ->
          (alg,signature))
      | Error(ad,x) -> failwith x
    in
    let fcver : FCertificateVerify = { sigAlg = alg;
                                       signature = signature;
                                       payload = to_log;
                                     }
    in
    Log.logInfo(sprintf "--- Algorithm : %A" fcver.sigAlg);
    Log.logInfo(sprintf "--- Signature : %s" (Bytes.hexString(fcver.signature)));
    LogManager.GetLogger("file").Debug(sprintf "--- Payload : %s" (Bytes.hexString(payload)));
    st,fcver
  | _ -> failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected handshake type: %A" hstype))

/// <summary>
/// Prepare a CertificateVerify message that will not be sent to the network stream
/// </summary>
/// <param name="log"> Log of the current handshake </param>
/// <param name="cs"> Ciphersuite of the current Handshake </param>
/// <param name="pv"> Protocol version of the current Handshake </param>
/// <param name="alg"> Signature algorithm allowed and usually provided by a Certificate Request </param>
/// <param name="skey"> Signature secret key associated to the algorithm </param>
/// <param name="ms"> Master secret that has to be provided to compute the log if protocol version is SSL3 </param>
/// <returns> Certificate Verify bytes * Certificate Verify record </returns>
let prepare (log:bytes) (cs:cipherSuite) (pv:ProtocolVersion) (alg:Sig.alg) (skey:Sig.skey) (ms:bytes) : FCertificateVerify =
  let si = { FlexConstants.nullSessionInfo with
             cipher_suite = cs;
             protocol_version = pv
           } 
  in
  let ams = (PRF.coerce (mk_msid si) ms) in
  let payload,tag = HandshakeMessages.makeCertificateVerifyBytes si ams alg skey log in
  let fcver = { sigAlg = alg; signature = tag; payload = payload } in
  Log.logInfo(sprintf "--- Algorithm: %A" fcver.sigAlg);
  Log.logInfo(sprintf "--- Signature: %s" (Bytes.hexString fcver.signature));
  fcver

/// <summary>
/// Overload : Send a CertificateVerify (signature over the current log) message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="si"> Session info being negotiated in the next security context </param>
/// <param name="alg"> Signature algorithm allowed and usually provided by a Certificate Request </param>
/// <param name="skey"> Signature secret key associated to the algorithm </param>
/// <param name="ms"> Optional master secret that has to be provided to compute the log if protocol version is SSL3 </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * Certificate Verify message </returns>
let send (st:state) (si:SessionInfo) (alg:Sig.alg) (skey:Sig.skey) (*?*)(ms:bytes) (*?*)(fp:fragmentationPolicy) : state * FCertificateVerify =
  // let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let ms = defaultArg ms empty_bytes in
  FlexCertificateVerify.send(st,si.cipher_suite,si.protocol_version,alg,skey,ms,fp)

/// <summary>
/// Send a CertificateVerify (signature over the current log) message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="cs"> Ciphersuite of the current Handshake </param>
/// <param name="pv"> Protocol version of the current Handshake </param>
/// <param name="alg"> Signature algorithm allowed and usually provided by a Certificate Request </param>
/// <param name="skey"> Signature secret key associated to the algorithm </param>
/// <param name="ms"> Optional master secret that has to be provided to compute the log if protocol version is SSL3 </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * Certificate Verify message </returns>
let send (st:state) (cs:cipherSuite) (pv:ProtocolVersion) (alg:Sig.alg) (skey:Sig.skey) (*?*)(ms:bytes) (*?*)(fp:fragmentationPolicy) : state * FCertificateVerify =
  Log.logInfo("# CERTIFICATE VERIFY : FlexCertificateVerify.send");
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  //  let ms = defaultArg ms empty_bytes in
  let fcver = FlexCertificateVerify.prepare(st.hs_log,cs,pv,alg,skey,ms) in
  let st = FlexHandshake.send (st,fcver.payload,fp) in
  st,fcver

