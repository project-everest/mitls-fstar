(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.Message.CertificateRequest


open Platform.Log
open Platform.Bytes
open Platform.Error

open MiTLS.TLSInfo
open MiTLS.TLSConstants
open MiTLS.HandshakeMessages

open FlexTLS.Types
open FlexTLS.Constants
open FlexTLS.Handshake


    /// <summary>
    /// Receive a CertificateRequest message from the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <param name="nsc"> Optional Next security context object updated with new data </param>
    /// <returns> Updated state * next security context * FCertificateRequest message record </returns>
    static member receive (st:state, ?nsc:nextSecurityContext) : state * nextSecurityContext * FCertificateRequest =
        LogManager.GetLogger("file").Info("# CERTIFICATE REQUEST : FlexCertificateRequest.receive");
        let nsc = defaultArg nsc FlexConstants.nullNextSecurityContext in
        let si = nsc.si in
        let pv = si.protocol_version in
        let st,hstype,payload,to_log = FlexHandshake.receive(st) in
        match hstype with
        | HT_certificate_request  ->
            (match parseCertificateRequest pv payload with
            | Error (_,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
            | Correct (certTypes,sigAlgs,names) ->
                let certReq : FCertificateRequest = {
                    certTypes = certTypes;
                    sigAlgs = sigAlgs;
                    names = names;
                    payload = to_log
                } in
                let si  = { si with client_auth = true} in
                let nsc = { nsc with si = si } in
                LogManager.GetLogger("file").Debug(sprintf "--- Payload : %s" (Bytes.hexString(payload)));
                (st,nsc,certReq)
            )
        | _ -> failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected handshake type: %A" hstype))

    /// <summary>
    /// Prepare a CertificateRequest message that won't be sent to the network stream
    /// </summary>
    /// <param name="cs"> Ciphersuite used to generate the request </param>
    /// <param name="pv"> Protocol version used to generate the request </param>
    /// <returns> FCertificateRequest message record</returns>
    static member prepare (cs:cipherSuite, pv:ProtocolVersion): FCertificateRequest =
        let payload = HandshakeMessages.certificateRequestBytes true cs pv in

        // We return dummy values in the FCertificateRequest sigAlgs so it can be used later by FCertificateVerify functions
        let fcreq = { FlexConstants.nullFCertificateRequest with sigAlgs = FlexConstants.sigAlgs_ALL ; payload = payload } in
        fcreq

    /// <summary>
    /// Send a CertificateRequest message to the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <param name="nsc"> Optional next security context to be updated </param>
    /// <param name="fp"> Optional fragmentation policy at the record level </param>
    /// <returns> Updated state * FCertificateRequest message record </returns>
    static member send (st:state, ?nsc:nextSecurityContext, ?fp:fragmentationPolicy): state * FCertificateRequest =

        let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
        let nsc = defaultArg nsc FlexConstants.nullNextSecurityContext in
        FlexCertificateRequest.send(st,nsc.si.cipher_suite,nsc.si.protocol_version,fp)

    /// <summary>
    /// Send a CertificateRequest message to the network stream
    /// </summary>
    /// <param name="st"> State of the current Handshake </param>
    /// <param name="cs"> Ciphersuite used to generate the request </param>
    /// <param name="pv"> Protocol version used to generate the request </param>
    /// <param name="fp"> Optional fragmentation policy at the record level </param>
    /// <returns> Updated state * FCertificateRequest message record </returns>
    static member send (st:state, cs:cipherSuite, pv:ProtocolVersion, ?fp:fragmentationPolicy): state * FCertificateRequest =
        LogManager.GetLogger("file").Info("# CERTIFICATE REQUEST : FlexCertificateRequest.send");
        let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in

        let fcreq = FlexCertificateRequest.prepare(cs,pv) in
        let st = FlexHandshake.send (st,fcreq.payload,fp) in
        st,fcreq
    end
