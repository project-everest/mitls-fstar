(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.Message.ServerKeyExchange


open Platform.Log
open Platform.Bytes
open Platform.Error

open MiTLS.TLSInfo
open MiTLS.TLSConstants
open MiTLS.TLSExtensions
open MiTLS.HandshakeMessages
open MiTLS.CommonDH

open FlexTLS.Types
open FlexTLS.Secrets
open FlexTLS.Constants
open FlexTLS.Handshake



/// <summary>
/// Fill kexDH structure by eventually finishing computation of all Diffie Hellman parameters.
/// </summary>
let filldh kexdh =
  let (p,g) = kexdh.pg in
  let x, gx =
    match kexdh.x,kexdh.gx with
    | x, gx when x = empty_bytes && gx = empty_bytes ->
      CoreDH.gen_key_pg p g
    | x, gx when gx = empty_bytes ->
      x, CoreDH.agreement p x g
    | x, gx -> x,gx
  in
  {kexdh with x = x; gx = gx}

/// <summary>
/// Fill kexECDH structure by eventually finishing computation of all Elliptic Curve Diffie Hellman parameters.
/// </summary>
let fillecdh kexecdh =
  let x, ecp_x =
    match kexecdh.x, kexecdh.ecp_x with
    | x, ecp_x when x = empty_bytes || ecp_x = (empty_bytes,empty_bytes) ->
      CoreECDH.gen_key (ECGroup.getParams kexecdh.curve)
    | x, ecp_x ->
      let ecx, ecy = ecp_x in
      x,{ecx = ecx; ecy = ecy}
  in
  {kexecdh with x = x; ecp_x = (ecp_x.ecx, ecp_x.ecy)}


/// <summary>
/// Receive DHE ServerKeyExchange from the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="nsc"> Next security context being negotiated </param>
/// <param name="check_sig"> Optional check on the Server certificate chain </param>
/// <param name="minDHsize"> Optional Minimal sizes for DH parameters.
///    If provided, received DH parameters will be checked for validity and their size;
///    if not provided, no check at all will be performed on the received parameters </param>
/// <returns> Updated state * Updated next security context * FServerKeyExchange message record </returns>
let receiveDHE (st:state, nsc:nextSecurityContext, (*?*)check_sig:bool, (*?*)minDHsize:nat*nat): state * nextSecurityContext * FServerKeyExchange =
  //  let check_sig = defaultArg check_sig false in
  let st,fske =
    match minDHsize with
    | None -> FlexServerKeyExchange.receiveDHE(st,nsc.si.protocol_version,nsc.si.cipher_suite)
    | Some(minDHsize) -> FlexServerKeyExchange.receiveDHE(st,nsc.si.protocol_version,nsc.si.cipher_suite,minDHsize)
  in
  let epk = {nsc.secrets with kex = fske.kex} in
  let nsc = {nsc with secrets = epk} in
  if check_sig then
    let kexDH =
      match nsc.secrets.kex with
      | DH(x) -> x
      | _ -> failwith (perror __SOURCE_FILE__ __LINE__ "Internal error: receiveDHE should return a DH kex")
    in
    let p,g = kexDH.pg in
    let gy = kexDH.gy in
    let dheB = CommonDH.serializeKX (DHP_P {dhp=p; dhg = g; dhq=empty_bytes; safe_prime=false}) {dhe_nil with dhe_p = Some gy} in
    let expected = nsc.crand @| nsc.srand @| dheB in
    match Cert.get_chain_public_signing_key nsc.si.serverID fske.sigAlg with
    | Error(_,x) -> failwith (perror __SOURCE_FILE__ __LINE__  x)
    | Correct(vkey) ->
      if Sig.verify fske.sigAlg vkey expected fske.signature then
        st,nsc,fske
      else
        failwith (perror __SOURCE_FILE__ __LINE__ "Signature check failed")
  else
    st,nsc,fske

/// <summary>
/// Receive DHE ServerKeyExchange from the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="pv"> Protocol version negotiated </param>
/// <param name="cs"> Ciphersuite negotiated </param>
/// <param name="minDHsize"> Optional Minimal sizes for DH parameters.
///    If provided, received DH parameters will be checked for validity and their size;
///    if not provided, no check at all will be performed on the received parameters </param>
/// <returns> Updated state * FServerKeyExchange message record </returns>
let receiveDHE (st:state, pv:ProtocolVersion, cs:cipherSuite, (*?*)minDHsize:nat*nat) : state * FServerKeyExchange =
  Log.LogInfo("# SERVER KEY EXCHANGE : FlexServerKeyExchange.receiveDHE");
  let st,hstype,payload,to_log = FlexHandshake.receive(st) in
  //  let mindh = defaultArg minDHsize FlexConstants.minDHSize in
  match hstype with
  | HT_server_key_exchange  ->
    (match HandshakeMessages.parseServerKeyExchange_DHE FlexConstants.dhdb mindh pv cs payload with
    | Error (_,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
    | Correct (dhdb, p, e ,alg,signature) ->
      let gy = CommonDH.get_p e in
      let p, g = match p with DHP_P { dhp = p; dhg  = g; dhq = q; safe_prime = _; } -> p, g | _ -> failwith "" in
      Log.logDebug(sprintf "---S Public Prime : %s" (Bytes.hexString(p)));
      Log.logDebug(sprintf "---S Public Generator : %s" (Bytes.hexString(g)));
      Log.logDebug(sprintf "---S Public Exponent : %s" (Bytes.hexString(gy)));
      Log.logDebug(sprintf "---S Signature algorithm : %A" (alg));
      Log.logDebug(sprintf "---S Signature : %s" (Bytes.hexString(signature)));
      Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(payload)));
//                (match minDHsize with
//                | None -> ()
//                | Some(minDHsize) ->
//                    // Check params and validate y
//                    match DHGroup.checkParams FlexConstants.dhdb minDHsize p g with
//                    | Error (_,x) -> failwith x
//                    | Correct(res) ->
//                        let (_,dhp) = res in
//                        match DHGroup.checkElement dhp gy with
//                        | None ->
//                            failwith "Server sent an invalid DH key"
//                        | Some(_) -> ()
//                );
      let kexdh = {pg = (p,g); x = empty_bytes; gx = empty_bytes; gy = gy} in
      let fske : FServerKeyExchange = { kex = DH(kexdh); payload = to_log; sigAlg = alg; signature = signature } in
      st,fske
    )
  | _ -> failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected handshake type: %A" hstype))

/// <summary>
/// Prepare DHE ServerKeyExchange message bytes that will not be sent to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="kexdh"> Key Exchange record containing Diffie-Hellman parameters </param>
/// <param name="crand"> Client public randomness </param>
/// <param name="srand"> Server public randomness </param>
/// <param name="pv"> Protocol version negotiated </param>
/// <param name="sigAlg"> Signature algorithm allowed and usually provided by a Certificate Request </param>
/// <param name="sigKey"> Signature secret key associated to the algorithm </param>
/// <returns> FServerKeyExchange message bytes * Updated state * FServerKeyExchange message record </returns>
let prepareDHE (kexdh:kexDH, crand:bytes, srand:bytes, pv:ProtocolVersion, sigAlg:Sig.alg, sigKey:Sig.skey) : FServerKeyExchange * kexDH =

  let kexdh = filldh kexdh in
  let p,g = kexdh.pg in
  let gx  = kexdh.gx in
  let dheB = CommonDH.serializeKX (DHP_P {dhp=p; dhg = g; dhq=empty_bytes; safe_prime=false}) {dhe_nil with dhe_p = Some gx} in
  let msgb = crand @| srand @| dheB in
  let sign = Sig.sign sigAlg sigKey msgb in

  let payload = HandshakeMessages.serverKeyExchangeBytes_DHE dheB sigAlg sign pv in
  let fske = { sigAlg = sigAlg; signature = sign; kex = DH(kexdh) ; payload = payload } in
  // We redundantly return kexdh for a better log
  fske,kexdh

/// <summary>
/// Send a DHE ServerKeyExchange message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="nsc"> Next security context being negotiated </param>
/// <param name="sigAlgAndKey"> Optional pair of Signature Algorithm and Signing key to use by force </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * FServerKeyExchange message record </returns>
let sendDHE (st:state, nsc:nextSecurityContext, (*?*)sigAlgAndKey:(Sig.alg * Sig.skey), (*?*)fp:fragmentationPolicy) : state * nextSecurityContext * FServerKeyExchange =
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let sAlg,sKey =
    match sigAlgAndKey with
    | Some(sak) -> sak
    | None ->
      match Cert.get_hint nsc.si.serverID with
      | None -> failwith (perror __SOURCE_FILE__ __LINE__ "Wrong server certificate provided")
      | Some(hint) ->
        let sigAlgs = TLSExtensions.default_sigHashAlg nsc.si.protocol_version nsc.si.cipher_suite in
        match Cert.for_signing sigAlgs hint sigAlgs with
        | None -> failwith (perror __SOURCE_FILE__ __LINE__ "Cannot find private key for certificate")
        | Some(_,sAlg,sKey) -> sAlg,sKey
  in
  let kexdh = 
    match nsc.secrets.kex with
    | DH(kexdh) -> kexdh
    | _ -> FlexConstants.nullKexDH
  in
  let st,fske = FlexServerKeyExchange.sendDHE(st,kexdh,nsc.crand,nsc.srand,nsc.si.protocol_version,sAlg,sKey,fp) in
  let epk = {nsc.secrets with kex = fske.kex } in
  let nsc = {nsc with secrets = epk} in
  st,nsc,fske

/// <summary>
/// Send a DHE ServerKeyExchange message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="kexdh"> Key Exchange record containing Diffie-Hellman parameters </param>
/// <param name="crand"> Client public randomness </param>
/// <param name="srand"> Server public randomness </param>
/// <param name="pv"> Protocol version negotiated </param>
/// <param name="sigAlg"> Signature algorithm allowed and usually provided by a Certificate Request </param>
/// <param name="sigKey"> Signature secret key associated to the algorithm </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * FServerKeyExchange message record </returns>
let sendDHE (st:state, kexdh:kexDH, crand:bytes, srand:bytes, pv:ProtocolVersion, sigAlg:Sig.alg, sigKey:Sig.skey, (*?*)fp:fragmentationPolicy) : state * FServerKeyExchange =
  Log.LogInfo("# SERVER KEY EXCHANGE : FlexServerKeyExchange.sendDHE");
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let fske,dh = FlexServerKeyExchange.prepareDHE(kexdh,crand,srand,pv,sigAlg,sigKey) in
  let st = FlexHandshake.send(st,fske.payload,fp) in
  let p,g = dh.pg in
  Log.logDebug(sprintf "--- Public Prime : %s" (Bytes.hexString(p)));
  Log.logDebug(sprintf "--- Public Generator : %s" (Bytes.hexString(g)));
  Log.logDebug(sprintf "--- Public Exponent : %s" (Bytes.hexString(dh.gx)));
  st,fske

(*** Elliptic Curve Diffie-Hellman ***)

/// <summary>
/// Receive ECDHE ServerKeyExchange from the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="nsc"> Next security context being negotiated </param>
/// <param name="check_sig"> Optional check on the Server certificate chain </param>
/// <param name="minECDHsize"> Optional Minimal sizes for Elliptic curve size parameters.
///     Currently, the check is not implemented
/// <returns> Updated state * Updated next security context * FServerKeyExchange message record </returns>
let receiveECDHE (st:state, nsc:nextSecurityContext, ?check_sig:bool, (*?*)minECDHsize:nat*nat): state * nextSecurityContext * FServerKeyExchange =
  //  let check_sig = defaultArg check_sig false in
  let st,fske =
   (* Check on the Curve size is not available at the moment *)
   (* match minECDHsize with
      | None -> FlexServerKeyExchange.receiveECDHE(st,nsc.si.protocol_version,nsc.si.cipher_suite)
      | Some(minECDHsize) -> FlexServerKeyExchange.receiveECDHE(st,nsc.si.protocol_version,nsc.si.cipher_suite,minECDHsize) *)
      FlexServerKeyExchange.receiveECDHE(st,nsc.si.protocol_version,nsc.si.cipher_suite)
  in
  let epk = {nsc.secrets with kex = fske.kex} in
  let nsc = {nsc with secrets = epk} in
  if check_sig then
    let kexecdh =
      match nsc.secrets.kex with
      | ECDH(x) -> x
      | _ -> failwith (perror __SOURCE_FILE__ __LINE__ "Internal error: receiveDHE should return a DH kex")
    in
    let curve,comp = kexecdh.curve,kexecdh.comp in
    let ecx,ecy = kexecdh.ecp_y in
    let ecdheB = CommonDH.serializeKX (DHP_EC (ECGroup.getParams curve)) {dhe_nil with dhe_ec = Some {ecx = ecx; ecy = ecy}} in
    let expected = nsc.crand @| nsc.srand @| ecdheB in
    match Cert.get_chain_public_signing_key nsc.si.serverID fske.sigAlg with
    | Error(_,x) -> failwith (perror __SOURCE_FILE__ __LINE__  x)
    | Correct(vkey) ->
      if Sig.verify fske.sigAlg vkey expected fske.signature then
        st,nsc,fske
      else
        failwith (perror __SOURCE_FILE__ __LINE__ "Signature check failed")
  else
    st,nsc,fske

/// <summary>
/// Receive ECDHE ServerKeyExchange from the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="pv"> Protocol version negotiated </param>
/// <param name="cs"> Ciphersuite negotiated </param>
/// <param name="minECDHsize"> Optional Minimal sizes for Elliptic curve size parameters.
///     Currently, the check is not implemented
/// <returns> Updated state * FServerKeyExchange message record </returns>
let receiveECDHE (st:state, pv:ProtocolVersion, cs:cipherSuite, (*?*)minECDHSize:nat) : state * FServerKeyExchange =
  Log.logInfo("# SERVER KEY EXCHANGE : FlexServerKeyExchange.receiveECDHE");
  let st,hstype,payload,to_log = FlexHandshake.receive(st) in
  //  let minECDHSize = defaultArg minECDHSize FlexConstants.minECDHSize in
  match hstype with
  | HT_server_key_exchange  ->
    (match HandshakeMessages.parseServerKeyExchange_DHE FlexConstants.dhdb (minECDHSize,minECDHSize) pv cs payload with
    | Error (_,x) -> failwith (perror __SOURCE_FILE__ __LINE__ x)
    | Correct (dhdb, p, e, alg, signature) ->
      let ecp_y = CommonDH.get_ec e in
      let ecp_yX,ecp_yY = match ecp_y with { ecx = ecx; ecy = ecy } -> ecx,ecy in
      let curve,comp =
        match p with
        | DHP_EC ({curve = eccurve; compression = comp}) ->
          let curve = ECGroup.curve_name {curve = eccurve; compression = comp} in
          curve,comp
        | _ -> failwith "This should be called only with ECDHE"
      in
      Log.logDebug(sprintf "--- Curve : %A" curve);
      Log.logDebug(sprintf "--- Compression : %A" comp);
      Log.logDebug(sprintf "--- Public Point : %s ; %s" (Bytes.hexString(ecp_yX)) (Bytes.hexString(ecp_yY)));
      Log.logDebug(sprintf "--- Signature algorithm : %A" (alg));
      Log.logDebug(sprintf "--- Signature : %s" (Bytes.hexString(signature)));
      Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(payload)));
      // Unlike in DHE, this check on the size is not done in miTLS so we can do it here =)  
      let kexecdh = {curve = curve; comp = comp; x = empty_bytes; ecp_x = (empty_bytes,empty_bytes); ecp_y = (ecp_yX,ecp_yY)} in
      let fske : FServerKeyExchange = { kex = ECDH(kexecdh); payload = to_log; sigAlg = alg; signature = signature } in
      st,fske
    )
  | _ -> failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected handshake type: %A" hstype))

/// <summary>
/// Prepare ECDHE ServerKeyExchange message bytes that will not be sent to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="kexecdh"> Key Exchange record containing Diffie-Hellman parameters </param>
/// <param name="crand"> Client public randomness </param>
/// <param name="srand"> Server public randomness </param>
/// <param name="pv"> Protocol version negotiated </param>
/// <param name="sigAlg"> Signature algorithm allowed and usually provided by a Certificate Request </param>
/// <param name="sigKey"> Signature secret key associated to the algorithm </param>
/// <returns> FServerKeyExchange message bytes * Updated state * FServerKeyExchange message record </returns>
let prepareECDHE (kexecdh:kexECDH, crand:bytes, srand:bytes, pv:ProtocolVersion, sigAlg:Sig.alg, sigKey:Sig.skey) : FServerKeyExchange * kexECDH =

  let kexecdh = fillecdh kexecdh in
  let ecx,ecy = kexecdh.ecp_x in
  let ecdheB = CommonDH.serializeKX (DHP_EC (ECGroup.getParams kexecdh.curve)) {dhe_nil with dhe_ec = Some {ecx = ecx; ecy = ecy}} i
  let msgb = crand @| srand @| ecdheB in
  let sign = Sig.sign sigAlg sigKey msgb in
  let payload = HandshakeMessages.serverKeyExchangeBytes_DHE ecdheB sigAlg sign pv in
  let fske = { sigAlg = sigAlg; signature = sign; kex = ECDH(kexecdh) ; payload = payload } in
  // We redundantly return kexecdh for a better log
  fske,kexecdh

/// <summary>
/// Send a ECDHE ServerKeyExchange message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="nsc"> Next security context being negotiated </param>
/// <param name="sigAlgAndKey"> Optional pair of Signature Algorithm and Signing key to use by force </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * FServerKeyExchange message record </returns>
let sendECDHE (st:state, nsc:nextSecurityContext, (*?*)sigAlgAndKey:(Sig.alg * Sig.skey), (*?*)fp:fragmentationPolicy) : state * nextSecurityContext * FServerKeyExchange =
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let sAlg,sKey =
    match sigAlgAndKey with
    | Some(sak) -> sak
    | None ->
      match Cert.get_hint nsc.si.serverID with
      | None -> failwith (perror __SOURCE_FILE__ __LINE__ "Wrong server certificate provided")
      | Some(hint) ->
        let sigAlgs = TLSExtensions.default_sigHashAlg nsc.si.protocol_version nsc.si.cipher_suite in
        match Cert.for_signing sigAlgs hint sigAlgs with
        | None -> failwith (perror __SOURCE_FILE__ __LINE__ "Cannot find private key for certificate")
        | Some(_,sAlg,sKey) -> sAlg,sKey
  in
  let kexecdh = 
    match nsc.secrets.kex with
    | ECDH(kexecdh) -> kexecdh
    | _ -> FlexConstants.nullKexECDH
  in
  let st,fske = FlexServerKeyExchange.sendECDHE(st,kexecdh,nsc.crand,nsc.srand,nsc.si.protocol_version,sAlg,sKey,fp) in
  let epk = {nsc.secrets with kex = fske.kex } in
  let nsc = {nsc with secrets = epk} in
  st,nsc,fske

/// <summary>
/// Send a ECDHE ServerKeyExchange message to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="kexecdh"> Key Exchange record containing Elliptic Curve Diffie-Hellman parameters </param>
/// <param name="crand"> Client public randomness </param>
/// <param name="srand"> Server public randomness </param>
/// <param name="pv"> Protocol version negotiated </param>
/// <param name="sigAlg"> Signature algorithm allowed and usually provided by a Certificate Request </param>
/// <param name="sigKey"> Signature secret key associated to the algorithm </param>
/// <param name="fp"> Optional fragmentation policy at the record level </param>
/// <returns> Updated state * FServerKeyExchange message record </returns>
let sendECDHE (st:state, kexecdh:kexECDH, crand:bytes, srand:bytes, pv:ProtocolVersion, sigAlg:Sig.alg, sigKey:Sig.skey, (*?*)fp:fragmentationPolicy) : state * FServerKeyExchange =
  Log.LogInfo("# SERVER KEY EXCHANGE : FlexServerKeyExchange.sendECDHE");
  //  let fp = defaultArg fp FlexConstants.defaultFragmentationPolicy in
  let fske,kexecdh = FlexServerKeyExchange.prepareECDHE(kexecdh,crand,srand,pv,sigAlg,sigKey) in
  let st = FlexHandshake.send(st,fske.payload,fp) in
  let ecp_xX,ecp_xY = kexecdh.ecp_x in
  Log.logDebug(sprintf "--- Curve : %A" kexecdh.curve);
  Log.logDebug(sprintf "--- Compression : %A" kexecdh.comp);
  Log.logDebug(sprintf "--- Public Point : %s ; %s" (Bytes.hexString(ecp_xX)) (Bytes.hexString(ecp_xY)));
  Log.logDebug(sprintf "--- Signature algorithm : %A" (fske.sigAlg));
  Log.logDebug(sprintf "--- Signature : %s" (Bytes.hexString(fske.signature)));
  Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(fske.payload)));
  st,fske
