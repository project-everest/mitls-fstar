(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.Secrets


open Log
open Platform.Bytes
open Platform.Error

open MiTLS.TLSInfo
open MiTLS.TLSConstants

open FlexTypes
open FlexConstants
open FlexState



/// Access the log
let log = Log.retrieve "FlexTLS.Log.General"

/// <summary>
/// Coerce a DH parameter from bytes to DH.secret abstract type
/// </summary>
/// <param name="x"> Bytes of the DH parameter </param>
/// <returns> Abstract DH parameter </returns>
let dh_coerce (x:bytes) : CommonDH.secret =
  CommonDH.coerce (CommonDH.DHP_P(FlexConstants.defaultDHParams)) CommonDH.dhe_nil x

/// <summary>
/// Leak a DH parameter from DH.secret abstract type to bytes
/// </summary>
/// <param name="x"> Abstract DH parameter </param>
/// <returns> DH parameter bytes </returns>
let dh_leak (x:CommonDH.secret) : bytes =
  CommonDH.leak (CommonDH.DHP_P(FlexConstants.defaultDHParams)) CommonDH.dhe_nil x

/// <summary>
/// Generate the PreMasterSecret from the key exchange parameters
/// </summary>
/// <param name="kex"> Key Exchange record </param>
/// <returns>  PreMasterSecret bytes </returns>
let kex_to_pms (kex:kex) : bytes =
  match kex with
  | RSA(pms) -> pms
  | DH(dhp) ->
    let p,_ = dhp.pg in
    CoreDH.agreement p dhp.x dhp.gy
  | DH13(dh13) ->
    let dhparams = dhgroup_to_dhparams dh13.group in
    CoreDH.agreement dhparams.dhp dh13.x dh13.gy
  | ECDH(kexecdh) ->
    let ecdhparams = ECGroup.getParams kexecdh.curve in
    let ecx,ecy = kexecdh.ecp_y in
    let ecp_y : ECGroup.point = {ecx = ecx; ecy = ecy } in
    CoreECDH.agreement ecdhparams kexecdh.x ecp_y

/// <summary>
/// Generate the MasterSecret from the PreMasterSecret
/// </summary>
/// <param name="pms"> PreMasterSecret bytes </param>
/// <returns>  MasterSecret bytes </returns>
let pms_to_ms (si:SessionInfo) (pms:bytes) : bytes =
(* It doesn't really matter if we coerce to DH or RSA, as internally
they're both just bytes. This is why the code requires dh params even for RSA *)
  let apms = PMS.coerceDH FlexConstants.defaultDHParams empty_bytes empty_bytes pms in
  let pms =
    let ee = {CommonDH.dhe_nil with dhe_p = Some empty_bytes} in
    PMS.DHPMS((CommonDH.DHP_P(FlexConstants.defaultDHParams)),ee,ee,apms) in
  let ams =
    if si.extensions.ne_extended_ms then
      KEF.extract_extended si pms
    else
      KEF.extract si pms
  in
  PRF.leak (mk_msid si) ams

/// <summary>
/// Generate all encryption keys from the MasterSecret and swap them in the proper order using the role
/// </summary>
/// <param name="er"> Next reading epoch </param>
/// <param name="ew"> Next writing epoch </param>
/// <param name="role"> Behavior as client or Server </param>
/// <param name="ms"> MasterSecret bytes </param>
/// <returns>  Reading keys bytes * Writing keys bytes </returns>
let ms_to_keys (er:epoch) (ew:epoch) (role:Role) (ms:bytes) : bytes * bytes =
  let ams = PRF.coerce (mk_msid (epochSI er)) ms in
  let ark,awk = PRF.deriveKeys (TLSInfo.mk_id er) (TLSInfo.mk_id ew) ams role in
  let rk = StatefulLHAE.LEAK (TLSInfo.mk_id er) TLSInfo.Reader ark in
  let wk = StatefulLHAE.LEAK (TLSInfo.mk_id ew) TLSInfo.Writer awk in
  rk,wk

/// <summary>
/// Compute verify_data from log and necessary informations
/// </summary>
/// <param name="si"> Next session info being negotiated </param>
/// <param name="ms"> MasterSecret bytes </param>
/// <param name="role"> Behavior as Client or Server </param>
/// <param name="log"> Log of the current Handshake messages </param>
/// <returns> Verify_data bytes </returns>
let makeVerifyData (si:SessionInfo) (ms:bytes) (role:Role) (log:bytes) : bytes =
  let ams = PRF.coerce (mk_msid si) ms in
  PRF.makeVerifyData si ams role log

/// <summary>
/// Generate secrets from the Key Exchange data and fill the next security context.
/// It is assumed that the nsc.kex field is already set to the desired value.
/// Any user-provided value will not be overwritten; instead it will be used for secrets generation.
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <param name="role"> Behavior as client or Server </param>
/// <param name="nsc"> Next security context being negotiated </param>
/// <returns> Updated next security context </returns>
let fillSecrets (st:state) (role:Role) (nsc:nextSecurityContext) : nextSecurityContext =
  Log.write log Debug "" "@ Fill Secrets";
  let er = FlexState.guessNextEpoch st.read.epoch  nsc in
  let ew = FlexState.guessNextEpoch st.write.epoch nsc in

  let pms =
    if nsc.secrets.pms = empty_bytes then
      FlexSecrets.kex_to_pms nsc.secrets.kex
    else
      nsc.secrets.pms
  in

  let ms = if nsc.secrets.ms = empty_bytes then FlexSecrets.pms_to_ms nsc.si pms else nsc.secrets.ms in
  let secrets = if nsc.secrets.epoch_keys = (empty_bytes,empty_bytes) then FlexSecrets.ms_to_keys er ew role ms else nsc.secrets.epoch_keys in
  let rkeys,wkeys = secrets in
  let epk_secrets = {nsc.secrets with pms = pms; ms = ms; epoch_keys = secrets} in
  Log.write log Debug "" (sprintf "--- Pre Master Secret : %A" (Bytes.hexString(pms)));
  Log.write log Debug "" (sprintf "--- Master Secret : %A" (Bytes.hexString(ms)));
  Log.write log Debug "" (sprintf "--- Reading Keys : %A" (Bytes.hexString(rkeys)));
  Log.write log Debug "" (sprintf "--- Writing Keys : %A" (Bytes.hexString(wkeys)));
  { nsc with secrets = epk_secrets }
