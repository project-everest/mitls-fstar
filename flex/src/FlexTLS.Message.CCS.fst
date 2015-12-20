(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module FlexTLS.Message.CCS


open Platform
open Platform.Log
open Platform.Bytes
open Platform.Error

open MiTLS.TLSConstants

open FlexTLS.Types
open FlexTLS.Constants
open FlexTLS.State
open FlexTLS.Record



/// <summary>
/// Receive CCS message from network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <returns> Updated state * CCS record * CCS byte </returns>
let receive (st:state) : state * FChangeCipherSpecs * bytes =
  Log.logInfo("# CCS : FlexCCS.receive");
  let ct,pv,len,_ = FlexRecord.parseFragmentHeader st in
  match ct with
  | Change_cipher_spec -> 
    let st,payload = FlexRecord.getFragmentContent(st,Change_cipher_spec,len) in
    if payload = HandshakeMessages.CCSBytes then
      (Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(payload)));
      st,{payload = payload },payload)
    else
      failwith (perror __SOURCE_FILE__ __LINE__ "Unexpected CCS content")
  | _ ->
    let _,b = FlexRecord.getFragmentContent (st, ct, len) in
    failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected content type : %A\n Payload (%d Bytes) : %s" ct len (Bytes.hexString(b))))

/// <summary>
/// Forward CCS to the network stream
/// </summary>
/// <param name="stin"> State of the current Handshake on the incoming side </param>
/// <param name="stout"> State of the current Handshake on the outgoing side </param>
/// <returns> Updated incoming state * Updated outgoing state * forwarded CCS byte </returns>
let forward (stin:state, stout:state) : state * state * bytes =
  Log.logInfo("# CCS : FlexCCS.forward");
  let stin,ccs,msgb  = FlexCCS.receive(stin) in
  let stout,_ = FlexCCS.send(stout) in
  Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(msgb)));
  stin,stout,msgb

/// <summary>
/// Send CCS to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake on the incoming side </param>
/// <param name="fccs"> Optional CCS message record </param>
/// <returns> Updated state * CCS message record </returns>
let send (st:state, ?fccs:FChangeCipherSpecs) : state * FChangeCipherSpecs =
  Log.logInfo("# CCS : FlexCCS.send");
  let fccs = defaultArg fccs FlexConstants.nullFChangeCipherSpecs in
  let record_write,_,_ = FlexRecord.send( st.ns, st.write.epoch, st.write.record,
                                          Change_cipher_spec, fccs.payload,
                                          st.write.epoch_init_pv) in
  let st = FlexState.updateOutgoingRecord st record_write in
  Log.logDebug(sprintf "--- Payload : %s" (Bytes.hexString(fccs.payload)));
  st,fccs
