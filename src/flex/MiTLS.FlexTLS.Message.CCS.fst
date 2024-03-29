(* Copyright (C) 2012--2016 Microsoft Research and INRIA *)

module MiTLS.FlexTLS.Message.CCS
open MiTLS


open MiTLS.Log
open MiTLS.Platform
open MiTLS.Platform.Bytes
open MiTLS.Platform.Error

open MiTLS.TLSConstants

open MiTLS.FlexTLS.Types
open MiTLS.FlexTLS.Constants
open MiTLS.FlexTLS.State
open MiTLS.FlexTLS.Record


/// Access the log
let log = Log.retrieve "FlexTLS.Log.General"

/// <summary>
/// Receive CCS message from network stream
/// </summary>
/// <param name="st"> State of the current Handshake </param>
/// <returns> Updated state * CCS record * CCS byte </returns>
let receive (st:state) : state * FChangeCipherSpecs * bytes =
  Log.write log Info "TLS Message" "# CCS : FlexCCS.receive";
  let ct,pv,len,_ = FlexRecord.parseFragmentHeader st in
  match ct with
  | Change_cipher_spec -> 
    let st,payload = FlexTLS.Record.getFragmentContent st Change_cipher_spec len in
    if payload = HandshakeMessages.CCSBytes then
      (Log.write log Debug "Payload" (sprintf "%s" (Bytes.hexString payload));
      st,{payload = payload },payload)
    else
      failwith (perror __SOURCE_FILE__ __LINE__ "Unexpected CCS content")
  | _ ->
    let _,b = FlexTLS.Record.getFragmentContent st ct len in
    failwith (perror __SOURCE_FILE__ __LINE__ (sprintf "Unexpected content type : %A\n Payload (%d Bytes) : %s" ct len (Bytes.hexString b)))

/// <summary>
/// Forward CCS to the network stream
/// </summary>
/// <param name="stin"> State of the current Handshake on the incoming side </param>
/// <param name="stout"> State of the current Handshake on the outgoing side </param>
/// <returns> Updated incoming state * Updated outgoing state * forwarded CCS byte </returns>
let forward (stin:state) (stout:state) : state * state * bytes =
  Log.write log Info "" "# CCS : FlexTLS.Message.CCS.forward";
  let stin,ccs,msgb  = FlexTLS.Message.CCS.receive stin in
  let stout,_ = FlexTLS.Message.CCS.send stout in
  Log.write log Debug "Payload" (sprintf "--- Payload : %s" (Bytes.hexString msgb));
  stin,stout,msgb

/// <summary>
/// Send CCS to the network stream
/// </summary>
/// <param name="st"> State of the current Handshake on the incoming side </param>
/// <param name="fccs"> Optional CCS message record </param>
/// <returns> Updated state * CCS message record </returns>
let send (st:state) (*?*)(fccs:FChangeCipherSpecs) : state * FChangeCipherSpecs =
  Log.write log Info "TLS Message" ("# CCS : FlexCCS.send");
  //  let fccs = defaultArg fccs FlexTLS.Message.Constants.nullFChangeCipherSpecs in
  let record_write,_,_ = FlexTLS.Record.send 
                           st.ns st.write.epoch st.write.record
                           Change_cipher_spec fccs.payload
                           st.write.epoch_init_pv in
  let st = FlexTLS.State.updateOutgoingRecord st record_write in
  Log.write log Debug "Payload" (sprintf "%s" (Bytes.hexString fccs.payload));
  st,fccs
