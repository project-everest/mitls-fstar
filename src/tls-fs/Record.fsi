(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Record

open Bytes
open Tcp
open TLSConstants
open Error
open TLSError
open TLSInfo
open Range

/// Implements stateful AE on top of LHAE,
/// managing sequence numbers and the binary record format

type ConnectionState
type sendState = ConnectionState
type recvState = ConnectionState

val initConnState: epoch -> rw -> StatefulLHAE.state -> ConnectionState
val nullConnState: epoch -> rw -> ConnectionState

val parseHeader: bytes -> Result<(ContentType * ProtocolVersion * nat)>
val makePacket: ContentType -> ProtocolVersion -> bytes -> bytes

//CF postV1, do some uniform renaming, e.g. s/Out/Send/
val recordPacketOut: epoch -> sendState -> ProtocolVersion -> range -> ContentType -> TLSFragment.fragment -> (sendState * bytes)
val recordPacketIn : epoch -> recvState -> ContentType -> bytes -> Result<(recvState * range * TLSFragment.fragment)>

val history: epoch -> rw -> ConnectionState -> TLSFragment.history

//CF val historyStream: epoch -> ConnectionState -> ContentType -> DataStream.stream

(*TODO val dataAvailable: recvState -> Result<bool> *)
(*TODO val coherentrw: SessionInfo -> recvState -> sendState -> bool *)

(*TODO ProtocolVersion: 
  - the interface can be used only for setting and checking them (they are never passed up)
  - initially, sendState is the minimal and recvState is Unknown. 
  - for receiving only, the "Unknown" ProtocolVersion means that we do not know yet, 
    so we are accepting any reasonable one in each record.
    Conservatively, we change from Unknown to the first received version. *)

(*TODO for now, we do not provide an interface for reporting sequence number overflows *)

 
