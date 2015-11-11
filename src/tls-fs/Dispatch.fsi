(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Dispatch

open Bytes
open TLSConstants
open Tcp
open Error
open TLSError
open Record
open Handshake
open TLSInfo
open DataStream
open Range

[<NoEquality;NoComparison>]
type preConnection
type Connection = preConnection
type nextCn = Connection
type nullCn = Connection
type query = Cert.chain
type msg_i = range * delta
type msg_o = range * delta

val networkStream: Connection -> NetworkStream
val init:   NetworkStream -> Role -> config -> Connection
val resume: NetworkStream -> sessionID -> config -> Connection

val rehandshake: Connection -> config -> bool * nextCn
val rekey:       Connection -> config -> bool * nextCn
val request:     Connection -> config -> bool * nextCn

val full_shutdown: Connection -> Connection
val half_shutdown: Connection -> unit

type writeOutcome =
    | WError of string (* internal *)
    | WriteAgain (* Possibly more data to send *)
    | WriteAgainFinishing (* Possibly more data to send, and the outgoing epoch changed *)
    | WriteAgainClosing (* An alert must be sent before the connection is torn down *)
    | WDone (* No more data to send in the current state *)
    | WAppDataDone (* App data have been sent, no more data to send *)
    | WriteFinished (* The finished message has been sent, but the handshake is not over *)
    | WHSDone (* The handshake is complete *)
    | SentFatal of alertDescription * string (* The alert that has been sent *)
    | SentClose

type readOutcome =
    | WriteOutcome of writeOutcome 
    | RError of string (* internal *)
    | RAgain
    | RAgainFinishing
    | RAppDataDone of msg_i
    | RQuery of query * bool
    | RFinished
    | RHSDone
    | RClose
    | RFatal of alertDescription (* The received alert *)
    | RWarning of alertDescription (* The received alert *)
    
val write:        Connection -> msg_o -> Connection * writeOutcome
val read:         Connection -> Connection * readOutcome
val authorize:    Connection -> query -> Connection * readOutcome
val refuse:       Connection -> query -> unit

val getEpochIn:   Connection -> epoch
val getEpochOut:  Connection -> epoch
val getInStream:  Connection -> stream
val getOutStream: Connection -> stream
