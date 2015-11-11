(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module TLS

open Bytes
open Error
open TLSError
open Dispatch
open TLSInfo
open Tcp
open DataStream

type Connection = Dispatch.Connection

type ioresult_i =
    | ReadError of option<alertDescription> * string
    | Close     of Tcp.NetworkStream
    | Fatal     of alertDescription
    | Warning   of nextCn * alertDescription 
    | CertQuery of nextCn * query * bool
    | CompletedFirst  of Connection
    | CompletedSecond of Connection
    | Read      of nextCn * msg_i
    | DontWrite of Connection

type ioresult_o =
    | WriteError    of option<alertDescription> * string
    | WriteComplete of nextCn
    | MustRead      of Connection

(* Event-driven interface *)

val read     : Connection -> ioresult_i
val write    : Connection -> msg_o -> ioresult_o
val full_shutdown : Connection -> Connection
val half_shutdown : Connection -> unit

val connect : NetworkStream -> config -> Connection
val resume  : NetworkStream -> sessionID -> config -> Connection

val rehandshake : Connection -> config -> bool * nextCn
val rekey       : Connection -> config -> bool * nextCn
val request     : Connection -> config -> bool * nextCn

val accept           : TcpListener   -> config -> Connection
val accept_connected : NetworkStream -> config -> Connection

val authorize: Connection -> query -> ioresult_i
val refuse:    Connection -> query -> unit

val getEpochIn:  Connection -> epoch
val getEpochOut: Connection -> epoch
val getSessionInfo: epoch -> SessionInfo
val getInStream:  Connection -> stream
val getOutStream: Connection -> stream
