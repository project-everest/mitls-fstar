(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Tcp

open Bytes
open Error

type NetworkStream 
type TcpListener 

(* Create a network stream from a given stream.
   Only used by the application interface TLSharp. *)
val create: System.IO.Stream -> NetworkStream

(* Get the underlying stream.
   Only used by the FlexTLS application *)
val getStream: NetworkStream -> System.IO.Stream

(* Server side *)

val listen: string -> int -> TcpListener
val acceptTimeout: int -> TcpListener -> NetworkStream
val accept: TcpListener -> NetworkStream
val stop: TcpListener -> unit

(* Client side *)

val connectTimeout: int -> string -> int -> NetworkStream
val connect: string -> int -> NetworkStream

(* Input/Output *)

val read: NetworkStream -> int -> (string,bytes) optResult
val write: NetworkStream -> bytes -> (string,unit) optResult
val close: NetworkStream -> unit
