open Bytes
open Error

type networkStream 
type tcpListener 

(* Create a network stream from a given stream.
   Only used by the application interface TLSharp. *)
(* val create: System.IO.Stream -> networkStream*)

(* Server side *)

val listen: string -> int -> tcpListener
val acceptTimeout: int -> tcpListener -> networkStream
val accept: tcpListener -> networkStream
val stop: tcpListener -> unit

(* Client side *)

val connectTimeout: int -> string -> int -> networkStream
val connect: string -> int -> networkStream

(* Input/Output *)

val read: networkStream -> int -> (string,bytes) optResult
val write: networkStream -> bytes -> (string,unit) optResult
val close: networkStream -> unit
