(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

(* -------------------------------------------------------------------- *)
type auth =
| ANone
| ACert of string

(* -------------------------------------------------------------------- *)
module Auth
    val ...

(* -------------------------------------------------------------------- *)
module Client
    type channel
    type document

    predicate Honest  of string
    predicate Secure  of channel
    predicate Client  of channel * auth
    predicate Request of channel * string
    predicate Respone of channel * request * document
    
    val create  : h:string -> (;h) channel
    val request : h:string -> c:((;h) channel) -> a:auth{Client(c, a)} -> r:string{Request(c, r)} -> unit
    val poll    : h:string -> c:((;h) channel) -> (r:request * d:document{Request(c, r) /\ Honest(h) => Response(c, r, d)}) option

(* -------------------------------------------------------------------- *)
module Server
   type channel
   type request

   (* Regarding the log, the client will assume ack. of the
    * response. We could thread the channel state instead *)

   val accept : h:string -> (c:((;h) channel) * r:request{Secure(c) => Request(c, r)} * log:((r':request * d':document){Secure(c) => Ack(c, r', d')}) list) option
   val auth   : h:string -> (;h) channel -> (a:auth{Honest(a) => Client(c, a) /\ Honest(h) => Secure(c)}) option
   val send   : h:string -> (;h) channel -> r:request{Secure(c) => Request(c, r)} -> d:document{Response(c, r, d)} -> unit
