(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

(* -------------------------------------------------------------------- *)
type cn = string

type auth =
| ACert of cn

type (;cn) channel                    (* indexed by server hostname *)

(* -------------------------------------------------------------------- *)
module Payload
    type (;range) url
    type (;channel) request = (rg:range * (; rg) url)

    type body (;range) body
    type (;channel, request) document = (rg:range * (;rg) body)

    type (;channel, request, document) ack
    type log = c:channel * r:(;c) request * d:(;c, r)document * (;c, r, d) ack

    val request  : h:string -> c:(;h) channel -> rg:range -> string -> (;c) request
    val document : h:string -> c:(;h) channel -> r:(;c) request -> rg:range -> string -> (;c, r) document
    val ack      : h:string -> c:(;h) channel -> r:(;c) request -> d:(;c, r) document -> log

(* -------------------------------------------------------------------- *)
predicate HonestHost   of cn        (* No compromised certificates  *)
predicate HonestClient of auth      (* No compromised certificates *)
predicate Secure       of channel   (* Channel between two compliant instances *)
predicate Client       of channel * auth (* Client endorses the channel *)

(* -------------------------------------------------------------------- *)
module Auth
    val honest  : cn -> bytes
    val corrupt : cn -> bytes -> bytes

(* -------------------------------------------------------------------- *)
module Client
    type document
    
    val create  : h:cn -> (;h) channel

    val request : h:cn -> c:((;h) channel) -> (a:auth{Client(c, a)}) option -> r:(;c) request -> unit

    val poll    : h:cn -> c:((;h) channel) -> (r:(;c) request * (;c, r) document) option

(* -------------------------------------------------------------------- *)
module Server
   (* Regarding the log, the client will assume ack. of the
    * response. We could thread the channel state instead *)

   val accept : h:cn -> (c:((;h) channel) * r:(;c) request * log:(log list))

   val auth   : h:cn -> (;h) channel -> (a:auth{HonestClient(a) => Client(c, a) /\ HonestHost(h) => Secure(c)}) option

   val send   : h:cn -> (;h) channel -> r:(;c) request -> d:(;c, r)document -> unit
