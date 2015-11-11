(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module TLS

open Bytes
open Error
open TLSError
open TLSInfo
open Tcp
open Dispatch

type Connection = Dispatch.Connection
type nextCn = Connection

// Outcomes for top-level functions
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

let connect ns po = Dispatch.init ns Client po
let resume ns sid po = Dispatch.resume ns sid po

let rehandshake c po = Dispatch.rehandshake c po
let rekey c po = Dispatch.rekey c po

let accept lt po =
    let ns = Tcp.accept lt in
    Dispatch.init ns Server po
let accept_connected ns po = Dispatch.init ns Server po

let request c po = Dispatch.request c po


let read ca = 
  let cb,outcome = Dispatch.read ca in 
    match outcome with
      | RError(err) -> 
          ReadError(None,err)
      | WriteOutcome(WError(err)) -> ReadError(None,err)
      | RAppDataDone(b) -> Read(cb,b)
      | RQuery(q,adv) -> CertQuery(cb,q,adv)
      | RHSDone -> CompletedFirst(cb)
      | RClose -> Close (networkStream cb)
      | RFatal(ad) -> Fatal(ad)
      | RWarning(ad) -> Warning(cb,ad)
      | WriteOutcome(WriteFinished) -> DontWrite(cb)
      | WriteOutcome(WHSDone) -> CompletedSecond(cb)
      | WriteOutcome(SentFatal(ad,s)) -> ReadError(Some(ad),s)
      | WriteOutcome(SentClose) -> Close (networkStream cb)
      | WriteOutcome(WriteAgain) -> unexpected "[read] Dispatch.read should never return WriteAgain"
      | _ -> ReadError(None, perror __SOURCE_FILE__ __LINE__ "Invalid dispatcher state. This is probably a bug, please report it")

let write c msg =
    let c,outcome = Dispatch.write c msg in
    match outcome with
      | WError(err) -> WriteError(None,err)
      | WAppDataDone -> WriteComplete c
      | WDone ->
          (* We are in the open state, and providing some data to be sent, so only WAppDataDone can apply here *)
          WriteError(None, perror __SOURCE_FILE__ __LINE__ "Invalid dispatcher state. This is probably a bug, please report it")
      | WHSDone ->
          (* A top-level write should never lead to HS completion.
             Currently, we report this as an internal error.
             Being more precise about the Dispatch state machine, we should be
             able to prove that this case should never happen, and so use the
             unexpected function. *)
          WriteError(None, perror __SOURCE_FILE__ __LINE__ "Invalid dispatcher state. This is probably a bug, please report it")
      | WriteFinished ->
          MustRead(c)
      | SentClose ->
          (* A top-level write can never send a closure alert on its own.
             Either the user asks for half_shutdown, and the connection is consumed,
             or it asks for full_shutdown, and then it cannot write anymore *)
          WriteError(None, perror __SOURCE_FILE__ __LINE__ "Invalid dispatcher state. This is probably a bug, please report it")
      | SentFatal(ad,err) ->
          WriteError(Some(ad),err)
      | WriteAgain | WriteAgainFinishing | WriteAgainClosing ->
          unexpected "[write] writeAll should never ask to write again"



let full_shutdown c = Dispatch.full_shutdown c
let half_shutdown c = Dispatch.half_shutdown c

let authorize c q =
    let cb,outcome = Dispatch.authorize c q in
    match outcome with
      | WriteOutcome(WError(err)) -> ReadError(None,err)
      | RError(err) -> ReadError(None,err)
      | RHSDone -> CompletedFirst(cb)
      | RClose -> Close (networkStream cb)
      | RFatal(ad) -> Fatal(ad)
      | RWarning(ad) -> Warning(cb,ad)
      | WriteOutcome(WriteFinished) -> DontWrite(cb)
      | WriteOutcome(WHSDone) -> CompletedSecond(cb)
      | WriteOutcome(SentFatal(ad,s)) -> ReadError(Some(ad),s)
      | WriteOutcome(SentClose) -> Close (networkStream cb)
      | WriteOutcome(WriteAgain) -> unexpected "[read] Dispatch.read should never return WriteAgain"
      | _ -> ReadError(None, perror __SOURCE_FILE__ __LINE__ "Invalid dispatcher state. This is probably a bug, please report it")

let refuse c q = Dispatch.refuse c q

let getEpochIn c = Dispatch.getEpochIn c
let getEpochOut c = Dispatch.getEpochOut c
let getSessionInfo ki = epochSI(ki)
let getInStream  c = Dispatch.getInStream c
let getOutStream c = Dispatch.getOutStream c
