(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module RPC

open Bytes
open TLSInfo
open Error
open TLSError
open Range
open Dispatch
open TLS

let msglen = 128

let padmsg = fun r ->
    if Bytes.length r > msglen then
        fst (Bytes.split r msglen)
    else
        r @| (Bytes.createBytes (msglen - (Bytes.length r)) 0)

let request_bytes  nonce r = nonce @| (padmsg r)
let response_bytes nonce r = nonce @| (padmsg r)

let service = fun r -> r

type DrainResult =
| DRError    of option<alertDescription> * string
| DRClosed   of Tcp.NetworkStream
| DRContinue of Connection

let rec drainMeta = fun conn ->
  match TLS.read conn with
  | ReadError  (ad,err)          -> DRError (ad,err)
  | Close      s                 -> DRClosed s
  | Fatal      e                 -> DRError (Some(e),"")
  | Warning    (conn, _)         -> DRContinue conn
  | CertQuery  (conn, q, advice) ->
    if advice then
        match authorize conn q with
        |ReadError(ad,err) -> DRError(ad,err)
        | Close(s) -> DRClosed(s)
        | Fatal(e) -> DRError(Some(e),"")
        | Warning(conn,_) -> DRContinue conn
        | CompletedFirst  (conn)
        | CompletedSecond (conn) -> DRContinue conn
        | DontWrite conn -> drainMeta conn
        | _ -> DRError(None,perror __SOURCE_FILE__ __LINE__ "Internal TLS error")
    else
        (refuse conn q; DRError(None,""))
  | CompletedFirst conn
  | CompletedSecond conn         -> DRContinue conn
  | DontWrite  conn              -> drainMeta conn
  | Read       (conn, _)         ->
        (ignore (TLS.full_shutdown conn);
        DRError (None,perror __SOURCE_FILE__ __LINE__ "Internal TLS error"))

let rec sendMsg = fun conn rg msg ->
    let rg0,rg1 = DataStream.splitRange (TLS.getEpochOut conn) rg in
    let msg_o,rem =
        if rg0 = rg then
            msg,None
        else
            let msg0,msg1 = DataStream.split (TLS.getEpochOut conn) (TLS.getOutStream conn) rg0 rg1 msg in
            msg0, Some(msg1)
    in
    match TLS.write conn (rg0, msg_o) with
    | WriteError    (ad,err)          -> None
    | WriteComplete conn              ->
        (match rem with
        | None -> Some conn
        | Some(msg1) -> sendMsg conn rg1 msg1)
    | MustRead      conn              ->
        (match drainMeta conn with
        | DRError    _    -> None
        | DRClosed   _    -> None
        | DRContinue conn -> sendMsg conn rg msg)

let recvMsg = fun conn ->
    let rec doit = fun conn buffer ->
        match TLS.read conn with
          | ReadError  _                 -> None
          | Close      _                 -> None
          | Fatal      _                 -> None
          | Warning    (conn, _)         -> doit conn buffer
          | CertQuery  (conn, q, advice) ->
            if advice then
                match authorize conn q with
                | Warning (conn,_)
                | CompletedFirst conn
                | CompletedSecond conn
                | DontWrite conn   -> doit conn buffer
                | _ -> None
            else
                (refuse conn q; None)
          | CompletedFirst conn
          | CompletedSecond conn         -> doit conn buffer
          | DontWrite  conn              -> doit conn buffer
          | Read       (conn, (r, d))    ->
                let ki     = Dispatch.getEpochIn  conn in
                let s      = TLS.getInStream conn in
                let buffer = buffer @| (DataStream.deltaRepr ki s r d) in

                if Bytes.length buffer < 2+msglen then
                    doit conn buffer
                else if Bytes.length buffer > 2+msglen then
                    (ignore (TLS.full_shutdown conn); None)
                else
                    Some (conn, buffer)
                    
    in
        doit conn empty_bytes

let doclient (request : string) =
    let ns      = Tcp.connect "127.0.0.1" 5000 in
    let conn    = TLS.connect ns defaultConfig in

    match drainMeta conn with
    | DRError  _ -> None
    | DRClosed _ -> None

    | DRContinue conn ->
        let nonce   = Nonce.random 2 in
        let request = request_bytes nonce (Bytes.utf8 request) in

        let msg =
            DataStream.createDelta
                ((Dispatch.getEpochOut conn)) (TLS.getOutStream conn)
                (Bytes.length request, Bytes.length request) request in

        match sendMsg conn (Bytes.length request, Bytes.length request) msg with
        | Some conn ->
            (match recvMsg conn with
            | None -> None
            | Some (conn, response) ->
                ignore (TLS.full_shutdown conn);

                if Bytes.length response <> 2+msglen then
                    None
                else
                    let rnonce, response = Bytes.split response 2 in
                    if Bytes.equalBytes nonce rnonce then
                        Some (Bytes.iutf8 response)
                    else
                        None)
        | None -> None

let doserver () =
    let ns = Tcp.listen "127.0.0.1" 5000 in

    let rec doclient = fun () ->
        let client = Tcp.accept ns in

        let result =
            let conn = TLS.accept_connected client defaultConfig in

            match drainMeta conn with
            | DRError  _ -> false
            | DRClosed _ -> false
            | DRContinue conn ->
                match recvMsg conn with
                | None -> false
                | Some (conn, request) ->
                    if Bytes.length request < 2 then
                        false
                    else
                        let nonce, request = Bytes.split request 2 in
                        let response = service (Bytes.iutf8 request) in
                        let response = response_bytes nonce (Bytes.utf8 response) in

                        let msg =
                            DataStream.createDelta
                                ((Dispatch.getEpochOut conn)) (TLS.getOutStream conn)
                                (Bytes.length response, Bytes.length response) response in

                        match sendMsg conn (Bytes.length response, Bytes.length response) msg with
                        | Some conn -> ignore (TLS.full_shutdown conn); true
                        | None -> false
        in
            Tcp.close client; result
    in
        doclient ()
