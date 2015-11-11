(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module UTLS

// TODO: locking

(* ------------------------------------------------------------------------ *)
open Bytes
open Error
open TLSError
open DataStream
open Dispatch
open TLSInfo
open TLS

(* ------------------------------------------------------------------------ *)
type rawfd   = Tcp.NetworkStream
type fd      = int
type queryhd = int

let EI_BADHANDLE  = -1
let EI_BADCERTIDX = -2
let EI_READERROR  = -3
let EI_CLOSE      = -4
let EI_FATAL      = -5
let EI_WARNING    = -6
let EI_CERTQUERY  = -7
let EI_HANDSHAKEN = -8
let EI_DONTWRITE  = -9
let EI_WRITEERROR = -10
let EI_MUSTREAD   = -11
let EI_HSONGOING  = -12

type handleinfo = {
    conn     : TLS.Connection;
    canwrite : bool;
}

type Phandleinfo = handleinfo

let handleinfo_of_conn (c : Connection) : Phandleinfo =
    { conn = c; canwrite = false; }

type fdmap = list<(fd * Phandleinfo)>

let fds = ref ([] : fdmap)
let fdc = ref 0

(* ------------------------------------------------------------------------ *)
let new_fd (conn : Connection) : fd =
    let fd = !fdc in
        fds := (fd, handleinfo_of_conn conn) :: !fds;
        fdc := !fdc + 1;
        fd

(* ------------------------------------------------------------------------ *)
let rec unbind_fd_r (fd : fd) (fds : fdmap) : fdmap =
    match fds with
    | [] -> []
    | (h, hi) :: fds ->
        let fds = unbind_fd_r fd fds in
            if fd = h then fds else (h, hi) :: fds

let unbind_fd (fd : fd) : unit =
    fds := unbind_fd_r fd !fds

(* ------------------------------------------------------------------------ *)
let rec connection_of_fd_r (fd : fd) (fds : fdmap) : option<Phandleinfo> =
    match fds with
    | [] -> None
    | (h, hd) :: fds ->
        if fd = h then Some hd else connection_of_fd_r fd fds

let connection_of_fd (fd : fd) : option<Phandleinfo> =
    connection_of_fd_r fd !fds

(* ------------------------------------------------------------------------ *)
let rec update_fd_connection_r (fd : fd) (cw : bool) (conn : Connection) (fds : fdmap) : fdmap =
    match fds with
    | [] -> Error.unexpected "[update_fd_connection_r] unbound"
    | (h, hd) :: fds ->
        if fd = h then
            (h, { hd with conn = conn; canwrite = cw }) :: fds
        else
            (h, hd) :: (update_fd_connection_r fd cw conn fds)

let update_fd_connection (fd : fd) (cw : bool) (conn : Connection) : unit =
    fds := update_fd_connection_r fd cw conn !fds

(* ------------------------------------------------------------------------ *)
let canwrite (fd : int) : int =
    match connection_of_fd fd with
    | None    -> EI_BADHANDLE
    | Some hd -> if hd.canwrite then 1 else 0

(* ------------------------------------------------------------------------ *)
let read (fd : int) : int * bytes =
    match connection_of_fd fd with
    | None -> (EI_BADHANDLE, empty_bytes)

    | Some c ->
        match TLS.read c.conn with
        | TLS.ReadError (_, _) ->
            (EI_READERROR, empty_bytes)

        | TLS.Close _ ->
            (unbind_fd fd;
            (EI_CLOSE, empty_bytes))

        | TLS.Fatal e ->
            (unbind_fd fd;
            (EI_FATAL, Alert.alertBytes e))

        | TLS.Warning (conn, e) ->
            let _ = update_fd_connection fd c.canwrite conn in
                (EI_WARNING, Alert.alertBytes e)

        | TLS.CertQuery (conn, q, advice) ->
            let _ = update_fd_connection fd c.canwrite conn in
                (EI_CERTQUERY, empty_bytes)

        | TLS.CompletedFirst conn
        | TLS.CompletedSecond conn ->
            let _ = update_fd_connection fd true conn in
                (EI_HANDSHAKEN, empty_bytes)

        | TLS.Read (conn, (rg, m)) ->
#if verify
            let plain = empty_bytes in
#else
            let plain =
                DataStream.deltaRepr
                    ((Dispatch.getEpochIn conn)) (TLS.getInStream conn) rg m
            in
#endif
                let _ = update_fd_connection fd c.canwrite conn in
                    (Bytes.length plain, plain)

        | TLS.DontWrite conn ->
            let _ = update_fd_connection fd false conn in
                (EI_DONTWRITE, empty_bytes)

(* ------------------------------------------------------------------------ *)
let mkDelta (conn : Connection) (bytes : bytes) : msg_o =
    let e = Dispatch.getEpochOut conn in
    let st = TLS.getOutStream conn  in
    let len = Bytes.length bytes in
    let rg = (len,len) in
    let d = DataStream.createDelta e st rg bytes in
    if len <= fragmentLength then
        (rg,d)
    else
        let (rg0,rg1) = DataStream.splitRange e rg in
        let (d0,d1) = DataStream.split e st rg0 rg1 d in
        (rg0,d0)
        

let write (fd : fd) (bytes : bytes) : int =
    match connection_of_fd fd with
    | None    -> EI_BADHANDLE
    | Some hd ->
        match hd.canwrite with
        | false -> Error.unexpected "[write] cannot write to FD"
        | true  ->
            let msg = mkDelta hd.conn bytes in
                match TLS.write hd.conn msg with
                | TLS.WriteError (_, _) ->
                    unbind_fd fd; EI_WRITEERROR
                | TLS.WriteComplete conn ->
                    let _ = update_fd_connection fd true conn in
                        let ((_,h),_) = msg in
                        h
                | TLS.MustRead conn ->
                    let _ = update_fd_connection fd false conn in
                        EI_MUSTREAD

(* ------------------------------------------------------------------------ *)
let shutdown (fd : fd) : unit =
    match connection_of_fd fd with
    | None -> ()
    | Some hd ->
        let _ = TLS.full_shutdown hd.conn in
            unbind_fd fd

(* ------------------------------------------------------------------------ *)
let connect (rawfd : rawfd) (config : config) : fd =
    let conn = TLS.connect rawfd config in
        new_fd conn

(* ------------------------------------------------------------------------ *)
let accept_connected (rawfd : rawfd) (config :config) : fd =
    let conn = TLS.accept_connected rawfd config in
        new_fd conn
