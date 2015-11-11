(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module TLStream

open Bytes
open Tcp
open Error
open System
open System.IO

type TLSBehavior =
    | TLSClient
    | TLSServer

type TLStream (s:System.IO.Stream, options, b, ?own, ?sessionID, ?certQuery) =
    inherit Stream()

    let own = defaultArg own true
    let certQuery = defaultArg certQuery (fun q advice -> advice)

    let mutable inbuf   : bytes = empty_bytes
    let mutable outbuf  : bytes = empty_bytes
    let mutable closed  : bool  = true
    let mutable disposed: bool = false

    let doMsg_o conn b =
        let ki = TLS.getEpochOut conn
        let s = TLS.getOutStream conn
        let l = length b
        (l,l),DataStream.createDelta (ki) s (l,l) b

    let undoMsg_i conn (r,d) =
        let ki = TLS.getEpochIn conn
        let s = TLS.getInStream conn
        DataStream.deltaRepr (ki) s r d

    let rec doHS conn =
        match TLS.read conn with
        | TLS.ReadError (adOpt,err) ->
            closed <- true
            match adOpt with
            | Some(ad) -> raise (IOException(sprintf "TLS-HS: Sent fatal alert: %A %A" ad err))
            | None     -> raise (IOException(sprintf "TLS-HS: Internal error: %A" err))
        | TLS.Close ns -> closed <- true; raise (IOException(sprintf "TLS-HS: Connection closed during HS"))
        | TLS.Fatal ad -> closed <- true; raise (IOException(sprintf "TLS-HS: Received fatal alert: %A" ad))
        | TLS.Warning (conn,ad) -> closed <- true; raise (IOException(sprintf "TLS-HS: Received warning alert: %A" ad))
        | TLS.CertQuery (conn,q,advice) ->
            if certQuery q advice then
                match TLS.authorize conn q with
                | TLS.ReadError (adOpt,err) ->
                    closed <- true
                    match adOpt with
                    | Some(ad) -> raise (IOException(sprintf "TLS-HS: Sent fatal alert: %A %A" ad err))
                    | None     -> raise (IOException(sprintf "TLS-HS: Internal error: %A" err))
                | TLS.Close ns -> closed <- true; raise (IOException(sprintf "TLS-HS: Connection closed during HS"))
                | TLS.Fatal ad -> closed <- true; raise (IOException(sprintf "TLS-HS: Received fatal alert: %A" ad))
                | TLS.Warning (conn,ad) -> closed <- true; raise (IOException(sprintf "TLS-HS: Received warning alert: %A" ad))
                | TLS.CertQuery (conn,q,advice) -> closed <- true; raise (IOException(sprintf "TLS-HS: Asked to authorize a certificate twice"))
                | TLS.CompletedFirst conn
                | TLS.CompletedSecond conn -> closed <- false; conn
                | TLS.Read (conn,msg) ->
                    let b = undoMsg_i conn msg
                    inbuf <- inbuf @| b
                    doHS conn
                | TLS.DontWrite conn -> doHS conn
            else
                TLS.refuse conn q
                closed <- true
                raise (IOException(sprintf "TLS-HS: Refusing untrusted certificate"))
        | TLS.CompletedFirst conn
        | TLS.CompletedSecond conn -> closed <- false; conn
        | TLS.Read (conn,msg) ->
            let b = undoMsg_i conn msg
            inbuf <- inbuf @| b
            doHS conn
        | TLS.DontWrite conn -> doHS conn

    let rec wrapRead conn =
        match TLS.read conn with
        | TLS.ReadError (adOpt,err) ->
            closed <- true
            match adOpt with
            | None -> raise (IOException(sprintf "TLS-HS: Internal error: %A" err))
            | Some ad -> raise (IOException(sprintf "TLS-HS: Sent fatal alert: %A %A" ad err))
        | TLS.Close ns -> closed <- true; (conn,empty_bytes) // AP: This is a closed connection, should not be used!
        | TLS.Fatal ad -> closed <- true; raise (IOException(sprintf "TLS-HS: Received fatal alert: %A" ad))
        | TLS.Warning (conn,ad) -> closed <- true; raise (IOException(sprintf "TLS-HS: Received warning alert: %A" ad))
        | TLS.CertQuery (conn,q,advice) ->
            if certQuery q advice then
                match TLS.authorize conn q with
                | TLS.ReadError (adOpt,err) ->
                    closed <- true
                    match adOpt with
                    | None -> raise (IOException(sprintf "TLS-HS: Internal error: %A" err))
                    | Some ad -> raise (IOException(sprintf "TLS-HS: Sent fatal alert: %A %A" ad err))
                | TLS.Close ns -> closed <- true; (conn,empty_bytes) // AP: This is a closed connection, should not be used!
                | TLS.Fatal ad -> closed <- true; raise (IOException(sprintf "TLS-HS: Received fatal alert: %A" ad))
                | TLS.Warning (conn,ad) -> closed <- true; raise (IOException(sprintf "TLS-HS: Received warning alert: %A" ad))
                | TLS.CertQuery (conn,q,advice) -> closed <- true; raise (IOException(sprintf "TLS-HS: Asked to authorize a certificate twice"))
                | TLS.CompletedFirst conn
                | TLS.CompletedSecond conn -> closed <- false; wrapRead conn
                | TLS.Read (conn,msg) ->
                    let read = undoMsg_i conn msg in
                    if equalBytes read empty_bytes then
                        // The other party sent some empty fragment. Let's read more.
                        wrapRead conn
                    else
                        (conn,read)
                | TLS.DontWrite conn -> wrapRead conn
            else
                TLS.refuse conn q
                closed <- true
                raise (IOException(sprintf "TLS-HS: Asked to authorize a certificate"))
        | TLS.CompletedFirst conn
        | TLS.CompletedSecond conn -> closed <- false; wrapRead conn
        | TLS.Read (conn,msg) ->
            let read = undoMsg_i conn msg in
            if equalBytes read empty_bytes then
                // The other party sent some empty fragment. Let's read more.
                wrapRead conn
            else
                (conn,read)
        | TLS.DontWrite conn -> wrapRead conn

    let rec wrapWrite conn (rg,d) =
        let rg0,rg1 = DataStream.splitRange (TLS.getEpochOut conn) rg in
        let msg,rem =
            if rg0 = rg then
                (rg,d),None
            else
                let d0,d1 = DataStream.split (TLS.getEpochOut conn) (TLS.getOutStream conn) rg0 rg1 d in
                (rg0,d0),Some(rg1,d1)
        match TLS.write conn msg with
        | TLS.WriteError (adOpt,err) ->
            match adOpt with
            | None -> raise (IOException(sprintf "TLS-HS: Internal error: %A" err))
            | Some ad -> raise (IOException(sprintf "TLS-HS: Sent alert: %A %A" ad err))
        | TLS.WriteComplete conn ->
            match rem with
            | None -> conn
            | Some(msg) -> wrapWrite conn msg
        | TLS.MustRead conn ->
            let conn = doHS conn
            wrapWrite conn msg

    let mutable conn =
        let tcpStream = Tcp.create s
        let conn =
            match b with
            | TLSClient ->
                match sessionID with
                | None -> TLS.connect tcpStream options
                | Some(id) -> TLS.resume tcpStream id options
            | TLSServer -> TLS.accept_connected tcpStream options
        doHS conn

    member self.GetSessionInfo () =
        if disposed then
            raise (ObjectDisposedException("Trying to get SessionInfo on a disposed connection."))
        if closed then
            raise (IOException("Trying to get SessionInfo on a closed connection."))
        (* We could also pick the outgoing epoch.
         * The user can only access an open connection, so epochs
         * are synchronized. *)
        let epoch = TLS.getEpochIn conn in
        TLS.getSessionInfo epoch

    member self.GetSessionInfoString() =
        let si = self.GetSessionInfo() in
        TLSInfo.sinfo_to_string si

    member self.ReHandshake (?config) =
        let config = defaultArg config options
        if closed || disposed then
            raise (ObjectDisposedException("Trying to rehandshake on a closed connection."))
        let res = 
            match b with
            | TLSServer -> TLS.request conn config
            | TLSClient -> TLS.rehandshake conn config
        match res with
            | (false,_) -> raise (IOException("Cannot rehandshake in current protocol state."))
            | (_,c) ->
                conn <- doHS c
                self.GetSessionInfo()

    override this.get_CanRead()     = not closed
    override this.get_CanWrite()    = not closed
    override this.get_CanSeek()     = false
    override this.get_Length()      = raise (NotSupportedException())
    override this.SetLength(i)      = raise (NotSupportedException())
    override this.get_Position()    = raise (NotSupportedException())
    override this.set_Position(i)   = raise (NotSupportedException())
    override this.Seek(i,o)         = raise (NotSupportedException())

    override this.Flush() =
        if disposed then
            raise(ObjectDisposedException("Trying to write to a closed connection."))
        if closed then
            raise(IOException("Trying to write to a closed connection."))
        if not (equalBytes outbuf empty_bytes) then
            let msgO = doMsg_o conn outbuf
            conn <- wrapWrite conn msgO
            outbuf <- empty_bytes

    override this.Read(buffer, offset, count) =
        if disposed then
            raise(ObjectDisposedException("Trying to read from a closed connection."))
        else
            if closed then
                0
            else
                let data =
                    if equalBytes inbuf empty_bytes then
                        (* Read from the socket, and possibly buffer some data *)
                        let (c,data) = wrapRead conn
                        // FIXME: if data is empty_bytes we should set conn to "null" (which we cannot)
                        conn <- c
                        data
                    else (* Use the buffer *)
                        let tmp = inbuf in
                        inbuf <- empty_bytes
                        tmp
                let l = length data in
                if l <= count then
                    Array.blit (cbytes data) 0 buffer offset l
                    l
                else
                    let (recv,newBuf) = split data count in
                    Array.blit (cbytes recv) 0 buffer offset count
                    inbuf <- newBuf
                    count

    override this.Write(buffer,offset,count) =
        if disposed then
            raise(ObjectDisposedException("Trying to write to a closed connection."));
        if closed then
            raise(IOException("Trying to write to a closed connection."))
        let data = Array.create count (byte 0) in
        Array.blit buffer offset data 0 count
        let b = abytes data in
        outbuf <- b
        this.Flush ()

    override this.Close() =
        if not closed then
            this.Flush()
            TLS.half_shutdown conn
            closed <- true
        if own then
            s.Close()
        disposed <- true
