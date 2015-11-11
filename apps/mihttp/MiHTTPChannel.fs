(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module MiHTTPChannel

open Bytes
open TLSConstants
open TLSInfo
open TLS

open MiHTTPData
open MiHTTPCookie

type channelid = bytes

type cstate = {
    c_channelid   : cbytes;
    c_hostname    : string;
    c_credentials : string option;
}

type hostname = string

type request = {
    uri : string;
}

type status = {
    done_       : (request * cdocument) list;
    credentials : string option;
    cookies     : cookie list;
}

type channel_infos = {
    channelid : bytes;
    hostname  : hostname;
}

type channel = {
    channel : channel_infos * status ref;
    lock    : MiHTTPWorker.lock;
}

type rchannel = channel

type auth =
| ACert of string

let initial_status =
    { done_ = []; credentials = None; cookies = []; }

let create_config sname cname = {
    minVer = TLS_1p0;
    maxVer = TLS_1p2;
    ciphersuites = cipherSuites_of_nameList
     [
        TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384; TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256; TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA;
        TLS_DHE_RSA_WITH_AES_256_GCM_SHA384; TLS_DHE_RSA_WITH_AES_128_GCM_SHA256; TLS_DHE_DSS_WITH_AES_256_CBC_SHA;
        TLS_RSA_WITH_AES_256_GCM_SHA384; TLS_RSA_WITH_AES_128_GCM_SHA256; TLS_RSA_WITH_AES_256_CBC_SHA;
     ];
    compressions = [ NullCompression ];

    honourHelloReq = HRPFull;
    allowAnonCipherSuite = true;
    request_client_certificate = false; (* ignored *)
    check_client_version_in_pms_for_old_tls = false; (* ignored *)

    safe_renegotiation = true;
    safe_resumption = false;
    server_name = sname;
    client_name = cname;

    sessionDBFileName = "session-db.db";
    sessionDBExpiry   = Date.newTimeSpan 1 0 0 0 (* one day *);

    TLSInfo.dhDBFileName = "dhparams-db.bin";
    dhDefaultGroupFileName = "defaultDH.pem";
    dhPQMinLength = TLSInfo.defaultConfig.dhPQMinLength;
    ecdhGroups = TLSInfo.defaultConfig.ecdhGroups;
}

let create_with_id (cid : channelid) (host : hostname) : channel =
    let lock  = MiHTTPWorker.create_lock () in
    let infos = { channelid = cid; hostname = host; } in
    let is = ref initial_status in
    { channel = (infos, is);
      lock    = lock; }

let create (host : string) =
    let cid = Nonce.random 16 in
    create_with_id cid host

let save_channel (c : channel) : cstate =
    let (infos, status) = c.channel in
    { c_channelid   = cbytes infos.channelid;
      c_hostname    = infos.hostname;
      c_credentials = (!status).credentials; }

let restore_channel (s : cstate) : channel =
    let conn = create_with_id (abytes s.c_channelid) s.c_hostname in
    (*conn.status := { !conn.status with credentials = s.credentials; }*)
    conn

let connect (h : hostname) =
    create h

let cinfos (c : channel) =
    let (infos, _) = c.channel in
        infos

let rec wait_handshake (c : TLS.Connection) : TLS.Connection =
    match TLS.read c with
    | ReadError (_, _)    -> Error.unexpected "read error"
    | Close _             -> Error.unexpected "connection closed"
    | Fatal _             -> Error.unexpected "fatal alert"
    | Warning (c, _)      -> wait_handshake c
    | CertQuery (c, q, b) ->
        match TLS.authorize c q with
        | ReadError (_, _)    -> Error.unexpected "read error"
        | Close _             -> Error.unexpected "connection closed"
        | Fatal _             -> Error.unexpected "fatal alert"
        | Warning (c, _)      -> wait_handshake c
        | CertQuery (_, _, _) -> Error.unexpected "cert. query"
        | CompletedFirst c
        | CompletedSecond c   -> c
        | Read (_, _)         -> Error.unexpected "app. data"
        | DontWrite c         -> wait_handshake c
    | CompletedFirst c
    | CompletedSecond c -> c
    | Read (_, _)  -> Error.unexpected "app. data"
    | DontWrite c  -> wait_handshake c

let rec full_write (conn : TLS.Connection) (rg,d) : TLS.Connection =
    let e = TLS.getEpochOut conn in
    let rg0,rg1 = DataStream.splitRange e rg in
    if rg0 = rg then
        match TLS.write conn (rg,d) with
        | WriteError (_, _)     -> Error.unexpected "write error"
        | WriteComplete c       -> c
        | MustRead _            -> Error.unexpected "must-read"
    else
        let st = TLS.getOutStream conn in
        let d0,d1 = DataStream.split e st rg0 rg1 d in
        match TLS.write conn (rg0,d0) with
        | WriteError (_, _)     -> Error.unexpected "write error"
        | WriteComplete c       -> full_write c (rg1,d1)
        | MustRead _            -> Error.unexpected "must-read"

let rec full_read conn d =
    match TLS.read conn with
    | ReadError (_, _)    -> Error.unexpected "read error"
    | Close _             -> (conn, MiHTTPData.finalize d)
    | Fatal _             -> Error.unexpected "fatal alert"
    | Warning (c, _)      -> full_read c d
    | CertQuery (_, _, _) -> Error.unexpected "cert. query"
    | CompletedFirst c
    | CompletedSecond c   -> Error.unexpected "complete"
    | DontWrite c         -> full_read c d
    | Read (c, (rg, x))   ->
        let epoch  = TLS.getEpochIn  conn in
        let stream = TLS.getInStream conn in
        let d = MiHTTPData.push_delta epoch stream rg x d in    
            full_read c d

let upgrade_credentials (c : channel) (a : auth option) : status =
    let (_, status) = c.channel in

    match a with
    | None -> !status
    | Some (ACert cn) ->
        match (!status).credentials with
        | None ->
            status := { !status with credentials = Some cn; }
            !status
        | Some cn' ->
            if cn <> cn' then Error.unexpected "inconsistent creds";
            !status

let request_of_string (conn : Connection) (r : request) =
    let epoch  = TLS.getEpochOut conn in
    let stream = TLS.getOutStream conn in
    let range  = (0, 1024) in
    (range, MiHTTPData.request epoch stream range r.uri) in

let get_cn_of_credentials (creds : string option) =
    match creds with
    | None    -> ""
    | Some cn -> cn

let add_cdocument_to_channel (c : channel) (r : request) (d : cdocument) =
    let (_, status) = c.channel in
        status := { !status with done_ = (r, d) :: (!status).done_; }

let dorequest (c : channel) (a : auth option) (r : request) : unit =
    let (infos, _) = c.channel in

#if verify
    let status = upgrade_credentials c a
#else
    let status = MiHTTPWorker.critical c.lock (fun () -> upgrade_credentials c a) () in
#endif
    let cname    = get_cn_of_credentials status.credentials in
    let config   = create_config infos.hostname cname in
    let conn     = Tcp.connect infos.hostname 443 in
    let conn     = TLS.connect conn config in
    let document = MiHTTPData.create () in
    let conn     = wait_handshake conn in
    let request  = request_of_string conn r in
    let conn     = full_write conn request in
    let conn, d  = full_read conn (MiHTTPData.create ()) in

    match d with
    | None   -> ()
    | Some d ->
#if verify
            add_cdocument_to_channel c r d
#else
            MiHTTPWorker.critical c.lock
                (fun () -> add_cdocument_to_channel c r d) ()
#endif

let request (c : channel) (a : auth option) (r : string) =
    let r = { uri = r; } in
#if verify
    dorequest c a r
#else
    let f = (fun () -> dorequest c a r) in
    MiHTTPWorker.async f ()
#endif

let dopoll (c : channel) =
    let (_, status) = c.channel in

    match (!status).done_ with
    | [] -> None
    | d :: ds -> status := { !status with done_ = ds }; Some d

let poll (c : channel) =
#if verify
    dopoll c
#else
    MiHTTPWorker.critical c.lock dopoll c
#endif
