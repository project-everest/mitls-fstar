(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module HttpEntryPoint

open System
open System.IO
open System.Net
open HttpServer
open Microsoft.FSharp.Text

let try_read_mimes path =
    try
        Mime.of_file path
    with :? IOException as e ->
        Console.WriteLine("cannot read mime-types: " + e.Message)
        Mime.MimeMap ()

let tlsoptions sessionDBDir dhDBDir serverName clientName = {
    TLSInfo.minVer = TLSConstants.ProtocolVersion.SSL_3p0
    TLSInfo.maxVer = TLSConstants.ProtocolVersion.TLS_1p2

    TLSInfo.ciphersuites =
        TLSConstants.cipherSuites_of_nameList [
            TLSConstants.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384;
            TLSConstants.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256;
            TLSConstants.TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384;
            TLSConstants.TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256;
            TLSConstants.TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA;
            TLSConstants.TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA;
            TLSConstants.TLS_DHE_RSA_WITH_AES_256_GCM_SHA384;
            TLSConstants.TLS_DHE_RSA_WITH_AES_128_GCM_SHA256;
            TLSConstants.TLS_DHE_RSA_WITH_AES_256_CBC_SHA256;
            TLSConstants.TLS_DHE_RSA_WITH_AES_128_CBC_SHA256;
            TLSConstants.TLS_DHE_RSA_WITH_AES_128_CBC_SHA;
            TLSConstants.TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA;
            TLSConstants.TLS_RSA_WITH_AES_256_GCM_SHA384;
            TLSConstants.TLS_RSA_WITH_AES_128_GCM_SHA256;
            TLSConstants.TLS_RSA_WITH_AES_256_CBC_SHA256;
            TLSConstants.TLS_RSA_WITH_AES_256_CBC_SHA;
            TLSConstants.TLS_RSA_WITH_AES_128_CBC_SHA;
            TLSConstants.TLS_RSA_WITH_3DES_EDE_CBC_SHA;
            TLSConstants.TLS_RSA_WITH_RC4_128_SHA;
        ]

    TLSInfo.compressions = [ TLSConstants.NullCompression ]

    TLSInfo.honourHelloReq = TLSInfo.HRPResume
    TLSInfo.allowAnonCipherSuite = false
    TLSInfo.check_client_version_in_pms_for_old_tls = true
    TLSInfo.request_client_certificate = match clientName with | None -> false | Some(_) -> true
    
    TLSInfo.safe_renegotiation = true
    TLSInfo.safe_resumption = false

    TLSInfo.server_name = serverName
    TLSInfo.client_name = match clientName with | None -> "" | Some(name) -> name

    TLSInfo.sessionDBFileName = Path.Combine(sessionDBDir, "sessionDBFile.bin")
    TLSInfo.sessionDBExpiry = Date.newTimeSpan 1 0 0 0 (* one day *)

    TLSInfo.dhDBFileName = Path.Combine(dhDBDir, "dhparams-db.bin")
    TLSInfo.dhDefaultGroupFileName = Path.Combine(dhDBDir, "default-dh.pem")
    TLSInfo.dhPQMinLength = TLSInfo.defaultConfig.dhPQMinLength

    TLSInfo.ecdhGroups =  TLSInfo.defaultConfig.ecdhGroups
}

type options = {
    rootdir   : string;
    certdir   : string;
    dhdir     : string;
    localaddr : IPEndPoint;
    localname : string;
    remotename: string option;
}

exception ArgError of string

let cmdparse = fun () ->
    let assembly = System.Reflection.Assembly.GetExecutingAssembly()
    let mypath   = Path.GetDirectoryName(assembly.Location)
    let myname   = Path.GetFileNameWithoutExtension(assembly.Location)

    let defaultPort = 2443
    let defaultRoot = "htdocs"
    let defaultCert = "sessionDB"
    let defaultDHDB = "DHDB"
    let defaultName = "localhost"
    
    let options  = ref {
        rootdir   = Path.Combine(mypath, defaultRoot);
        certdir   = Path.Combine(mypath, defaultCert);
        dhdir     = Path.Combine(mypath, defaultDHDB);
        localaddr = IPEndPoint(IPAddress.Loopback, defaultPort);
        localname = defaultName;
        remotename= None; }

    let valid_path = fun path ->
        Directory.Exists path

    let o_rootdir = fun s ->
        if not (valid_path s) then
            let msg = sprintf "Invalid path (root directory): %s" s in
                raise (ArgError msg);
        options := { !options with rootdir = s }

    let o_certdir = fun s ->
        if not (valid_path s) then
            let msg = sprintf "Invalid path (certs directory): %s" s in
                raise (ArgError msg);
        options := { !options with certdir = s }

    let o_dhdir = fun s ->
        if not (valid_path s) then
            let msg = sprintf "Invalid path (DHDB directory): %s" s in
                raise (ArgError msg);
        options := { !options with dhdir = s }

    let o_port = fun i ->
        if i <= 0 || i > 65535 then
            raise (ArgError (sprintf "Invalid (bind) port: %d" i));
        let ep = IPEndPoint((!options).localaddr.Address, i) in
            options := { !options with localaddr = ep }

    let o_address = fun s ->
        try
            let ip = IPAddress.Parse s
            let ep = IPEndPoint(ip, (!options).localaddr.Port) in
                options := { !options with localaddr = ep }
        with :?System.FormatException ->
            raise (ArgError (sprintf "Invalid IP Address: %s" s))

    let o_localname = fun s ->
        options := { !options with localname = s }

    let o_remotename = fun s ->
        options := { !options with remotename = Some(s) }

    let specs = [
        "--root-dir"     , ArgType.String o_rootdir   , sprintf "\t\tHTTP root directory (default `pwd`/%s)" defaultRoot
        "--sessionDB-dir", ArgType.String o_certdir   , sprintf "\tsession database directory (default `pwd`/%s)" defaultCert
        "--dhDB-dir"     , ArgType.String o_dhdir     , sprintf "\t\tdh database directory (default `pwd`/%s)" defaultDHDB
        "--bind-port"    , ArgType.Int    o_port      , sprintf "\t\tlocal port (default %d)" defaultPort
        "--bind-address" , ArgType.String o_address   , "\tlocal address (default localhost)"
        "--local-name"   , ArgType.String o_localname , sprintf "\t\tlocal host name (default %s)" defaultName
        "--remote-name"  , ArgType.String o_remotename, "\tremote client name (if any, default anonymous client)"]

    let specs = specs |> List.map (fun (sh, ty, desc) -> ArgInfo(sh, ty, desc))

    try
        ArgParser.Parse (specs, usageText = sprintf "Usage: %s <options>" myname);
        !options

    with ArgError msg ->
        ArgParser.Usage(specs, sprintf "Error: %s\n" msg);
        exit 1

let _ =
    HttpLogger.HttpLogger.Level <- HttpLogger.DEBUG;

    let options    = cmdparse () in
    let tlsoptions = tlsoptions options.certdir options.dhdir options.localname options.remotename in
    let mimesmap   = try_read_mimes (Path.Combine(options.rootdir, "mime.types")) in

        HttpServer.run {
            docroot    = options.rootdir  ;
            mimesmap   = mimesmap         ;
            localaddr  = options.localaddr;
            tlsoptions = Some tlsoptions  ;
            servname   = options.localname;
        }
