(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module EchoTest

open System
open System.IO
open System.Net
open System.Text

open Microsoft.FSharp.Text
open Microsoft.FSharp.Reflection

(* ------------------------------------------------------------------------ *)
exception NotAValidEnumeration

let enumeration<'T> () =
    let t = typeof<'T>

    if not (FSharpType.IsUnion(t)) then
        raise NotAValidEnumeration;

    let cases = FSharpType.GetUnionCases(t)

    if not (Array.forall
                (fun (c : UnionCaseInfo) -> c.GetFields().Length = 0)
                (FSharpType.GetUnionCases(t))) then
        raise NotAValidEnumeration;

    let cases =
        Array.map
            (fun (c : UnionCaseInfo) ->
                (c.Name, FSharpValue.MakeUnion(c, [||]) :?> 'T))
            cases
    in
        cases

(* ------------------------------------------------------------------------ *)
let cs_map = enumeration<TLSConstants.cipherSuiteName> ()
let vr_map = enumeration<TLSConstants.ProtocolVersion> ()

(* ------------------------------------------------------------------------ *)
let parse_cipher  = let map = Map.ofArray cs_map in fun x -> map.TryFind x
let parse_version = let map = Map.ofArray vr_map in fun x -> map.TryFind x

(* ------------------------------------------------------------------------ *)
exception ArgError of string

let parse_cmd () =
    let assembly = System.Reflection.Assembly.GetExecutingAssembly()
    let mypath   = Path.GetDirectoryName(assembly.Location)
    let myname   = Path.GetFileNameWithoutExtension(assembly.Location)
    let defaultCS = [
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
    let defaultMinVer  = TLSConstants.SSL_3p0
    let defaultMaxVer  = TLSConstants.TLS_1p2
    let defaultSN   = "localhost"
    let defaultCN   = None
    let defaultPort = 443
    let defaultDB   = "sessionDB"
    let defaultDH   = "DHDB"
    
    let options : EchoImpl.options ref = ref {
        ciphersuite   = defaultCS;
        tlsminversion = defaultMinVer;
        tlsmaxversion = defaultMaxVer;
        servername    = defaultSN;
        clientname    = defaultCN;
        localaddr     = IPEndPoint(IPAddress.Loopback, defaultPort);
        sessiondir    = Path.Combine(mypath, defaultDB);
        dhdir         = Path.Combine(mypath, defaultDH);
        insecure      = false }

    let isclient = ref false

    let valid_path = fun path ->
        Directory.Exists path

    let o_certdir = fun s ->
        if not (valid_path s) then
            let msg = sprintf "Invalid path (certs directory): %s" s in
                raise (ArgError msg);
        options := { !options with sessiondir = s }

    let o_dhdir = fun s ->
        if not (valid_path s) then
            let msg = sprintf "Invalid path (dh directory): %s" s in
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

    let o_ciphers (ciphers : string) =
        let ciphers =
            let parse cipher =
                match parse_cipher cipher with
                | None        -> raise (ArgError (sprintf "invalid cipher-suite: `%s'" cipher))
                | Some cipher -> cipher
            in
                match ciphers.Split(',') with
                | a when a.Length = 0 -> raise (ArgError "empty ciphers list")
                | a -> Array.toList (Array.map parse (ciphers.Split(':')))
        in
            options := { !options with ciphersuite = ciphers }
    
    let o_version (version : string) =
        match parse_version version with
        | None -> raise (ArgError (sprintf "invalid TLS version: `%s'" version))
        | Some version -> options := { !options with tlsmaxversion = version; tlsminversion = version }

    let o_client_name (name : string) =
        options := { !options with clientname = Some name }

    let o_server_name (name : string) =
        options := { !options with servername = name }

    let o_insecure () =
        options := { !options with insecure = true}

    let o_list () =
        let all = [ ("ciphers"     , Array.toList (Array.map (fun (k, _) -> k) cs_map));
                    ("TLS versions", Array.toList (Array.map (fun (k, _) -> k) vr_map)); ]
        in
            List.iter
                (fun (head, values) ->
                    printfn "Supported %s:" head
                    List.iter (fun x -> printfn "  %s" x) values
                    printfn "")
                all;
            exit 2

    let specs =
        let specs = [
            "--sessionDB-dir", ArgType.String o_certdir    , sprintf "\tsession database directory (default: `pwd`/%s)" defaultDB
            "--dhDB-dir"     , ArgType.String o_dhdir      , sprintf "\t\tdh database directory (default: `pwd`/%s)" defaultDH
            "--port"         , ArgType.Int    o_port       , sprintf "\t\t\tserver port (default: %d)" defaultPort
            "--address"      , ArgType.String o_address    , "\t\tserver address (default: localhost)"
            "--ciphers"      , ArgType.String o_ciphers    , sprintf "\t\t,-separated ciphers list (default: %s)" (String.Join(",", List.map (sprintf "%A") defaultCS))
            "--tlsversion"   , ArgType.String o_version    , sprintf "\t\tTLS version to use -- strict (default: any supported version)"
            "--client-name"  , ArgType.String o_client_name, "\tTLS client name (default: None, anonymous client)"
            "--server-name"  , ArgType.String o_server_name, (sprintf "\tTLS server name (default: %s)" defaultSN)
            "--list"         , ArgType.Unit   o_list       , "\t\t\tPrint supported versions/ciphers and exit"
            "--client"       , ArgType.Set    isclient     , "\t\t\tAct as a client instead of a server"
            "--insecure"     , ArgType.Unit   o_insecure   , "\t\t\tDo not check peer's certificate"]
        in
            specs |> List.map (fun (sh, ty, desc) -> ArgInfo(sh, ty, desc))

    in
        try
            ArgParser.Parse(specs, usageText = sprintf "Usage: %s <options>" myname);
            (!options, !isclient)

        with ArgError msg ->
            ArgParser.Usage(specs, sprintf "Error: %s\n" msg);
            exit 1

(* ------------------------------------------------------------------------ *)
let _ =
    let options, isclient = parse_cmd () in
    match isclient with
    | true  -> EchoImpl.client options
    | false -> EchoImpl.server options

