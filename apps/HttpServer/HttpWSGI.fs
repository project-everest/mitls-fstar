(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module HttpWSGI

open System
open System.IO
open Microsoft.FSharp.Reflection
open Python.Runtime
open HttpData

// ------------------------------------------------------------------------
type WsgiEngineLock () =
    let gil = PythonEngine.AcquireLock ()

    interface IDisposable with
        member this.Dispose () =
            PythonEngine.ReleaseLock gil

// ------------------------------------------------------------------------
type WsgiEngine () =
    static let mutable tid = (nativeint) 0

    static member initialize () =
        lock typeof<Python.Runtime.Runtime> (fun () ->
            if tid <> (nativeint) 0 then
                failwith "WsgiHandler already initialized";
            if PythonEngine.IsInitialized then
                failwith "PythonEngine already initialized";
            PythonEngine.Initialize ();
            try
                tid <- PythonEngine.BeginAllowThreads ()
            with e ->
                PythonEngine.Shutdown ();
                raise e)

    static member finalize () =
        lock typeof<Python.Runtime.Runtime> (fun () ->
            try
                if tid <> (nativeint) 0 then
                    PythonEngine.EndAllowThreads tid;
                    PythonEngine.Shutdown ()
            finally
                tid <- (nativeint) 0)

// ------------------------------------------------------------------------
// We currently only support one WSGI application per server
type WsgiHandler () =
    static let mutable application = null

    do
        WsgiEngine.initialize ()
        use lock   = new WsgiEngineLock () in
        use appmod = PythonEngine.ImportModule ("wsgiapp") in
            application <- appmod.GetAttr("main").Invoke([||])

    (* ------------------------------------------------------------------------ *)
    static let cs_map = Map.ofArray (Utils.enumeration<TLSConstants.cipherSuiteName> ())
    static let vr_map = Map.ofArray (Utils.enumeration<TLSConstants.ProtocolVersion> ())
    static let cp_map = Map.ofArray (Utils.enumeration<TLSConstants.Compression>     ())

    interface IDisposable with
        member self.Dispose () =
            application <- null
            WsgiEngine.finalize ()

    static member entry (config : HttpServerConfig) (request : HttpRequest) (stream : Stream) =
        assert PythonEngine.IsInitialized

        use lock   = new WsgiEngineLock () in
        use bridge = PythonEngine.ImportModule ("wsgibridge") in
        let error  = System.Console.Error in
        let url    = sprintf "https://%s/%s" config.servname request.path in

        let sinfo =
            try
                let sinfo = (stream :?> TLStream.TLStream) in
                let sinfo = sinfo.GetSessionInfo () in
                let sinfo =
                    [ ("cipher"      , Map.find (Utils.unerror (TLSConstants.name_of_cipherSuite sinfo.cipher_suite)) cs_map :> obj);
                      ("compression" , Map.find sinfo.compression cp_map :> obj);
                      ("version"     , Map.find sinfo.protocol_version vr_map :> obj);
                      ("session-hash", Bytes.hexString sinfo.session_hash :> obj);
                      ("session-extensions", Printf.sprintf "%A" sinfo.extensions :> obj);
                    ]
                        |> Map.ofList
                in
                    sinfo
            with :? InvalidCastException -> Map.empty
        in

        let config =
            [ ("url"    , url     :> obj);
              ("request", request :> obj);
              ("error"  , error   :> obj);
              ("input"  , stream  :> obj);
              ("output" , stream  :> obj);
              ("sinfo"  , sinfo   :> obj);
            ]
                |> Map.ofList
                |> PyObject.FromManagedObject
        in

        ignore (bridge.GetAttr("_entry").Invoke([|config; application|]))
