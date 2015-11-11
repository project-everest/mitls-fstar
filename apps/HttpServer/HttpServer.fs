(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module HttpServer

open System
open System.IO
open System.Net
open System.Net.Sockets
open System.Text
open System.Text.RegularExpressions
open System.Threading

open HttpHeaders
open HttpStreamReader
open HttpData
open HttpLogger
open Utils

#if wsgi
open HttpWSGI
#endif

open TLStream

exception HttpResponseExn of HttpResponse

let HttpResponseExnWithCode = fun code ->
    HttpResponseExn (http_response_of_code code)

type HttpClientHandler (server : HttpServer, peer : TcpClient) =
    let mutable rawstream : NetworkStream    = null
    let mutable stream    : Stream           = null
    let mutable reader    : HttpStreamReader = Unchecked.defaultof<HttpStreamReader>

    let mutable handlers = []

    interface IDisposable with
        member self.Dispose () =
            if stream <> null then
                noexn (fun () -> rawstream.Dispose ());
            if rawstream <> null then
                noexn (fun () -> rawstream.Dispose ());

            rawstream <- null
            stream    <- null
            reader    <- Unchecked.defaultof<HttpStreamReader>

            noexn (fun () -> peer.Close ())

    member private self.SendLine line =
        let bytes = Encoding.ASCII.GetBytes(sprintf "%s\r\n" line) in
            HttpLogger.Debug ("--> " + line);
            stream.Write(bytes, 0, bytes.Length)

    member private self.SendStatus version code =
        self.SendLine
            (sprintf "HTTP/%s %d %s"
                (string_of_httpversion version)
                (HttpCode.code code)
                (HttpCode.http_status code))

    member private self.SendHeaders (headers : seq<string * string>) =
        headers |>
            Seq.iter(fun (h, v) -> self.SendLine (sprintf "%s: %s" h v))

    member private self.SendResponseWithBody version code headers (body : byte[]) =
        self.SendStatus  version code;
        self.SendHeaders headers;
        self.SendLine    "";

        if body.Length <> 0 then
            stream.Write(body, 0, body.Length)

    member private self.SendResponse version code =
        self.SendResponseWithBody
            version code [("Content-Type", "text/plain"); ("Connection", "close")] 
            (Encoding.ASCII.GetBytes((HttpCode.http_message code) + "\r\n"))

    member private self.ResponseOfStream (fi : FileInfo) (stream : Stream) =
        let ctype =
            match server.Config.mimesmap.Lookup(Path.GetExtension(fi.FullName)) with
            | Some ctype -> ctype
            | None -> "text/plain"
        in
            { code    = HttpCode.HTTP_200;
              headers = HttpHeaders.OfList [(HttpHeaders.CONTENT_TYPE, ctype)];
              body    = HB_Stream (stream, fi.Length) }

#if wsgi
    member private self.ServeWsgi (request : HttpRequest) =
        HttpWSGI.WsgiHandler.entry server.Config request stream

    member private self.WsgiHandler (request : HttpRequest) =
        let path   = HttpServer.CanonicalPath request.path in
        let wsgire = new Regex(@"^wsgi(:?/|$)") in

            if wsgire.IsMatch(path) then
                self.ServeWsgi(request)
                Some false (* No keep-alive *)
            else
                None        
#endif

    member private self.ServeStatic (request : HttpRequest) =
        let path = HttpServer.CanonicalPath request.path in
        let path = if path.Equals("") then "index.html" else path
        let path = Path.Combine(server.Config.docroot, path) in

            if request.mthod <> "GET" then begin
                raise (HttpResponseExnWithCode HttpCode.HTTP_400)
            end;

            try
                let infos = FileInfo(path) in
                    if not infos.Exists then begin
                        raise (HttpResponseExnWithCode HttpCode.HTTP_404)
                    end;

                    let input =
                        try
                            infos.Open(FileMode.Open, FileAccess.Read, FileShare.Read)
                        with 
                        | :? IOException ->
                            raise (HttpResponseExnWithCode HttpCode.HTTP_500)
                    in
                        self.ResponseOfStream infos input
            with
            | :? UnauthorizedAccessException ->
                raise (HttpResponseExnWithCode HttpCode.HTTP_403)
            | :? PathTooLongException | :? NotSupportedException | :? ArgumentException ->
                raise (HttpResponseExnWithCode HttpCode.HTTP_404)

    member private self.ReadAndServeRequest () =
        try
            let request = reader.ReadRequest () in

            match List.tryPick (fun handler -> handler(request)) handlers with
            | Some status -> status
            
            | None ->            
                let close =
                    match request.headers.Get "Connection" with
                    | Some v when v.ToLowerInvariant() = "close" -> true
                    | Some v when v.ToLowerInvariant() = "keep-alive" -> false
                    | _ -> request.version <> HTTPV_11
                in
                let response =
                    try self.ServeStatic request
                    with
                    | :? System.IO.IOException as e -> raise e
                    | HttpResponseExn response -> response
                    | e -> http_response_of_code HttpCode.HTTP_500
                in
                    if close then begin
                        response.headers.Set "Connection" "close"
                    end;
                    response.headers.Set "Content-Length" (sprintf "%d" (http_body_length response.body));
                    begin
                        match response.body with
                        | HB_Raw bytes ->
                                self.SendResponseWithBody
                                    request.version response.code (response.headers.ToSeq ())
                                    bytes
                        | HB_Stream (f, flen) ->
                                self.SendStatus request.version response.code;
                                self.SendHeaders (response.headers.ToSeq ());
                                self.SendLine "";
                                try
                                    if f.CopyTo(stream, flen) < flen then
                                        failwith "ReadAndServeRequest: short-read"
                                finally
                                    noexn (fun () -> f.Close ())
                    end;
                    stream.Flush (); not close

        with
        | InvalidHttpRequest | NoHttpRequest as e->
            if e <> NoHttpRequest then begin
                self.SendResponse HTTPV_10 HttpCode.HTTP_400;
                stream.Flush ();
            end;
            false (* no keep-alive *)

    member self.Start () =
#if wsgi
        handlers <- self.WsgiHandler :: handlers
#endif

        try
            try
                HttpLogger.Info
                    (sprintf "new connection from [%A]" peer.Client.RemoteEndPoint);
                rawstream <- peer.GetStream ();
                match server.Config.tlsoptions with
                | None ->
                    HttpLogger.Info "Plaintext connection"
                    stream <- rawstream
                | Some tlsoptions ->
                    let s = new TLStream(rawstream, tlsoptions, TLSServer)
                    HttpLogger.Info
                        (sprintf "Secure connection:\n%s" (s.GetSessionInfoString()))
                    stream <- s
                reader <- new HttpStreamReader(stream);
                while self.ReadAndServeRequest () do () done
            with
            | e ->
                Console.WriteLine(e.Message)
        finally
            HttpLogger.Info "closing connection";
            noexn (fun () -> peer.Close ())

and HttpServer (localaddr : IPEndPoint, config : HttpServerConfig) =
    let (*---*) config : HttpServerConfig = config
    let mutable socket : TcpListener      = null

    interface IDisposable with
        member self.Dispose () =
            if socket <> null then noexn (fun () -> socket.Stop ())

    member self.Config
        with get () = config

    static member CanonicalPath (path : string) =
        let path =
            path.Split('/') |>
                Array.fold
                    (fun canon segment ->
                        match canon, segment with
                        | _                , ""      -> canon
                        | _                , "."     -> canon
                        | csegment :: ctail, ".."    -> ctail
                        | []               , ".."    -> []
                        | _                , segment -> segment :: canon)
                    []
        in
            String.Join("/", Array.ofList (List.rev path))

    member private self.ClientHandler peer = fun () ->
        use peer    = peer
        use handler = new HttpClientHandler (self, peer)
        handler.Start()

    member private self.AcceptAndServe () =
        while true do
            
            let peer = socket.AcceptTcpClient() in
                try
                    let thread = Thread(ThreadStart(self.ClientHandler peer)) in
                        thread.IsBackground <- true;
                        thread.Start()
                with
                | e ->
                    noexn (fun () -> peer.Close())
                    Console.WriteLine(e.Message)

    member self.Start () =
        if socket <> null then begin
            raise (InvalidOperationException ())
        end;

        HttpLogger.Info (sprintf "Starting HTTP server on port %d" localaddr.Port);
        socket <- TcpListener localaddr;
        try
            socket.Start ();
            socket.Server.SetSocketOption(SocketOptionLevel.Socket,
                                          SocketOptionName.ReuseAddress,
                                          true);
            self.AcceptAndServe ()
        finally
            noexn (fun () -> socket.Stop ())
            socket <- null

let run = fun config ->
#if wsgi
    use wsgi = new WsgiHandler ()
#endif
    use http = new HttpServer (config.localaddr, config)
    http.Start ()
