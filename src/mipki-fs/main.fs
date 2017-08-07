module Main

open System.IO
open System.Security.Cryptography
open System.Security.Cryptography.X509Certificates
open Microsoft.FSharp.Text.Lexing
open System.Collections

let mutable templates = new Map<string, TplAst.asntpl>([])
let mutable parsed = new Map<string, Asn1.asn1>([])
let mutable debug = false

let rec command (args: string list) = 
    match args with
    | "-d" :: r ->
        debug <- true
        command r
    | "match" :: tpl :: asn :: r ->
        try
            let x = Map.find asn parsed
            let t = Map.find tpl templates
            let o = Tplverifier.tpl_verify t x
            printfn "%s" (Parsedprinter.parsed_print o)
            command r
        with e -> 
            printfn "%A" e; 1
    | "writeasn" :: asn :: file :: r ->
        try
            let x = Map.find asn parsed
            let s = Asn1print.asn1_print x
            if file = "-" then printfn "%s" s
            else
                File.WriteAllText(file, s)
                printfn "Written %d bytes to %s" s.Length file
            command r
        with e -> 
            printfn "%A" e
            printfn "Unknown asn.1 reference: %s" asn; 1
    | "writeder" :: asn :: file :: r ->
        try
            let x = Map.find asn parsed
            let ba = Asn1encode.asn1_serialize x
            File.WriteAllBytes(file, ba);
            printfn "Written %d bytes to %s" ba.Length file
            command r
        with e -> 
            printfn "Unknown asn.1 reference: %s" asn; 1
    | "loadder" :: asnname :: derfile :: r ->
        try
            let ba = File.ReadAllBytes(derfile)
            let x = Asn1decode.asn1_decode ba
            parsed <- Map.add asnname x parsed;
            printfn "Loaded ASN.1 %s from DER file %s" asnname derfile
            if debug then printfn "%A" x
            command r
        with e -> 
            printfn "Failed to load DER file: %A" e; 3
    | "loadasn" :: asnname :: asnfile :: r ->
        use textReader = new System.IO.StreamReader(asnfile) in
        let lexbuf = LexBuffer<char>.FromTextReader textReader in
        try
            let x = Parser.start_asn (Lexer.token) lexbuf in
            parsed <- Map.add asnname x parsed;
            printfn "Loaded ASN.1 %s from ASN file %s" asnname asnfile
            if debug then printfn "%A" x
            command r
        with e -> 
            let pos = lexbuf.EndPos in
            let line = pos.Line in
            let column = pos.Column in
            let message = e.Message in
            printf "Syntax error in <%s> on line %d, character %d: %s" asnfile (line+1) column message;
            1
    | "loadtpl" :: tplname :: tplfile :: r ->
        use textReader = new System.IO.StreamReader(tplfile) in
        let lexbuf = LexBuffer<char>.FromTextReader textReader in
        try
            let x = Parser.start (Lexer.token) lexbuf in
            templates <- Map.add tplname x templates;
            printfn "Loaded template %s from file %s" tplname tplfile
            if debug then printfn "%A" x
            command r
        with e -> 
            let pos = lexbuf.EndPos in
            let line = pos.Line in
            let column = pos.Column in
            let message = e.Message in
            printf "Syntax error in <%s> on line %d, character %d: %s" tplfile (line+1) column message;
            1
    | [] -> 0
    | _ -> printfn "Usage: [-d] action\n\tloadtpl <tplname> <tplfile>: load ASN.1 template from <tplfile> under name tplname\n\n "; 2

[<EntryPoint>]
let main argv = 
    command (List.ofArray argv)