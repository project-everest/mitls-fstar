(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Mime

open System
open System.IO
open System.Text
open System.Text.RegularExpressions

type mime = string

type MimeMap () =
    let mutable mimes : Map<string, string> = Map.empty

    static member CanonizeExt (ext : string) =
        let ext = ext.ToLowerInvariant() in
            if ext.StartsWith(".") then ext else "." + ext

    member self.Bind (ext : string) (mime : mime) =
        let ext = MimeMap.CanonizeExt(ext) in
            if ext = "." then begin
                raise (ArgumentException ("cannot bind empty extension"))
            end;
            mimes <- Map.add ext mime mimes

    member self.Lookup (ext : string) =
        mimes.TryFind (MimeMap.CanonizeExt ext)

let of_stream (stream : Stream) =
    let process_line = fun line ->
        match Regex.Replace(line, "#.*$", "").Trim() with
        | "" -> None
        | _  ->
            match List.ofArray (Regex.Split(line, "\s+")) with
            | [] -> failwith "MimeMap.of_stream"
            | ctype :: exts -> Some (ctype, exts)
    in
        use reader = new StreamReader(stream, Encoding.ASCII)
        let mime = MimeMap () in

        let _ =
            for line in Utils.IO.ReadAllLines reader do
                match process_line line with
                | Some (ctype, exts) ->
                    exts |> List.iter (fun ext -> mime.Bind ext ctype)
                | None -> ()
        in
            mime

let of_file (filename : string) =
    use stream = File.Open(filename, FileMode.Open, FileAccess.Read)
    of_stream stream

