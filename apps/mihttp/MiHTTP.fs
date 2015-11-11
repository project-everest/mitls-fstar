(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

(* ------------------------------------------------------------------------ *)
open System

(* ------------------------------------------------------------------------ *)
[<EntryPoint>]
let main args =
    if Array.length args >= 1 then
        let hostname = args.[0] in
        let requests = List.tail (List.ofArray args) in

        let channel = MiHTTPChannel.connect hostname in
        requests
            |> List.iter (fun request -> MiHTTPChannel.request channel None request)
        let rec wait () =
            match MiHTTPChannel.poll channel with
            | None -> Async.RunSynchronously (Async.Sleep 500)
            | Some (_, (_, d)) -> fprintfn stderr "%s\n" (Bytes.iutf8 (Bytes.abytes d))
            wait ()
        in
            wait (); 0
    else
        1
