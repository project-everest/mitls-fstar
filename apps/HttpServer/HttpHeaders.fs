(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module HttpHeaders

open System
open System.Globalization

open Utils

let CONTENT_LENGTH = "Content-Length"
let CONTENT_TYPE   = "Content-Type"

let normkey = fun (key : string) ->
    key.Trim().ToLowerInvariant()

type HttpHeaders () =
    let mutable headers : (string * string) list = []

    static member OfList (headers : (string * string) list) =
        let aout = HttpHeaders () in
            headers
                |> List.map (fun (h, v) -> (h.Trim(), v))
                |> List.iter (fun (h, v) -> aout.Add h v);
            aout

    member self.ToSeq () =
        headers
            |> List.rev
            |> Seq.ofList

    member self.Exists (key : string) =
        let key = normkey(key) in
            headers |> List.exists (fun (k, _) -> normkey(k) = key)

    member self.Get (key : string) =
        let key = normkey(key) in
            match headers |> List.tryFind (fun (k, _) -> normkey(k) = key) with
            | Some (_, value) -> Some value
            | None -> None

    member self.GetDfl(key : string, dfl : string) =
        match self.Get (key) with
        | None   -> dfl
        | Some x -> x

    member self.GetAll (key : string) =
        let key = normkey(key) in
            headers |> List.filter (fun (k, _) -> normkey(k) = key)

    member self.Set (key : string) (value : string) =
        let normed = normkey(key) in
            headers <- headers |> List.filter (fun (k, _) -> normkey(k) <> normed);
            headers <- (key, value) :: headers

    member self.Add (key : string) (value : string) =
        headers <- (key, value) :: headers

    member self.Del (key : string) =
        let key = normkey(key) in
            headers <- headers |> List.filter (fun (k, _) -> normkey(k) = key)

    member self.ContentLength () =
        match self.Get CONTENT_LENGTH with
        | None      -> None
        | Some clen ->
            try
                Some (Int64.Parse(clen, NumberStyles.None))
            with
            | :? FormatException | :? OverflowException ->
                raise (FormatException ())


exception InvalidHttpHeaderContinuation

type HttpHeadersBuilder () =
    let mutable lastseen = None
    let mutable headers  = HttpHeaders ()

    member private self.MaybePop () =
        match lastseen with
        | Some (h, v) -> headers.Add h v; lastseen <- None
        | _ -> ()

    member self.Push (key : string) (value : string) =
        self.MaybePop (); lastseen <- Some (key, value.Trim())

    member self.PushContinuation(value : string) =
        match lastseen with
        | Some (h, v) -> lastseen <- Some (h, sprintf "%s %s" v (value.Trim ()))
        | _ -> raise InvalidHttpHeaderContinuation

    member self.Headers
        with get () = self.MaybePop(); headers
