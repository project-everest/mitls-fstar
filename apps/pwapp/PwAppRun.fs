(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module PwAppRun

open System
open System.Threading

let servname = "mitls.example.org"
let my       = "xxxxxxxxxxxxxxxx"
let token    = PwToken.create ()
let _        = PwToken.register my token

let server () =
    try
        printfn "S: %A" (PwApp.response servname)
    with e ->
        printfn "E: %A" e

let client () =
    let r = (PwApp.request servname my token) in
        printfn "C: %A" r

let program () =
    let tserver = new Thread(new ThreadStart(server))

    tserver.Name <- "Server"; tserver.Start ()
    Thread.Sleep 1000; client ();
    Thread.Sleep -1

let _ =
    program ()
