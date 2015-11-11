(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module MiHTTPInstanceDB

open Bytes
open Serialization
open MiHTTPChannel

let dbname = "http-instances.sqlite3"

let save (c : channel) =
    let state = save_channel c in
    let key   = serialize<cbytes> state.c_channelid in
    let value = serialize<cstate> state in

    let doit (db : DB.db) =
        ignore (DB.remove db key);
        DB.put db key value
    in

    let db = DB.opendb dbname in
    try
        DB.tx db doit
    finally
        DB.closedb db

let restore (id : channelid) =
    let key   = serialize<cbytes> (cbytes id) in

    let doit (db : DB.db) =
        DB.get db key
            |> Option.map deserialize<cstate>
            |> Option.map MiHTTPChannel.restore_channel    
    in

    let db = DB.opendb dbname in
    try
        DB.tx db doit
    finally
        DB.closedb db
