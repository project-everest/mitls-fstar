(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module DB

open System
open System.Data
open System.IO

#if __MonoSQL__
open Mono.Data.Sqlite
type SQLiteConnection = SqliteConnection
#else
open System.Data.SQLite
#endif

exception DBError of string

type db = DB of SQLiteConnection

type key = string
type value = string

let _db_lock = new Object()

module Internal =
    let wrap (cb : unit -> 'a) =
        try  cb ()
        with exn ->
            fprintfn stderr "DBError: %s" exn.Message;
            raise (DBError (exn.ToString()))

    let opendb (filename : string) =
        ((new FileInfo(filename)).Directory).Create()
        let request = "CREATE TABLE IF NOT EXISTS map(key TEXT PRIMARY KEY, value TEXT NOT NULL)" in
        let urn     = String.Format("Data Source={0};Version=3", filename) in
        let db      = new SQLiteConnection(urn) in
            db.Open();
            db.DefaultTimeout <- 5;
            use command = db.CreateCommand() in
                command.CommandText <- request;
                ignore (command.ExecuteNonQuery() : int);
                DB db

    let closedb (DB db : db) =
        use db = db in ()

    let attach (DB db : db) (filename : string) (alias : string) =
        let request = sprintf "ATTACH :filename AS :alias" 
        use command = db.CreateCommand() in
            command.CommandText <- request;
            command.Parameters.Add("filename", DbType.String).Value <- filename;
            command.Parameters.Add("alias", DbType.String).Value <- alias;
            ignore (command.ExecuteNonQuery() : int);
            DB db

    let put (DB db : db) (k : key) (v : value) =
        let request = "INSERT OR REPLACE INTO map (key, value) VALUES (:k, :v)" in
        use command = db.CreateCommand() in
            command.CommandText <- request;
            command.Parameters.Add("k", DbType.String).Value <- k;
            command.Parameters.Add("v", DbType.String).Value <- v;
            ignore (command.ExecuteNonQuery())

    let get (DB db : db) (k : key) =
        let request = "SELECT value FROM map WHERE key = :k LIMIT 1" in
        use command = db.CreateCommand() in

            command.CommandText <- request;
            command.Parameters.Add("k", DbType.String).Value <- k;

            let reader  = command.ExecuteReader() in
                try
                    if reader.Read() then
                        let data = reader.GetString(0) in
                        Some data
                    else
                        None
                finally
                    reader.Close()

    let remove (DB db : db) (k : key) =
        let request = "DELETE FROM map WHERE key = :k" in
        use command = db.CreateCommand() in
            command.CommandText <- request;
            command.Parameters.Add("k", DbType.String).Value <- k;
            command.ExecuteNonQuery() <> 0

    let all (DB db : db) =
        let request = "SELECT key, value FROM map" in
        use command = db.CreateCommand() in

            command.CommandText <- request;

            let reader = command.ExecuteReader() in
            let aout   = ref [] in

                try
                    while reader.Read() do
                        let kdata = reader.GetString(0) in
                        let vdata = reader.GetString(1) in
                        aout := (kdata, vdata) :: !aout
                    done;
                    !aout
                finally
                    reader.Close()

    let keys (DB db : db) =
        let request = "SELECT key FROM map" in
        use command = db.CreateCommand() in

            command.CommandText <- request;

            let reader = command.ExecuteReader() in
            let aout   = ref [] in

                try
                    while reader.Read() do
                        let kdata = reader.GetString(0) in
                        aout := kdata :: !aout
                    done;
                    !aout
                finally
                    reader.Close()

    let merge (DB db : db) (alias : string) =
        // Only used internally, alias is trusted    
        let request = sprintf "INSERT OR IGNORE INTO map (key, value) SELECT key, value FROM %s.map" alias in
        use command = db.CreateCommand() in         
            command.Parameters.Add("alias", DbType.String).Value <- alias;
            command.CommandText <- request;
            ignore (command.ExecuteNonQuery() : int)

    let tx (DB db : db) (f : db -> 'a) : 'a =
        lock (_db_lock) (fun () ->
            use tx = db.BeginTransaction (IsolationLevel.ReadCommitted) in
            let aout = f (DB db) in
                tx.Commit (); aout)

let opendb (filename : string) =
    Internal.wrap (fun () -> Internal.opendb filename)

let closedb (db : db) =
    Internal.wrap (fun () -> Internal.closedb db)

let attach (db : db) (filename : string) (alias : string) =
    Internal.wrap (fun () -> Internal.attach db filename alias)

let put (db : db) (k : key) (v : value) =
    Internal.wrap (fun () -> Internal.put db k v)

let get (db : db) (k : key) =
    Internal.wrap (fun () -> Internal.get db k)

let remove (db : db) (k : key) =
    Internal.wrap (fun () -> Internal.remove db k)

let all (db : db) =
    Internal.wrap (fun () -> Internal.all db)

let keys (db : db) =
    Internal.wrap (fun () -> Internal.keys db)

let merge (db : db) (db2 : string) =
    let db = attach db db2 "db" in
    Internal.wrap (fun () -> Internal.merge db "db")

let tx (db : db) (f : db -> 'a) =
    Internal.wrap (fun () -> Internal.tx db f)
