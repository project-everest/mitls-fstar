(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module DHDBManager

open Bytes
open Error
open System.IO

open Microsoft.FSharp.Text
open Org.BouncyCastle.Math
open Org.BouncyCastle.Utilities.IO.Pem
open Org.BouncyCastle.Asn1


type dh_params =
 | DH  of bytes * bytes
 | DHX of bytes * bytes * bytes

type _command = 
  | Check
  | Dump of string
  | Insert of string
  | Import of string

type command = option<_command>

type options = {
    command: command;
    dbfile:  string;
    minplen: int;
    minqlen: int;
    confidence: int;
    force: bool;
}

exception ArgError of string
exception InvalidPEMFile of string

let defaultDHPrimeConfidence = 80

(* ------------------------------------------------------------------------ *)
let PEM_DH_PARAMETERS_HEADER  = "DH PARAMETERS"       (* p, g, [len] *)
let PEM_DHX_PARAMETERS_HEADER = "X9.42 DH PARAMETERS" (* p, q, g, [j, validation] *)

(* ------------------------------------------------------------------------ *)
let load_params (stream : Stream) : dh_params =
    let reader = new PemReader(new StreamReader(stream))
    let obj    = reader.ReadPemObject() in

    if obj.Type = PEM_DH_PARAMETERS_HEADER then
        let obj = DerSequence.GetInstance(Asn1Object.FromByteArray(obj.Content)) in
        if obj.Count < 2 then
            raise (InvalidPEMFile(sprintf "Expecting at least 2 parameters, got %d" obj.Count))
        else
             DH (abytes (DerInteger.GetInstance(obj.Item(0)).PositiveValue.ToByteArrayUnsigned()),
                 abytes (DerInteger.GetInstance(obj.Item(1)).PositiveValue.ToByteArrayUnsigned()))
        
    else if obj.Type = PEM_DHX_PARAMETERS_HEADER then
        let obj = DerSequence.GetInstance(Asn1Object.FromByteArray(obj.Content)) in
        if obj.Count < 3 then
            raise (InvalidPEMFile(sprintf "Expecting at least 3 parameters, got %d" obj.Count))
        else
            DHX (abytes (DerInteger.GetInstance(obj.Item(0)).PositiveValue.ToByteArrayUnsigned()),
                 abytes (DerInteger.GetInstance(obj.Item(1)).PositiveValue.ToByteArrayUnsigned()),
                 abytes (DerInteger.GetInstance(obj.Item(2)).PositiveValue.ToByteArrayUnsigned()))
    
    else
        raise (InvalidPEMFile(sprintf "Unrecognized PEM header: %s" obj.Type))

(* ------------------------------------------------------------------------ *)
let load_params_from_file (file : string) : dh_params =
    let filestream = new FileStream(file, FileMode.Open, FileAccess.Read) in
    try
        load_params filestream
    finally
        filestream.Close()

(* ------------------------------------------------------------------------ *)
let load_default_params pem_file dhdb minSize =
    let p,g =
        match load_params_from_file pem_file with
        | DH(p,g) -> p,g
        | DHX(p,_,g) -> p,g
    match CoreDH.check_params dhdb defaultDHPrimeConfidence minSize p g with
    | Error(x) -> raise (InvalidPEMFile(x))
    | Correct(res) -> res


(* ------------------------------------------------------------------------ *)
let save_params (stream:Stream) (dhp:dh_params) =
    let writer    = new PemWriter(new StreamWriter(stream)) in
    match dhp with
    | DH(p,g) ->
        let derparams = 
            new DerSequence([| new DerInteger(new BigInteger(1, cbytes p)) :> Asn1Encodable;
                               new DerInteger(new BigInteger(1, cbytes g)) :> Asn1Encodable |])
            :> Asn1Encodable
        in
            writer.WriteObject(new PemObject(PEM_DH_PARAMETERS_HEADER, derparams.GetDerEncoded()))
    | DHX(p,q,g) ->
        let derparams = 
            new DerSequence([| new DerInteger(new BigInteger(1, cbytes p)) :> Asn1Encodable;
                               new DerInteger(new BigInteger(1, cbytes q)) :> Asn1Encodable;
                               new DerInteger(new BigInteger(1, cbytes g)) :> Asn1Encodable |])
            :> Asn1Encodable
        in
            writer.WriteObject(new PemObject(PEM_DHX_PARAMETERS_HEADER, derparams.GetDerEncoded()))
    writer.Writer.Flush()

(* ------------------------------------------------------------------------ *)
let save_params_to_file (file:string) (dhp:dh_params) =
    let filestream = new FileStream(file, FileMode.Create, FileAccess.Write) in
    try
        try
            save_params filestream dhp
        finally
            filestream.Close()
    with _ ->
        failwith "unexpected"

(* ------------------------------------------------------------------------------- *)
let dump db dir =
    let keys = DHDB.keys db in
    let n = ref 1u in
        for (p,g) in keys do
            match DHDB.select db (p,g) with
            | None -> failwith "unexpected"
            | Some(q,_) ->
                save_params_to_file (sprintf "%s/dhparams_%u.pem" dir !n) (DHX(p,q,g));
                n := !n + 1u

(* ------------------------------------------------------------------------------- *)
let check conf minPl minQl db =
    let keys = DHDB.keys db in
        for (pbytes,gbytes) in keys do
            match DHDB.select db (pbytes,gbytes) with
            | None -> failwith "unexpected"
            | Some(qbytes,safe_prime) ->
                match CoreDH.check_p_g_q conf minPl minQl pbytes gbytes qbytes with
                | Error(x) ->
                    eprintfn "Found an invalid parameter";
                    exit 1
                | Correct(sp') ->
                    if safe_prime <> sp' then
                        eprintfn "Found a parameter with an inconsistent safe_prime flag";
                        exit 1

(* ------------------------------------------------------------------------ *)
let cmdParse () = 
    let assembly = System.Reflection.Assembly.GetExecutingAssembly()
    let mypath   = Path.GetDirectoryName(assembly.Location)
    let myname   = Path.GetFileNameWithoutExtension(assembly.Location)

    let defaultDBFile  = DHDB.defaultFileName
    let defaultMinPlen = fst CoreDH.defaultPQMinLength
    let defaultMinQlen = snd CoreDH.defaultPQMinLength
  
    let options = ref {
        command = None;
        dbfile  = Path.Combine(mypath, defaultDBFile); 
        minplen = defaultMinPlen;
        minqlen = defaultMinQlen; 
        force   = false; 
        confidence = defaultDHPrimeConfidence; }

    let o_dbfile = fun s ->
        options := { !options with dbfile = s }

    let o_pemfile = fun s ->
        if not (File.Exists s) then
            let msg = sprintf "File not found: %s" s in
                raise (ArgError msg);
        options := { !options with command = Some(Insert(s)) }

    let o_dumpdir = fun s ->
        options := { !options with command = Some(Dump(s)) }
        
    let o_dbfile2 = fun s ->
        if not (File.Exists s) then
            let msg = sprintf "File not found: %s" s in
                raise (ArgError msg);
        options := { !options with command = Some(Import(s)) }

    let o_check = fun () ->
        options := { !options with command = Some(Check) }
    
    let o_force = fun () ->
        options := { !options with force = true }
    
    let o_minplen = fun n ->
        if n < 0 then
            let msg = sprintf "Length must be non-negative, given %d" n in
                raise (ArgError msg);
        options := { !options with minplen = n }

    let o_minqlen = fun n ->
        if n < 0 then
            let msg = sprintf "Length must be non-negative, given %d" n in
                raise (ArgError msg);
        options := { !options with minqlen = n }

    let o_confidence = fun n ->
        if n <= 0 then
            let msg = sprintf "Confidence level must be positive, given %d" n in
                raise (ArgError msg);
        options := { !options with confidence = n }

    let specs = [
        "-db",        ArgType.String o_dbfile  , sprintf "Database file (creates an empty one if it does not exist); default: %s" defaultDBFile
        "-insert",    ArgType.String o_pemfile , "Insert parameters stored in a PEM file"
        "-dump",      ArgType.String o_dumpdir , "Dump entries in the database as PEM files in the directory specified"
        "-check",     ArgType.Unit o_check     , "Check the validity of parameters in the database"
        "-import",    ArgType.String o_dbfile2 , "Import all parameters from given database"
        "-minPlen",   ArgType.Int o_minplen    , sprintf "Minimum modulus length in bits (used for validation); default: %d" defaultMinPlen
        "-minQlen",   ArgType.Int o_minqlen    , sprintf "Minimum subgroup size in bits (used for validation); default: %d" defaultMinQlen
        "-confidence",ArgType.Int o_confidence , sprintf "Confidence level for primality checks; default: %d" defaultDHPrimeConfidence
        "-force",     ArgType.Unit o_force     , "Do not validate parameters before inserting or importing them"   
    ]

    let specs = specs |> List.map (fun (sh, ty, desc) -> ArgInfo(sh, ty, desc))

    let usage = sprintf "Usage: %s options" myname

    try
      ArgParser.Parse (specs, usageText = usage);
      !options

    with ArgError msg ->
        ArgParser.Usage(specs, sprintf "Error: %s\n\n%s" msg usage);
        exit 1
            
(* ------------------------------------------------------------------------------- *)
[<EntryPoint>]
let _ =
    let options = cmdParse ()

    let db = 
        try 
            DHDB.create options.dbfile
        with _ ->
            eprintf "Could not open nor create database: %s" options.dbfile;
            exit 1
 
    match options.command with
    | None ->
        eprintf "At least one command must be specified";
        exit 1
    | Some(command) ->
        match command with  
        | Insert(pemfile) ->
            let dhp =
                try load_params_from_file pemfile
                with InvalidPEMFile s -> 
                    eprintfn "Invalid PEM file. %s" s;
                    exit 1
            in
                match dhp with
                | DH(p,g) -> 
                    match DHDB.select db (p,g) with
                    | Some _ -> 
                        eprintfn "Found parameters in the database with same modulus and generator";
                        exit 1
                    | _ ->
                        if options.force then
                            let p' = new BigInteger(1, cbytes p)
                            let pm1 = p'.Subtract(BigInteger.One)
                            let q' = pm1.Divide(BigInteger.Two) in
                            let q = abytes(q'.ToByteArrayUnsigned())
                            ignore(DHDB.insert db (p,g) (q,true));
                            exit 0
                        else
                            match CoreDH.check_p_g options.confidence options.minplen options.minqlen p g with
                            | Error(x) ->
                                eprintfn "Could not validate the parameters";
                                exit 1
                            | Correct(q) ->
                                ignore(DHDB.insert db (p,g) (q,true));
                                exit 0
                | DHX(p,q,g) ->
                    match DHDB.select db (p,g) with
                    | Some _ -> 
                        eprintfn "Found parameters in the database with same modulus and generator";
                        exit 1
                    | _ ->
                        if options.force then
                            let safe_prime =
                                let q = new BigInteger(1, cbytes q)
                                let p = new BigInteger(1, cbytes p)
                                let pm1 = p.Subtract(BigInteger.One)
                                let q' = pm1.Divide(BigInteger.Two) in
                                q.Equals(q')
                            ignore(DHDB.insert db (p,g) (q,safe_prime));
                            exit 0
                        else
                            match CoreDH.check_p_g_q options.confidence options.minplen options.minqlen p g q with
                            | Error(x) ->
                                eprintfn "Could not validate the parameters";
                                exit 1
                            | Correct(safe_prime) ->
                                ignore(DHDB.insert db (p,g) (q,safe_prime));
                                exit 0

        | Dump(dumpdir) -> 
            try 
                let di = Directory.CreateDirectory dumpdir in
                dump db dumpdir;
                exit 0
            with _ ->
                eprintf "Could not open nor create directory: %s" dumpdir;
                exit 1

        | Check ->
            check options.confidence options.minplen options.minqlen db;
            exit 0

        | Import(dbfile2) ->
            try 
                ignore (DHDB.merge db dbfile2);
                exit 0
            with _ ->
                eprintfn "Error merging the databases";
                exit 1
