(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module DER

// ------------------------------------------------------------------------
open System
open Org.BouncyCastle.Asn1

// ------------------------------------------------------------------------
type dervalue =
    | Bool       of bool
    | Bytes      of Bytes.bytes
    | Utf8String of string
    | Sequence   of dervalue list

// ------------------------------------------------------------------------
exception DerEncodingFailure
exception DerDecodingFailure

// ------------------------------------------------------------------------
let get_asn1_object (bytes : byte[]) : Asn1Object =
    try
        let stream = new Asn1InputStream(bytes)
        let obj    = stream.ReadObject()

        if stream.Position <> int64(bytes.Length) then null else obj

    with _ ->
        null

// ------------------------------------------------------------------------
let rec encode_r = function
    | Bytes      bytes  -> (new DerOctetString(Bytes.cbytes bytes)  :> Asn1Encodable)
    | Utf8String string -> (new DerUtf8String (string) :> Asn1Encodable)

    | Bool  b -> 
        let b = if b then 0xffuy else 0x00uy in
            ((new DerBoolean [|b|]) :> Asn1Encodable)

    | Sequence   seq    ->
        let seq = seq |> List.map encode_r in
            (new DerSequence(Array.ofList seq) :> Asn1Encodable)
    
let encode (x : dervalue) =
    try
        Bytes.abytes ((encode_r x).GetDerEncoded())
    with _ ->
        raise DerEncodingFailure

// ------------------------------------------------------------------------
let rec decode_r (o : Asn1Encodable) : dervalue  =
    match o with
    | (:? DerBoolean     as o) -> Bool       (o.IsTrue)
    | (:? DerOctetString as o) -> Bytes      (Bytes.abytes (o.GetOctets()))
    | (:? DerUtf8String  as o) -> Utf8String (o.GetString())
    | (:? DerSequence    as o) -> Sequence   ((Seq.cast o) |> Seq.map decode_r |> Seq.toList)
    | _                        -> raise DerDecodingFailure

let decode (bytes : Bytes.bytes) : dervalue option =
    try
        let obj = get_asn1_object (Bytes.cbytes bytes) in
            Some (decode_r obj)
    with _ ->
        None
