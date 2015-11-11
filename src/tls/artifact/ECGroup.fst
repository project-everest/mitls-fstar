(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module ECGroup

open Platform.Bytes
open CoreCrypto
open Platform.Error
open TLSError
open TLSConstants

type ec_curve = CoreCrypto.ec_curve

type ec_all_curve =
| EC_CORE of ec_curve
| EC_UNKNOWN of int
| EC_EXPLICIT_PRIME
| EC_EXPLICIT_BINARY

type point_format =
| ECP_UNCOMPRESSED
| ECP_UNKNOWN of int

type point = ec_point

let getParams (c : ec_curve) : ec_params = {curve = c; point_compression = false}

let parse_curve (b : bytes) : option ec_params =
    if length b = 3 then
        let (ty, id) = split b 1 in
        if cbyte ty = 3uy then
            match cbyte2 id with
            | (0uy, 23uy) -> Some (getParams (ECC_P256))
            | (0uy, 24uy) -> Some (getParams (ECC_P384))
            | (0uy, 25uy) -> Some (getParams (ECC_P521))
            | _ -> None
        else None
    else None

val curve_id: ec_params -> Tot (lbytes 2)
let curve_id (p:ec_params) : bytes =
    abyte2 (match p.curve with
    | ECC_P256 -> (0uy, 23uy)
    | ECC_P384 -> (0uy, 24uy)
    | ECC_P521 -> (0uy, 25uy))

let bytelen (p:ec_params) : int =
    match p.curve with
    | ECC_P256 -> 32
    | ECC_P384 -> 48
    | ECC_P521 -> 66

val serialize_point: ec_params -> point -> Tot (b:bytes{length b < 257})
let serialize_point (p:ec_params) (e:point) : bytes =
  let x = CoreCrypto.ec_point_serialize e in
  let y:bytes = vlbytes 1 x in
  y

let parse_point (p:ec_params) (b:bytes) : option point  =
    let clen = bytelen p in
    if length b = 2*clen + 1 then
        let (et, r) = split b 1 in
        match cbyte et with
        | 4uy ->
            let (a,b) = split r clen in
            let e = {ecx = a; ecy = b;} in
            if CoreCrypto.ec_is_on_curve p e then Some e else None
        |_ -> None
    else
        None

let checkElement (p:ec_params) (b:point): option point =
    Some b
