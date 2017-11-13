(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module PwToken

// ------------------------------------------------------------------------
open Bytes
open DER
open Nonce
open TLSInfo
open DataStream
module Range = Range

// ------------------------------------------------------------------------
type username = string

type token =
  | GToken of bytes
  | BToken  of bytes

type utk = UTK of username * token

#if verify
type gt = GoodToken       of token
type rt = RegisteredToken of utk
#endif

// ------------------------------------------------------------------------
let MaxTkReprLen = 512

// ------------------------------------------------------------------------
let tokens = ref ([] : utk list)

// ------------------------------------------------------------------------
let create () =
    let token = GToken (Nonce.random 256)
#if verify
    Pi.assume (GoodToken(token));
#endif
    token

// ------------------------------------------------------------------------
let register (username : username) (token : token) =
    match token with
    | BToken _  -> ()
    | GToken tk ->
        let utk = UTK (username, token)
#if verify
        Pi.assume (RegisteredToken utk);
#endif
        tokens := utk :: !tokens

// ------------------------------------------------------------------------
let rec verify_r (utk : utk) (tokens : utk list) =
    match tokens with
    | [] -> false
    | x :: tokens -> (utk = x) || verify_r utk tokens

let verify (username : username) (token : token) =
    let utk = UTK (username, token)
    verify_r utk !tokens

// ------------------------------------------------------------------------
let guess (bytes : bytes) =
    BToken bytes

// ------------------------------------------------------------------------
type delta = DataStream.delta

// ------------------------------------------------------------------------
let tk_good (token : token) =
    match token with GToken _ -> true | _ -> false

let tk_bytes (token : token) =
    match token with
    | GToken bytes -> bytes
    | BToken bytes -> bytes

// ------------------------------------------------------------------------
let tk_repr (e : epoch) (s : stream) (u : username) (tk : token) : delta =
    let tkgood  = tk_good  tk
    let tkbytes = tk_bytes tk

    let der = DER.Sequence [DER.Utf8String u; DER.Bool tkgood; DER.Bytes tkbytes]
    let der = DER.encode der

    if Bytes.length der > MaxTkReprLen then
        Error.unexpected "PwToken.tk_repr: token too large"
    else
        let rg = (0, MaxTkReprLen) in
        DataStream.createDelta e s rg der

// ------------------------------------------------------------------------
let tk_plain (e : epoch) (s : stream) (r : range) (delta : delta) : (username * token) option =
    let data =
#if verify
        empty_bytes
#else
        DataStream.deltaRepr (e) s r delta
#endif
    in
        match DER.decode data with
        | Some (Sequence [Utf8String u; Bool tkgood; Bytes tkbytes]) ->
            let tkbytes = tkbytes in
            let token = if tkgood then GToken tkbytes else BToken tkbytes in
                Some (u, token)
        | _ -> None

// ------------------------------------------------------------------------
let rp_repr (e : epoch) (s : stream) (b : bool) : delta =
    let bytes = DER.encode (DER.Bool b)

    if Bytes.length bytes > MaxTkReprLen then
        Error.unexpected "PwToken.rp_repr: token too large"
    else
        let rg = (0, MaxTkReprLen) in
        DataStream.createDelta (e) s rg bytes

// ------------------------------------------------------------------------
let rp_plain (e : epoch) (s : stream) (r : range) (d : delta) : bool =
    let data =
#if verify
        empty_bytes
#else
        DataStream.deltaRepr (e) s r d
#endif
    in
        match DER.decode data with
        | Some (DER.Bool b) -> b
        | _ -> false
