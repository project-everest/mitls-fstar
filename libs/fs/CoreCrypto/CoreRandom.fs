(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module CoreRandom

open Org.BouncyCastle.Security

let provider = new SecureRandom()

let random (i : int) =
    if i < 0 then
        invalidArg "length" "must be non-negative";

    let bytes = Array.create i 0uy in
        lock provider (fun () -> provider.NextBytes(bytes, 0, i));
        Bytes.abytes bytes
