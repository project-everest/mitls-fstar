(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module DER

open Bytes

type dervalue =
    | Bool       of bool
    | Bytes      of bytes
    | Utf8String of string
    | Sequence   of dervalue list

val encode : dervalue -> bytes
val decode : bytes -> dervalue option
