(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module PwToken

// ------------------------------------------------------------------------
open Bytes
open TLSInfo
open DataStream
open Range

// ------------------------------------------------------------------------
type token
type username = string

val create   : unit -> token
val register : username -> token -> unit
val verify   : username -> token -> bool
val guess    : bytes -> token

// ------------------------------------------------------------------------
type delta = DataStream.delta

val MaxTkReprLen : int

val tk_repr  : epoch -> stream -> username -> token -> delta
val tk_plain : epoch -> stream -> range -> delta -> (username * token) option

val rp_repr  : epoch -> stream -> bool -> delta
val rp_plain : epoch -> stream -> range -> delta -> bool
