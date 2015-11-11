(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module KEF

open Bytes
open TLSConstants
open TLSInfo
open Error
open TLSError
open PMS

//MK unused? type log = bytes

val extract: SessionInfo -> pms -> PRF.masterSecret
val extract_extended: SessionInfo -> pms -> PRF.masterSecret

