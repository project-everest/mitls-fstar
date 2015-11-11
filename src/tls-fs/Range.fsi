(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Range

open Bytes
open TLSInfo

type range = nat * nat 
type rbytes = bytes
val sum: range -> range -> range

val ivSize: id -> nat
val fixedPadSize: id -> nat
val maxPadSize: id -> nat
#if TLSExt_extendedPadding
val extendedPad: id -> range -> nat -> bytes
#endif
val targetLength: id -> range -> nat
val cipherRangeClass: id -> nat -> range
val rangeClass: id -> range -> range
