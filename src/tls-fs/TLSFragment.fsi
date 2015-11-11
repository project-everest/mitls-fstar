(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module TLSFragment

open Bytes
open TLSInfo
open TLSConstants
open Range
open Error
open TLSError

type history

type fragment
type plain = fragment

val emptyHistory: epoch -> history
val extendHistory: epoch -> ContentType -> history -> range -> fragment -> history

val handshakeHistory: epoch -> history -> HSFragment.stream
val ccsHistory: epoch -> history -> HSFragment.stream
val alertHistory: epoch -> history -> HSFragment.stream

val mk_plain: epoch -> ContentType -> history -> range -> bytes -> plain
val mk_fragment: id -> ContentType -> range -> bytes -> fragment 
val reprFragment: id -> ContentType -> range -> fragment -> bytes
val repr:  epoch -> ContentType -> history -> range -> plain -> bytes

val hsPlainToRecordPlain     : epoch -> history -> range -> HSFragment.plain -> plain
val ccsPlainToRecordPlain    : epoch -> history -> range -> HSFragment.plain -> plain
val alertPlainToRecordPlain  : epoch -> history -> range -> HSFragment.plain -> plain
val appPlainToRecordPlain    : epoch -> history -> range -> AppFragment.plain -> plain
val recordPlainToHSPlain     : epoch -> history -> range -> plain -> HSFragment.plain
val recordPlainToCCSPlain    : epoch -> history -> range -> plain -> HSFragment.plain
val recordPlainToAlertPlain  : epoch -> history -> range -> plain -> HSFragment.plain
val recordPlainToAppPlain    : epoch -> history -> range -> plain -> AppFragment.plain

val makeExtPad:  id -> ContentType -> range -> fragment -> fragment
val parseExtPad: id -> ContentType -> range -> fragment -> Result<fragment>

#if ideal
val widen: id -> ContentType -> range -> fragment -> fragment
#endif
