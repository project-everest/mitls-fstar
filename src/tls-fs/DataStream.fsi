(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module DataStream
open TLSInfo
open Bytes
open Error
open TLSError
open Range

val splitRange: epoch -> range -> range * range

type stream
type delta

// The following two functions are used only by the application.
// They are never called from TLS.
val createDelta: epoch -> stream -> range -> rbytes -> delta
val deltaBytes: epoch -> stream -> range -> delta -> rbytes

val init: epoch -> stream
val append: epoch -> stream -> range -> delta -> stream
val split: epoch -> stream -> range -> range -> delta -> delta * delta
val deltaPlain: epoch -> stream -> range -> rbytes -> delta
val deltaRepr: epoch -> stream -> range -> delta -> rbytes

#if ideal
val widen: epoch -> stream -> range -> range -> delta -> delta
#endif
