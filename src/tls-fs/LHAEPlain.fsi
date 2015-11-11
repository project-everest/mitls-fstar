(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module LHAEPlain
open Bytes
open TLSInfo
open Range
open TLSError

type adata = bytes
type fragment
type plain = fragment

val mk_plain: id -> adata -> range -> bytes -> plain
val repr:  id -> adata -> range -> plain -> bytes

val makeAD: id -> StatefulPlain.history -> StatefulPlain.adata -> adata
val parseAD: id -> adata -> StatefulPlain.adata
val statefulPlainToLHAEPlain: id -> StatefulPlain.history -> StatefulPlain.adata -> adata -> range -> StatefulPlain.plain -> plain
val lhaePlainToStatefulPlain: id -> StatefulPlain.history -> StatefulPlain.adata -> adata -> range -> plain -> StatefulPlain.plain

val makeExtPad:  id -> adata -> range -> plain -> plain
val parseExtPad: id -> adata -> range -> plain -> Result<plain>

#if ideal
val widen: id -> adata -> range -> fragment -> fragment
#endif
