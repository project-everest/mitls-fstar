(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module StatefulPlain

open Bytes
open TLSConstants
open TLSInfo
open Range
open Error
open TLSError

type adata = bytes

type fragment
type prehistory = list<(adata * range * fragment)>
type history  = (nat * prehistory)
type plain = fragment

//------------------------------------------------------------------------------
val mk_plain: id -> history -> adata -> range -> bytes -> plain
val reprFragment:  id -> adata -> range -> fragment -> bytes
val repr:  id -> history -> adata -> range -> plain -> bytes

//------------------------------------------------------------------------------
val emptyHistory: id -> history
val extendHistory: id -> adata -> history -> range -> fragment -> history

val makeAD: id -> ContentType -> adata
val recordPlainToStAEPlain: epoch -> ContentType -> adata -> TLSFragment.history -> history -> range -> TLSFragment.plain -> plain
val stAEPlainToRecordPlain: epoch -> ContentType -> adata -> TLSFragment.history -> history -> range -> plain -> TLSFragment.plain

val makeExtPad:  id -> adata -> range -> fragment -> fragment
val parseExtPad: id -> adata -> range -> fragment -> Result<fragment>

#if ideal
val widen: id -> adata -> range -> fragment -> fragment
#endif
