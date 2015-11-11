(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Encode

open Bytes
open Error
open TLSError
open TLSInfo
open TLSConstants
open Range

type plain
val mk_plain: id -> LHAEPlain.adata -> nat -> bytes -> plain
val repr:  id -> LHAEPlain.adata -> range -> plain -> bytes

val mac: id -> MAC.key -> LHAEPlain.adata -> range -> LHAEPlain.plain -> plain
val verify: id -> MAC.key -> LHAEPlain.adata -> range -> plain -> Result<LHAEPlain.plain>

val decodeNoPad_bytes: id -> LHAEPlain.adata -> range -> l:nat -> lbytes -> rbytes * MAC.tag
val verify_MACOnly: id -> MAC.key -> LHAEPlain.adata -> range -> nat -> rbytes -> MAC.tag ->
    Result<(range*LHAEPlain.plain)>

#if ideal
val widen: id -> LHAEPlain.adata -> range -> plain -> plain
#endif
