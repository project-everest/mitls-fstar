module Crypto.Plain

open Crypto.Indexing
open Platform.Bytes
open Flag

type plainLen = nat
val plain: i:id -> l:plainLen -> Type0
val as_bytes: #i:id -> #l:plainLen -> p:plain i l -> GTot (lbytes l)
val repr: #i:id {~(safeId i)} -> #l:plainLen -> p:plain i l -> Tot (b:lbytes l {b = as_bytes p })
val make: #i:id {~(safeId i)}-> l:plainLen -> b:lbytes l -> Tot (p:plain i l {b = as_bytes p})
