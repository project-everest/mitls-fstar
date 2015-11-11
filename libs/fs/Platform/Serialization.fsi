(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Serialization

val serialize<'T>   : 'T -> string
val deserialize<'T> : string -> 'T
