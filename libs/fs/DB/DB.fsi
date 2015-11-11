(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module DB

type db

type key   = string
type value = string

exception DBError of string

val opendb  : string -> db
val closedb : db -> unit
val put     : db -> key -> value -> unit
val get     : db -> key -> value option
val remove  : db -> key -> bool
val all     : db -> (key * value) list
val keys    : db -> key list
val merge   : db -> string -> unit
val tx      : db -> (db -> 'a) -> 'a
