(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module List

open Bytes

// Most of these functions are not used parametrically by other modules, but required types are not defined here.
val fold: (bytes -> bytes -> bytes) -> bytes -> bytes list -> bytes
val filter: ('a -> bool) -> 'a list -> 'a list
val foldBack: (bytes -> bytes -> bytes) -> bytes list -> bytes -> bytes
val exists: ('a -> bool) -> 'a list -> bool
val memr: 'a list -> 'a -> bool when 'a : equality
val choose: ('a -> 'b option) -> 'a list -> 'b list
val tryFind: ('a -> bool) -> 'a list -> 'a option
val listLength: ('a list) -> int
val listHead: ('a list) -> 'a
val find: ('a -> bool) -> 'a list -> 'a
val map: ('a -> 'b) -> 'a list -> 'b list
