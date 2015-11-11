module List
open Bytes

val fold: (bytes -> bytes -> bytes) -> bytes -> list bytes -> bytes
val filter: ('a -> bool) -> 'a list -> 'a list // AP: In HS, only used with 'a = HT_type, but it's not defined here.
val foldBack: (bytes -> bytes -> bytes) -> list bytes -> bytes -> bytes
val exists: ('a -> bool) -> list 'a -> bool
val memr: list 'a -> 'a -> bool
val choose: ('a -> 'b option) -> list 'a -> list 'a
val tryFind: ('a -> bool) -> 'a list -> 'a option
val listLength: ('a list) -> int
val listHead: ('a list) -> 'a
val find: ('a -> bool) -> 'a list -> 'a
val map: ('a -> 'b) -> 'a list -> 'b list
