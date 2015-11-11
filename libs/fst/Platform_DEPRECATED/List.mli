open Bytes

val fold: (bytes -> bytes -> bytes) -> bytes -> bytes list -> bytes
val filter: ('a -> bool) -> 'a list -> 'a list // AP: In HS, only used with 'a = HT_type, but it's not defined here.
val foldBack: (bytes -> bytes -> bytes) -> bytes list -> bytes -> bytes
val exists: ('a -> bool) -> 'a list -> bool
val memr: 'a list -> 'a -> bool when 'a : equality
val choose: ('a -> 'b option) -> 'a list -> 'b list // AP: Not used parametrically in HS, but types are not defined here.
val tryFind: ('a -> bool) -> 'a list -> 'a option
val listLength: ('a list) -> int
val listHead: ('a list) -> 'a
val find: ('a -> bool) -> 'a list -> 'a
val map: ('a -> 'b) -> 'a list -> 'b list
