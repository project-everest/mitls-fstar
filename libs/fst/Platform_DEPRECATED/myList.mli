(*@ open Bytes @*)
open Bytes
(*@ function val ListLength : ('a list -> Bytes.nat) @*)

(*@  assume ListLength (C_op_Nil ()) = 0 @*)

(*@  assume (!x. (!y. ListLength (C_op_ColonColon (x, y)) = C_bop_Addition (1, ListLength (y)))) @*)

(*@  assume (!l. Bytes.BLength (C_array_of_list (l)) = ListLength (l)) @*)

(*@ function val Unfold : ((Bytes.bytes * Bytes.bytes list) -> Bytes.bytes) @*)

(*@ function val UnfoldBack : ((Bytes.bytes list * Bytes.bytes) -> Bytes.bytes) @*)

(*@ val fold : ((Bytes.bytes -> (Bytes.bytes -> Bytes.bytes)) -> (s:Bytes.bytes -> (bl:Bytes.bytes list -> (b:Bytes.bytes){b = Unfold (s, bl)}))) @*)
val fold : ((Bytes.bytes -> (Bytes.bytes -> Bytes.bytes)) -> (Bytes.bytes -> (Bytes.bytes list -> Bytes.bytes))) 
(*@ val filter : (('a -> bool) -> ('a list -> 'a list)) @*)
val filter : (('a -> bool) -> ('a list -> 'a list)) 
(*@ val foldBack : ((Bytes.bytes -> (Bytes.bytes -> Bytes.bytes)) -> (bl:Bytes.bytes list -> (s:Bytes.bytes -> (b:Bytes.bytes){b = UnfoldBack (bl, s)}))) @*)
val foldBack : ((Bytes.bytes -> (Bytes.bytes -> Bytes.bytes)) -> (Bytes.bytes list -> (Bytes.bytes -> Bytes.bytes))) 
(*@ val exists : (('a -> bool) -> ('a list -> bool)) @*)
val exists : (('a -> bool) -> ('a list -> bool)) 
(*@ val memr : ('a list -> ('a -> bool)) @*)
val memr : ('a list -> ('a -> bool)) 
(*@ val choose : (('a -> 'b option) -> ('a list -> 'b list)) @*)
val choose : (('a -> 'b option) -> ('a list -> 'b list)) 
(*@ val tryFind : (('a -> bool) -> ('a list -> 'a option)) @*)
val tryFind : (('a -> bool) -> ('a list -> 'a option)) 
(*@ val listLength : (l:'a list -> (len:Bytes.nat){ListLength (l) = len}) @*)
val listLength : ('a list -> Bytes.nat) 
(*@ val listHead : ((l:'a list){C_pr_GreaterThan(ListLength (l), 0)} -> 'a) @*)
val listHead : ('a list -> 'a) 
(*@ val find : (('a -> bool) -> ('a list -> 'a)) @*)
val find : (('a -> bool) -> ('a list -> 'a)) 
(*@ val map : (('a -> 'b) -> ('a list -> 'b list)) @*)
val map : (('a -> 'b) -> ('a list -> 'b list)) 
