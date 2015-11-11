type byte = char
(*@ type nat = (n:int){C_pr_LessThanOrEqual(0, n)} @*)
type nat = int
(*@ type cbytes = string @*)
type cbytes = string
(*@ type bytes @*)
type bytes
(*@ function val B : (bytes -> byte array) @*)

(*@ val empty_bytes : (b:bytes){B (b) = C_array_of_list C_op_Nil ()} @*)
val empty_bytes : bytes 
(*@ val abytes : (b:cbytes -> (a:bytes){B (a) = b}) @*)
val abytes : (cbytes -> bytes) 
(*@ val abyte : (b:byte -> (a:bytes){B (a) = C_array_of_list C_op_ColonColon (b, C_op_Nil ())}) @*)
val abyte : (byte -> bytes) 
(*@ val abyte2 : (b:(byte * byte) -> (a:bytes){(!b1. (!b2. b = (b1, b2) => B (a) = C_array_of_list C_op_ColonColon (b1, C_op_ColonColon (b2, C_op_Nil ()))))}) @*)
val abyte2 : ((byte * byte) -> bytes) 
(*@ val cbytes : (a:bytes -> (b:cbytes){B (a) = b}) @*)
val get_cbytes : (bytes -> cbytes) 
(*@ val cbyte : (a:bytes -> (b:byte){B (a) = C_array_of_list C_op_ColonColon (b, C_op_Nil ())}) @*)
val cbyte : (bytes -> byte) 
(*@ val cbyte2 : (a:bytes -> (b1:byte * b2:byte){B (a) = C_array_of_list C_op_ColonColon (b1, C_op_ColonColon (b2, C_op_Nil ()))}) @*)
val cbyte2 : (bytes -> (byte * byte)) 
(*@ function val BLength : (cbytes -> int) @*)

(*@ function val Length : (bytes -> int) @*)

(*@  assume (!x. (!y. BLength (C_bop_ArrayAppend (x, y)) = C_bop_Addition (BLength (x), BLength (y)))) @*)

(*@  assume (!x. Length (x) = BLength (B (x))) @*)

(*@ val length : (b:bytes -> (l:nat){Length (b) = l}) @*)
val length : (bytes -> nat) 
(*@ type (l:nat) lbytes = (b:bytes){Length (b) = l} @*)
type lbytes = bytes
(*@ val createBytes : (l:int -> ((v:int){C_pr_LessThanOrEqual(0, v) /\ C_pr_LessThan(v, 256)} -> (;l) lbytes)) @*)
val createBytes : (int -> (int -> lbytes)) 
(*@ val equalBytes : (b0:bytes -> (b1:bytes -> (r:bool){r = True /\ B (b0) = B (b1) \/ r = False /\ B (b0) <> B (b1)})) @*)
val equalBytes : (bytes -> (bytes -> bool)) 
(*@ val xor : (bytes -> (bytes -> (nb:nat -> (b3:bytes){Length (b3) = nb}))) @*)
val xor : (bytes -> (bytes -> (nat -> bytes))) 
(*@ val op_AtBar : (b1:bytes -> (b2:bytes -> (b:bytes){B (b) = C_bop_ArrayAppend (B (b1), B (b2))})) @*)
val op_AtBar : (bytes -> (bytes -> bytes)) 
(*@ val split : (b:bytes -> ((i:nat){C_pr_GreaterThanOrEqual(Length (b), i)} -> (b1:bytes * b2:bytes){Length (b1) = i /\ B (b) = C_bop_ArrayAppend (B (b1), B (b2))})) @*)
val split : (bytes -> (nat -> (bytes * bytes))) 
(*@ val split2 : (b:bytes -> (i:nat -> ((j:nat){C_pr_GreaterThanOrEqual(Length (b), C_bop_Addition (i, j))} -> (b1:bytes * b2:bytes * b3:bytes){Length (b1) = i /\ Length (b2) = j /\ B (b) = C_bop_ArrayAppend (B (b1), C_bop_ArrayAppend (B (b2), B (b3)))}))) @*)
val split2 : (bytes -> (nat -> (nat -> (bytes * bytes * bytes)))) 
(*@  assume (!x. C_bop_ArrayAppend (x, C_array_of_list C_op_Nil ()) = x) @*)

(*@  assume (!b1. (!b2. (!c1. (!c2. C_bop_ArrayAppend (b1, b2) = C_bop_ArrayAppend (c1, c2) /\ BLength (b1) = BLength (c1) => b1 = c1 /\ b2 = c2)))) @*)

(*@  assume (!b1. (!b2. (!c1. (!c2. C_bop_ArrayAppend (b1, b2) = C_bop_ArrayAppend (c1, c2) /\ BLength (b2) = BLength (c2) => b1 = c1 /\ b2 = c2)))) @*)

(*@  assume (!b1. (!b2. (!b3. C_bop_ArrayAppend (C_bop_ArrayAppend (b1, b2), b3) = C_bop_ArrayAppend (b1, C_bop_ArrayAppend (b2, b3))))) @*)

(*@ function val IntBytes : ((int * int) -> bytes) @*)

(*@ val bytes_of_int : (l:int -> (i:int -> (b:bytes){b = IntBytes (l, i)})) @*)
val bytes_of_int : (int -> (int -> bytes)) 
(*@ val int_of_bytes : ((b:bytes){C_pr_LessThanOrEqual(Length (b), 8)} -> (i:nat){b = IntBytes (Length (b), i) /\ Length (b) = 1 => C_pr_LessThanOrEqual(0, i) /\ C_pr_LessThan(i, 256)}) @*)
val int_of_bytes : (bytes -> nat) 
(*@  assume (!l. (!i. Length (IntBytes (l, i)) = l)) @*)

(*@  assume (!l. (!i0. (!i1. IntBytes (l, i0) = IntBytes (l, i1) => i0 = i1))) @*)

(*@ function val Utf8 : (string -> bytes) @*)

(*@ val utf8 : (s:string -> (b:bytes){b = Utf8 (s)}) @*)
val utf8 : (string -> bytes) 
(*@ val iutf8 : (b:bytes -> (s:string){b = Utf8 (s)}) @*)
val iutf8 : (bytes -> string) 
(*@  assume (!x. (!y. Utf8 (x) = Utf8 (y) => x = y)) @*)

