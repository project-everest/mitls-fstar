(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Error

type ('a,'b) optResult =
    | Error of 'a
    | Correct of 'b

val perror: string -> string -> string -> string
val correct: 'a -> ('b,'a) optResult
val unexpected: string -> 'a
val unreachable: string -> 'a

val if_ideal: (unit -> 'a) -> 'a -> 'a
val mem: 'a -> 'a list -> bool when 'a : equality
