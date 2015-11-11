(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module MiHTTPWorker

type lock

val create_lock : unit -> lock

val async    : ('a -> unit) -> 'a -> unit
val critical : lock -> ('a -> 'b) -> 'a -> 'b
