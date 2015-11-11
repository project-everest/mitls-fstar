(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module MiHTTPUtils

val split_and_strip: char -> int -> string -> string list
val parse_date : string -> Date.DateTime option
