(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module MiHTTPInstanceDB

open Bytes
open MiHTTPChannel

val save    : channel -> unit
val restore : channelid -> channel option
