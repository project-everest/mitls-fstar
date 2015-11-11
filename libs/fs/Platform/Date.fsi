(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Date

type DateTime
type TimeSpan
val now: unit -> DateTime
val secondsFromDawn: unit -> int
val newTimeSpan: int -> int -> int -> int -> TimeSpan
val addTimeSpan: DateTime -> TimeSpan -> DateTime
val greaterDateTime: DateTime -> DateTime -> bool
