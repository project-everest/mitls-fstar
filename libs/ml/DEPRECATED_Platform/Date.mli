type dateTime
type timeSpan
val now: unit -> dateTime
val secondsFromDawn: unit -> int
val newTimeSpan: int -> int -> int -> int -> timeSpan
val addTimeSpan: dateTime -> timeSpan -> dateTime
val greaterDateTime: dateTime -> dateTime -> bool
