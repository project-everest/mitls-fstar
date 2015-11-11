type dateTime = DT of float
type timeSpan = TS of float
let now () = DT (Unix.gettimeofday())
let secondsFromDawn () = int_of_float (Unix.time())
let newTimeSpan d h m s = TS (((((float_of_int d) *. 24.0) +. (float_of_int h)) *. 60.0 +. (float_of_int m)) *. 60.0 +. (float_of_int s))
let addTimeSpan (DT(a)) (TS(b)) = DT (a +. b)
let greaterDateTime (DT(a)) (DT(b)) = a > b