(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module Date

type DateTime = DT of System.DateTime
type TimeSpan = TS of System.TimeSpan
let now () = DT (System.DateTime.Now)
let dawn = new System.DateTime(1970, 1, 1)
let secondsFromDawn () = (int32) (System.DateTime.UtcNow - dawn).TotalSeconds
let newTimeSpan d h m s = TS (new System.TimeSpan(d,h,m,s))
let addTimeSpan (DT(a)) (TS(b)) = DT (a + b)
let greaterDateTime (DT(a)) (DT(b)) = a > b
