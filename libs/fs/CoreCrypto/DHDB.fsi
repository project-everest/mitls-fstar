(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module DHDB

open Bytes

// p, g, q, true  => prime(p) /\ prime(q) /\ g^q mod p = 1 /\ p = 2*q + 1
// p, g, q, false => prime(p) /\ prime(q) /\ g^q mod p = 1 /\ ?j. p = j*q + 1 /\ length(q) >= threshold
type Key   = bytes * bytes // p, g
type Value = bytes * bool  // q, safe_prime?

type dhdb

val defaultFileName: string
val defaultDHPrimeConfidence: int

val create: string -> dhdb
val select: dhdb -> Key -> Value option
val insert: dhdb -> Key -> Value -> dhdb
val remove: dhdb -> Key -> dhdb
val keys  : dhdb -> Key list
val merge : dhdb -> string -> dhdb
