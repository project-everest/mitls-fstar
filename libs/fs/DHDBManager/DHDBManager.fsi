(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module DHDBManager

open DHDB
open Bytes
open CoreKeys

// Constant confidence value for primality tests
val defaultDHPrimeConfidence : nat

// Throws exceptions in case of error
// (file not found, parsing error, unsafe parameters...)
val load_default_params : string -> dhdb -> nat * nat -> dhdb * dhparams
