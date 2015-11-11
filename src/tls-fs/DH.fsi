(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module DH

open Bytes
open DHGroup

open CoreKeys
open CommonDH

val leak  : parameters -> element -> secret -> bytes
val coerce: parameters -> element -> bytes -> secret

val serverGenDH: string -> DHDB.dhdb -> nat * nat -> DHDB.dhdb option * parameters * element * secret
val serverGenECDH: ECGroup.ec_curve -> DHDB.dhdb option * parameters * element * secret

val clientGenExp: parameters -> element -> (element * PMS.dhpms)
val serverExp: parameters -> element -> element -> secret -> PMS.dhpms 

val serialize: element -> bytes
