(** Expansion of secrets into expanded secrets *)
module KDF.Salt.ODH

open FStar.Heap

open FStar.HyperStack

open FStar.Bytes
open FSTar.Error
open TLSError
open TLSConstants
open TLSInfo

module MM = FStar.Monotonic.Map


module HS = FStar.HyperStack

(* Source index is a secret index *)
type id = secretId

type state (i:id) =
  | State: r:rgn -> state i
