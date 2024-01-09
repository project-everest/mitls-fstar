(** Expansion of secrets into expanded secrets *)
module MiTLS.KDF.Salt.ODH
open MiTLS

open FStar.Heap
open FStar.HyperStack
open FStar.Bytes
open FStar.Error

open MiTLS.Mem
open MiTLS.TLSError
open MiTLS.TLSConstants
open MiTLS.TLSInfo

module HS = FStar.HyperStack

(* Source index is a secret index *)
type id = secretId

type state (i:id) =
  | State: r:rgn -> state i
