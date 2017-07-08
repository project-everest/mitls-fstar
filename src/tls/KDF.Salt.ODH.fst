(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
(** Expansion of secrets into expanded secrets *)
module KDF.Salt.ODH

open Mem

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSInfo

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = Mem
module HS = Mem

(* Source index is a secret index *)
type id = secretId

type state (i:id) =
  | State: r:rgn -> state i
