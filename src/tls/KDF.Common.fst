(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
(**
 Shared state for secret expansion and salt expansion
 This file exists to break a cyclic module dependency:
 KDF.Salt.* operates on the same secrets as KDF.Expand
 but both cannot be implemented in a single module because
 of the cyclic dependency.
 *)
module KDF.Common

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSInfo

module MM = MonotoneMap
module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

(* Source index is a secret index *)
type id = secretId

(* The kind of expansion, either salt of expanded secret *)
type expand_kind (i:id) =
  | ExpandSalt: expand_kind i
  | ExpandSecret:
     log: hashed_log ->
     li: logInfo{
         (EarlySecretID? i ==> LogInfo_CH? li) /\
         (HandshakeSecretID? i ==> LogInfo_SH? li) /\
         (ApplicationSecretID? i ==> LogInfo_SF? li) /\
         log_info li log
       } ->
     expand_kind i

// Conceptually, this is either a KDF.Salt.X.state i or KDF.Expand.state i
// However, the table stores actual key values, and the proper interface for
// accessing it is spread between KDF.Salt.X and KDF.Expand
type extracted_secret (#i:id) (x:expand_kind i) =
  lbytes (Hashing.Spec.tagLen (secretId_hash i))

type expand_log (i:id) (r:rgn) =
  (if Flags.ideal_KEF then
    MM.t r (expand_kind i) (extracted_secret #i) (fun _ -> True)
  else
    unit)

type state (i:id) =
  | State:
    r:rgn ->
    log: expand_log i r ->
    state i

let kdf_region:rgn = new_region tls_tables_region
type kdf_instance_table =
  (if Flags.ideal_KEF then
    MM.t kdf_region id state (fun _ -> True)
  else
    unit)

let kdf_instances : kdf_instance_table =
  (if Flags.ideal_KEF then
    MM.alloc #kdf_region #id #state #(fun _ -> True)
  else
    ())
