(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
(** Expansion of secrets into expanded secrets *)
module KDF.Expand

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

assume val ideal_Expand : bool

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

type extracted_secret (#i:id) (x:expand_kind i) =
  lbytes (Hashing.Spec.tagLen (secretId_hash i))

type expand_log (i:id) (r:rgn) =
  (if ideal_Expand then
    MM.t r (expand_kind i) extracted_secret (fun _ -> True)
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
