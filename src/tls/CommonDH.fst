(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
﻿module CommonDH

open Platform.Bytes
open Platform.Error
open CoreCrypto
open TLSConstants
open TLSError

type group =
  | FFDH of DHGroup.group
  | ECDH of ECGroup.group

type keyshare (g:group) =
  (match g with
  | FFDH dhg -> DHGroup.keyshare dhg
  | ECDH ecg -> ECGroup.keyshare ecg)

type share (g:group) =
  (match g with
  | FFDH dhg -> DHGroup.share dhg
  | ECDH ecg -> ECGroup.share ecg)

type secret (g:group) =
  (match g with
  | FFDH dhg -> DHGroup.secret dhg
  | ECDH ecg -> ECGroup.secret ecg)

val group_of_namedGroup: namedGroup -> Tot (option group)
let group_of_namedGroup g =
  match g with
  | SEC ec    -> Some (ECDH ec)
  | FFDHE dhe -> Some (FFDH (DHGroup.Named dhe))
  | _ -> None

val pubshare: #g:group -> keyshare g -> Tot (share g)
let pubshare #g ks =
  match g with
  | FFDH dhg -> DHGroup.pubshare #dhg ks
  | ECDH ecg -> ECGroup.pubshare #ecg ks

val default_group: group
let default_group = ECDH (CoreCrypto.ECC_P256)

val keygen: g:group -> St (keyshare g)
let keygen = function
  | FFDH g -> DHGroup.keygen g
  | ECDH g -> ECGroup.keygen g

val dh_responder: #g:group -> share g -> St (keyshare g * secret g)
let dh_responder #g gx = match g with
  | FFDH g -> DHGroup.dh_responder #g gx
  | ECDH g -> ECGroup.dh_responder #g gx

val dh_initiator: #g:group -> keyshare g -> share g -> St (secret g)
let dh_initiator #g gx gy =
  match g with
  | FFDH g -> DHGroup.dh_initiator #g gx gy
  | ECDH g -> ECGroup.dh_initiator #g gx gy

// Serialize in KeyExchange message format
val serialize: #g:group -> share g -> Tot bytes
let serialize #g s =
  match g with
  | FFDH g -> DHGroup.serialize #g s
  | ECDH g -> ECGroup.serialize #g s

val parse_partial: bool -> bytes -> Tot (result ((g:group & share g) * bytes))
let parse_partial ec p =
  if ec then
    begin
    match ECGroup.parse_partial p with
    | Correct((|g , s|), rem) -> Correct ((| ECDH g, s |), rem)
    | Error z -> Error z
    end
  else
    begin
    match DHGroup.parse_partial p with
    | Correct((|g, s|), rem) -> Correct ((| FFDH g, s |), rem)
    | Error z -> Error z
    end

// Serialize for keyShare extension
val serialize_raw: #g:group -> share g -> Tot bytes
let serialize_raw #g s =
  match g with
  | FFDH g ->
    let dhp = DHGroup.params_of_group g in
    DHGroup.serialize_public #g s (length dhp.dh_p)
  | ECDH g -> ECGroup.serialize_point #g s

val parse: g:group -> bytes -> Tot (option (share g))
let parse g x =
  match g with
  | ECDH g -> ECGroup.parse_point g x
  | FFDH g ->
    let dhp = DHGroup.params_of_group g in
    if length x = length dhp.dh_p then Some x
    else None

(*
val key_params: key -> Tot params
let key_params k =
  match k with
  | FFKey k -> FFP k.dh_params
  | ECKey k -> ECP k.ec_params

  let checkParams dhdb minSize (p:parameters) =
    match p with
    | DHP_P(dhp) ->
      begin match dhdb with
        | None -> Error (TLSError.AD_internal_error, "Not possible")
        | Some db ->
            (match DHGroup.checkParams db minSize dhp.dh_p dhp.dh_g with
            | Error(x) -> Error(x)
            | Correct(db, dhp) -> Correct(Some db, p))
      end
    | DHP_EC(ecp) -> correct (None, p)

let checkElement (p:parameters) (e:element) : option element  =
    match (p, e.dhe_p, e.dhe_ec) with
    | DHP_P(dhp), Some b, None ->
      begin match DHGroup.checkElement dhp b with
        | None -> None
        | Some x -> Some ({dhe_nil with dhe_p = Some x})
      end
    | DHP_EC(ecp), None, Some p ->
      begin match ECGroup.checkElement ecp p with
        | None -> None
        | Some p -> Some ({dhe_nil with dhe_ec = Some p})
      end
    | _ -> failwith "impossible"
*)
