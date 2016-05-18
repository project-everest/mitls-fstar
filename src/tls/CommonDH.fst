module CommonDH

open Platform.Bytes
open Platform.Error
open CoreCrypto
open TLSConstants

type group =
  | FFDH of DHGroup.group
  | ECDH of ECGroup.group

type params =
  | FFP of DHGroup.params
  | ECP of ECGroup.params

type key = 
  | FFKey of DHGroup.key
  | ECKey of ECGroup.key

type share =
  | FFShare of DHGroup.group * DHGroup.share
  | ECShare of ECGroup.group * ECGroup.share

type secret = bytes

val group_of_namedGroup: namedGroup -> Tot (option group)
let group_of_namedGroup g =
  match g with
  | SEC ec    -> Some (ECDH ec) 
  | FFDHE dhe -> Some (FFDH (DHGroup.Named dhe))
  | _ -> None

val same_group: share -> share -> Tot bool
let same_group a b = match a, b with
  | FFShare (g1, _), FFShare(g2, _) -> g1=g2
  | ECShare (g1, _), ECShare(g2, _) -> g1=g2
  | _ -> false

val default_group: group
let default_group = FFDH (DHGroup.Named FFDHE2048)

val keygen: group -> Tot key
let keygen = function
  | FFDH g -> FFKey (DHGroup.keygen g)
  | ECDH g -> ECKey (ECGroup.keygen g)

val dh_responder: key -> Tot (key * secret)
let dh_responder = function
  | FFKey gx -> 
    let y, shared = DHGroup.dh_responder gx in
    FFKey y, shared
  | ECKey gx -> 
    let y, shared = ECGroup.dh_responder gx in
    ECKey y, shared

val dh_initiator: key -> key -> Tot secret
let dh_initiator x gy =
  match x, gy with
  | FFKey x, FFKey gy -> DHGroup.dh_initiator x gy
  | ECKey x, ECKey gy -> ECGroup.dh_initiator x gy
  | _, _ -> empty_bytes (* TODO: add refinement/index to rule out cross cases *)


// Serialize in KeyExchange message format
val serialize: key -> Tot bytes
let serialize k = 
  match k with
  | FFKey k -> DHGroup.serialize k.dh_params k.dh_public
  | ECKey k -> ECGroup.serialize k.ec_params k.ec_point

val parse_partial: bytes -> bool -> Tot (TLSError.result (key * bytes)) 
let parse_partial p ec = 
    if ec then 	 
      (match ECGroup.parse_partial p with
       | Correct(eck,rem) -> 
	 Correct (ECKey eck, rem)
       | Error z -> Error z)
    else 
      (match DHGroup.parse_partial p with
       | Correct(dhk,rem) -> 	   
         Correct (FFKey dhk, rem)
       | Error z -> Error z)

        
  
// Serialize for keyShare extension
val serialize_raw: key -> Tot bytes
let serialize_raw = function
  | ECKey k -> ECGroup.serialize_point k.ec_params k.ec_point
  | FFKey k -> DHGroup.serialize_public k.dh_public

val parse: params -> bytes -> Tot (option key)
let parse p x =
  match p with
  | ECP p -> (match ECGroup.parse_point p x with | Some eck -> Some (ECKey ({ec_params=p; ec_point=eck; ec_priv=None;})) | None -> None)
  | FFP p -> (match DHGroup.parse_public x with
    | Correct r -> Some (FFKey ({dh_params = p; dh_public = r; dh_private = None;}))
    | _ -> None)

val key_params: key -> Tot params
let key_params k =
  match k with
  | FFKey k -> FFP k.dh_params
  | ECKey k -> ECP k.ec_params

(*
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
