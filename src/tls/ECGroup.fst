module ECGroup

open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open CoreCrypto
open TLSError
open TLSConstants

type params = CoreCrypto.ec_params

type key = k:CoreCrypto.ec_key
  {length k.ec_point.ecx = ec_bytelen k.ec_params.curve /\
   length k.ec_point.ecy = ec_bytelen k.ec_params.curve}

type share = CoreCrypto.ec_point

type group = CoreCrypto.ec_curve

type secret = bytes

type ec_all_curve =
  | EC_CORE of ec_curve
  | EC_UNKNOWN of (n:nat{repr_bytes n <= 2})
  | EC_EXPLICIT_PRIME
  | EC_EXPLICIT_BINARY

type point_format =
  | ECP_UNCOMPRESSED
  | ECP_UNKNOWN of (n:nat{repr_bytes n <= 1})

val params_of_group: group -> Tot params 
let params_of_group c = {curve = c; point_compression = false}

val share_of_key: key -> Tot (group * share)
let share_of_key k =
  k.ec_params.curve, k.ec_point

val keygen: group -> St key
let keygen g =
  let params = params_of_group g in
  ec_gen_key params

val dh_responder: ec_key -> St (key * secret)
let dh_responder gx =
  let params = gx.ec_params in
  let y = ec_gen_key params in
  let shared = ecdh_agreement y gx.ec_point in
  y, shared

val dh_initiator: x:ec_key{Some? x.ec_priv} -> ec_key -> St secret
let dh_initiator x gy =
  ecdh_agreement x gy.ec_point

