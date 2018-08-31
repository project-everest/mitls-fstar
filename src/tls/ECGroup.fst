module ECGroup

open FStar.Bytes
open FStar.Error
open CoreCrypto

open TLSError
open Mem
open Parse

module CC = CoreCrypto
module LP = LowParse.SLow.Base

type params = CC.ec_params

type ec_all_curve =
  | EC_CORE of ec_curve
  | EC_UNKNOWN of (n:nat{repr_bytes n <= 2})
  | EC_EXPLICIT_PRIME
  | EC_EXPLICIT_BINARY

val params_of_group: group -> bool -> Tot params
let params_of_group c compression = {curve = c; point_compression = compression}

let pubshare #g k =
  match g with
  | ECC_X25519 ->
    let KS_X25519 ks = k in S_X25519 (TLS.Curve25519.pubshare ks)
  | ECC_X448 ->
    let KS_X448 (p,s) = k in S_X448 p
  | _ ->
    let KS_CC ks = k in S_CC ks.ec_point

#reset-options "--using_facts_from '* -LowParse'"
let keygen g =
  match g with
  | ECC_X25519 -> KS_X25519 (TLS.Curve25519.keygen ())
  | ECC_X448 ->
    let s = Random.sample32 56ul in
    let p = Random.sample32 56ul in
    KS_X448 (p, s)
  | _ ->
    let params = params_of_group g false in
    let s = ec_gen_key params in
    KS_CC s

let dh_initiator #g gx gy =
  match g with
  | ECC_X25519 ->
    let KS_X25519 (p,s) = gx in
    let S_X25519 gy = gy in
    TLS.Curve25519.mul s gy
  | ECC_X448 ->
    let KS_X448 (p,s) = gx in
    s // TODO BEWARE
  | _ ->
    let KS_CC gx = gx in
    let S_CC gy = gy in
    ecdh_agreement gx gy
#reset-options

// cwinter: parse_curve, parse_point, and parse_partial really describe
// one parser for one datatype of the shape
// { ECCurveType, ECNamedGroup (or NamedCurve), UncompressedPointRepresentation or raw bytes }
// but I can't figure out whether that type has a name in the RFCs
// (I don't think so, because 'namedcurve' in ECParameters only contains the 
// curve name, no further parameters).
val parse_curve: bytes -> Tot (option group)
let parse_curve b =
  if (length b < 1) then None else (
    let open Format.ECCurveType in  
    let open Format.NamedGroup in
    match ecCurveType_parser32 b with // <- parse_curve == ecCurveType_parser and-then named_group_parser
    | Some (Format.ECCurveType.NAMED_CURVE, _) -> 
      let ty, id = split b 1ul in
      (match namedGroup_parser32 id with
       | Some (SECP256R1, _) -> Some CC.ECC_P256
       | Some (SECP384R1, _) -> Some CC.ECC_P384
       | Some (SECP521R1, _) -> Some CC.ECC_P521
       | Some (X25519, _   ) -> Some CC.ECC_X25519
       | Some (X448, _     ) -> Some CC.ECC_X448
       | _                   -> None)
    | _ -> None)

#reset-options "--using_facts_from '* -LowParse'"
let parse_point g b =
  // parser for flat bytes or uncompressedPointPepresentation
  match g with
  | ECC_X448 -> (
      let (p:LP.parser32 _) = LowParse.SLow.parse32_flbytes 56 56ul in
      match p b with
      | Some (bs, _) -> Some (S_X448 bs)
      | _ -> None)
  | ECC_X25519 -> (
      let (p:LP.parser32 _) = LowParse.SLow.parse32_flbytes 32 32ul in
      match p b with
      | Some (bs, _) -> Some (S_X25519 bs)
      | _ -> None)
  | _ ->
      let open Format.UncompressedPointRepresentation in
      let cl = UInt32.uint_to_t (ec_bytelen g) in
      match (uncompressedPointRepresentation_parser32 cl) b with
      | Some (ucpr, _) -> 
          let e = { ecx = ucpr.x; ecy = ucpr.y } in
          if CoreCrypto.ec_is_on_curve (params_of_group g false) e then
            Some (S_CC e)
          else None
    | _ -> None

let parse_partial payload =
    // This really means:
    // ecCurveType_parser and-then 
    // namedGroup_parser (or NamedCurve) and-then
    // ( uncompressedPointRepresentation_parser or flbytes_parser )
    // We should rewrite it using parser combinators
    if length payload >= 7 then
      let (curve, point) = split payload 3ul in
      match parse_curve curve with
      | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Unsupported curve")
      | Some(ecp) ->
        match vlsplit 1 point with
        | Error(z) -> Error(z)
        | Correct(x) ->
           let rawpoint, rem = x in
           match parse_point ecp rawpoint with
           | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ("Invalid EC point received:"^(FStar.Bytes.print_bytes rawpoint)))
           | Some p -> Correct ((| ecp, p |),rem)
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

open FStar.Mul

#reset-options "--using_facts_from '* -LowParse'"
(* Assumes uncompressed point format for now (04||ecx||ecy) *)
let serialize_point #g s =
  match g with
  | ECC_X25519 ->
    let S_X25519 p = s in     
    let r = LowParse.SLow.serialize32_flbytes (ec_bytelen g) p in
    assume (length r = ec_bytelen g);
    r
  | ECC_X448 ->
    let S_X448 p = s in    
    let r = LowParse.SLow.serialize32_flbytes (ec_bytelen g) p in
    assume (length r = ec_bytelen g);
    r
  | _ ->
    let S_CC e = s in
    let open Format.UncompressedPointRepresentation in    
    let l = length e.ecx in
    let (l32:coordinate_length_type) = UInt32.uint_to_t l in
    let (ucp:uncompressedPointRepresentation l32) = { legacy_form = 4uy; x = e.ecx; y = e.ecy } in
    let x = (uncompressedPointRepresentation_serializer32 l32) ucp in
    assume (length x = 2 * (ec_bytelen g) + 1);
    x

let curve_id g : Tot (lbytes 2) =
  let open Format.NamedGroup in
  let r = namedGroup_serializer32 ( // <- curve_id == namedGroup_serializer
    match g with
    | ECC_P256   -> SECP256R1
    | ECC_P384   -> SECP384R1
    | ECC_P521   -> SECP521R1
    | ECC_X25519 -> X25519
    | ECC_X448   -> X448) in
  assume (length r = 2);
  r

let serialize #g ecdh_Y =
  // Similar to parse_partial, we should rewrite this using serializer combinators
  let ty = abyte 3z in
  let id = curve_id g in
  let e = serialize_point ecdh_Y in
  lemma_repr_bytes_values (FStar.Bytes.length e);
  assert (repr_bytes (length e) <= 1);
  let ve = vlbytes 1 e in
  ty @| id @| ve
