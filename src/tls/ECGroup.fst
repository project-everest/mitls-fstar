module ECGroup

open FStar.Bytes
open FStar.Error

open CoreCrypto
open TLSError
open Mem
open Parse

module CC = CoreCrypto
module LP = LowParse.SLow

type group = CC.ec_curve
type params = CC.ec_params

private type pre_keyshare g =
  | KS_CC of k:CC.ec_key {
    Some? k.ec_priv /\ k.ec_params.curve = g /\
    length k.ec_point.ecx = ec_bytelen g /\
    length k.ec_point.ecy = ec_bytelen g }
  | KS_X25519 of TLS.Curve25519.keyshare
  | KS_X448 of (pub:lbytes 56 * priv:lbytes 56)

// ADL do not use untagged union here!
// The ML Obj.t type is not compatible with CC extracted as --codegen-lib
type keyshare (g:group) =
  s:pre_keyshare g{(match g with
    | ECC_X25519 -> KS_X25519? s
    | ECC_X448 -> KS_X448? s
    | _ -> KS_CC? s)}

private type pre_share g =
  | S_CC of p:CC.ec_point{
     length p.ecx = ec_bytelen g /\
     length p.ecy = ec_bytelen g}
  | S_X25519 of TLS.Curve25519.point
  | S_X448 of lbytes 56

type share (g:group) =
  s:pre_share g{(match g with
    | ECC_X25519 -> S_X25519? s
    | ECC_X448 -> S_X448? s
    | _ -> S_CC? s)}

type secret (g:group) = bytes

type ec_all_curve =
  | EC_CORE of ec_curve
  | EC_UNKNOWN of (n:nat{repr_bytes n <= 2})
  | EC_EXPLICIT_PRIME
  | EC_EXPLICIT_BINARY

val params_of_group: group -> bool -> Tot params
let params_of_group c compression = {curve = c; point_compression = compression}

val pubshare: #g:group -> keyshare g -> Tot (share g)
let pubshare #g k =
  match g with
  | ECC_X25519 ->
    let KS_X25519 ks = k in S_X25519 (TLS.Curve25519.pubshare ks)
  | ECC_X448 ->
    let KS_X448 (p,s) = k in S_X448 p
  | _ ->
    let KS_CC ks = k in S_CC ks.ec_point

#reset-options "--using_facts_from '* -LowParse'"
val keygen: g:group -> ST (keyshare g)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
let keygen g =
  match g with
  | ECC_X25519 -> KS_X25519 (TLS.Curve25519.keygen ())
  | ECC_X448 ->
    let s = CoreCrypto.random 56 in
    let p = CoreCrypto.random 56 in
    KS_X448 (p, s)
  | _ ->
    let params = params_of_group g false in
    let s = ec_gen_key params in
    KS_CC s

val dh_initiator: #g:group -> gx:keyshare g -> gy:share g -> ST (secret g)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
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
#reset-options "--z3rlimit 50 --admit_smt_queries true"
val parse_curve: bytes -> Tot (option group)
let parse_curve b =
  if (length b < 1) then None else (
    let open Format.ECCurveType in  
    let open Format.NamedGroup in
    match ecCurveType_parser32 b with // <- parse_curve == ecCurveType_parser and-then named_group_parser
    | Some (Format.ECCurveType.NAMED_CURVE, _) -> 
      let ty, id = split b 1ul in
      match namedGroup_parser32 id with
      | Some (SECP256R1, _) -> Some CC.ECC_P256
      | Some (SECP384R1, _) -> Some CC.ECC_P384
      | Some (SECP521R1, _) -> Some CC.ECC_P521
      | Some (X25519, _   ) -> Some CC.ECC_X25519
      | Some (X448, _     ) -> Some CC.ECC_X448
      | _                   -> None
    | _ -> None)
#reset-options

val curve_id: group -> Tot (lbytes 2)
let curve_id g =
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

#reset-options "--using_facts_from '* -LowParse'"
val parse_point: g:group -> bytes -> Tot (option (share g))
let parse_point g b =
  // parser for flat bytes or uncompressedPointPepresentation
  match g with
  | ECC_X448 -> (
      let (p:LP.parser32 _) = LP.parse32_flbytes 56 56ul in
      match p b with
      | Some (bs, _) -> Some (S_X448 bs)
      | _ -> None)
  | ECC_X25519 -> (
      let (p:LP.parser32 _) = LP.parse32_flbytes 32 32ul in
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

val parse_partial: bytes -> Tot (result ((g:group & share g) * bytes))
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

(* Assumes uncompressed point format for now (04||ecx||ecy) *)
val serialize_point: #g:group -> e:share g -> Tot (b:bytes{length b <= 255})
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

val serialize: #g:group -> e:share g -> Tot (b:bytes{length b <= 259})
let serialize #g ecdh_Y =
  // Similar to parse_partial, we should rewrite this using serializer combinators
  let ty = abyte 3z in
  let id = curve_id g in
  let e = serialize_point ecdh_Y in
  lemma_repr_bytes_values (FStar.Bytes.length e);
  let ve = vlbytes 1 e in
  ty @| id @| ve
#reset-options

(* KB: older more general code below
let getParams (c : ec_curve) : ec_params =
    let rawcurve : ec_prime = match c with
    | ECC_P256 ->
        {
            ecp_prime = "115792089210356248762697446949407573530086143415290314195533631308867097853951";
            ecp_order = "115792089210356248762697446949407573529996955224135760342422259061068512044369";
            ecp_a = "115792089210356248762697446949407573530086143415290314195533631308867097853948"; // p-3
            ecp_b = "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b";
            ecp_gx = "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296";
            ecp_gy = "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5";
            ecp_bytelen = 32;
            ecp_id = twobytes (0z, 23z);
        }
    | ECC_P384 ->
        {
            ecp_prime = "39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319";
            ecp_order = "39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643";
            ecp_a = "39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112316"; // p-3
            ecp_b = "b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef";
            ecp_gx = "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7";
            ecp_gy = "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f";
            ecp_bytelen = 48;
            ecp_id = twobytes (0z, 24z);
        }
    | ECC_P521 ->
        {
            ecp_prime = "6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151";
            ecp_order = "6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449";
            ecp_a = "6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057148"; // p-3
            ecp_b = "051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00";
            ecp_gx = "0c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66";
            ecp_gy = "11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650";
            ecp_bytelen = 66;
            ecp_id = twobytes (0z, 25z);
        }
    in { curve = EC_PRIME rawcurve; point_compression = false; }
*)
