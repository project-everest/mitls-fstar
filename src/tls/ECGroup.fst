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

val parse_curve: bytes -> Tot (option params)
let parse_curve b =
  if length b = 3 then
    let (ty, id) = split b 1 in
    if cbyte ty = 3z then
      match cbyte2 id with
      | (0z, 23z) -> Some (params_of_group ECC_P256)
      | (0z, 24z) -> Some (params_of_group ECC_P384)
      | (0z, 25z) -> Some (params_of_group ECC_P521)
      | _ -> None
    else None
  else None

val curve_id: params -> Tot (lbytes 2)
let curve_id p =
  abyte2 (match p.curve with
  | ECC_P256 -> (0z, 23z)
  | ECC_P384 -> (0z, 24z)
  | ECC_P521 -> (0z, 25z))

val parse_point: params -> bytes -> Tot (option share)
let parse_point p b =
  let clen = ec_bytelen p.curve in 
  if length b = (op_Multiply 2 clen) + 1 then
    let (et, ecxy) = split b 1 in
    match cbyte et with
    | 4z ->
      let (x,y) = split ecxy clen in
      let e = {ecx = x; ecy = y;} in
      if CoreCrypto.ec_is_on_curve p e then Some e else None
    |_ -> None
  else None

val parse_partial: bytes -> Tot (TLSError.result ( key * bytes ))
let parse_partial payload = 
    if length payload >= 7 then
      let (curve, point) = split payload 3 in
      match parse_curve curve with
      | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Unsupported curve")
      | Some(ecp) ->
        match vlsplit 1 point with
        | Error(z) -> Error(z)
        | Correct(rawpoint, rem) ->
           match parse_point ecp rawpoint with
           | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ("Invalid EC point received:"^(Platform.Bytes.print_bytes rawpoint)))
           | Some p -> Correct ({ec_params = ecp; ec_point = p; ec_priv = None},rem)
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

open FStar.Mul

(* Assumes uncompressed point format for now (04||ecx||ecy) *) 
val serialize_point: p:params 
  -> e:share{length e.ecx = ec_bytelen p.curve /\ length e.ecy = ec_bytelen p.curve}
  -> Tot (b:bytes{length b = 2*ec_bytelen p.curve + 1})
let serialize_point p e =
  let pc = abyte 4z in
  let x = pc @| e.ecx @| e.ecy in
  x

val serialize: p:params
  -> e:share{length e.ecx = ec_bytelen p.curve /\ length e.ecy = ec_bytelen p.curve}
  -> Tot (b:bytes{length b = 2*ec_bytelen p.curve + 5})
let serialize ecp ecdh_Y =
  let ty = abyte 3z in
  let id = curve_id ecp in
  let e = serialize_point ecp ecdh_Y in
  lemma_repr_bytes_values (length e);
  let ve = vlbytes 1 e in
  ty @| id @| ve


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
            ecp_id = abyte2 (0z, 23z);
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
            ecp_id = abyte2 (0z, 24z);
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
            ecp_id = abyte2 (0z, 25z);
        }
    in { curve = EC_PRIME rawcurve; point_compression = false; }
*)
