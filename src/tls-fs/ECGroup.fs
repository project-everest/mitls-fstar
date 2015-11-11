#light "off"

module ECGroup

open Bytes
open CoreKeys
open Error
open TLSError
open TLSConstants

type ec_curve =
| ECC_P256
| ECC_P384
| ECC_P521

type ec_all_curve =
| EC_CORE of ec_curve
| EC_UNKNOWN of int
| EC_EXPLICIT_PRIME
| EC_EXPLICIT_BINARY

type point_format =
| ECP_UNCOMPRESSED
| ECP_UNKNOWN of int

type point = ecpoint

let getParams (c : ec_curve) : ecdhparams =
    let rawcurve : ecprime = match c with
    | ECC_P256 ->
        {
            ecp_prime = "115792089210356248762697446949407573530086143415290314195533631308867097853951";
            ecp_order = "115792089210356248762697446949407573529996955224135760342422259061068512044369";
            ecp_a = "115792089210356248762697446949407573530086143415290314195533631308867097853948"; // p-3
            ecp_b = "5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b";
            ecp_gx = "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296";
            ecp_gy = "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5";
            ecp_bytelen = 32;
            ecp_id = abyte2 (0uy, 23uy);
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
            ecp_id = abyte2 (0uy, 24uy);
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
            ecp_id = abyte2 (0uy, 25uy);
        }
    in { curve = EC_PRIME rawcurve; compression = false; }

let parse_curve (b : bytes) :  ecdhparams option =
    if length b = 3 then
        let (ty, id) = split b 1 in
        if cbyte ty = 3uy then
            match cbyte2 id with
            | (0uy, 23uy) -> Some (getParams (ECC_P256))
            | (0uy, 24uy) -> Some (getParams (ECC_P384))
            | (0uy, 25uy) -> Some (getParams (ECC_P521))
            | _ -> None
        else None
    else None

let curve_id (p:ecdhparams) : bytes =
    match p.curve with
    | EC_PRIME c -> c.ecp_id

(* ADL: Stub for supporting more point format options *)
let serialize_point (p:ecdhparams) (e:point) =
    vlbytes 1 (CoreECDH.serialize e)

let parse_point (p:ecdhparams) (b:bytes) :  point option =
    let clen = match p.curve with EC_PRIME c -> c.ecp_bytelen in
    if length b = 2*clen + 1 then
        let (et, r) = split b 1 in
        match cbyte et with
        | 4uy ->
            let (a,b) = split r clen in
            let e = {ecx = a; ecy = b;} in
            if CoreECDH.is_on_curve p e then Some e else None
        |_ -> None
    else
        None

(* TODO *)
let checkElement (p:ecdhparams) (b:point): option<point> =
    Some b
