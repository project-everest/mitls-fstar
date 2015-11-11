module CoreCrypto.ECDH

open Platform.Bytes
open System
open CoreCrypto.Keys
open Org.BouncyCastle.Math
open Org.BouncyCastle.Crypto
open Org.BouncyCastle.Crypto.Digests
open Org.BouncyCastle.Crypto.Generators
open Org.BouncyCastle.Crypto.Signers
open Org.BouncyCastle.Crypto.Parameters
open Org.BouncyCastle.Math.EC
open Org.BouncyCastle.Security

let secp256r1 =
    let p256 = new BigInteger("115792089210356248762697446949407573530086143415290314195533631308867097853951", 10) in
    let curve =
        new FpCurve(p256,
                    new BigInteger("115792089210356248762697446949407573530086143415290314195533631308867097853948"),
                    new BigInteger("5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b", 16)) in
    let basepx = new FpFieldElement(p256, new BigInteger("6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296", 16)) in
    let basepy = new FpFieldElement(p256, new BigInteger("4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5", 16)) in
    let basep = new FpPoint(curve, basepx, basepy) in
    let dom = new ECDomainParameters(curve, basep, new BigInteger("115792089210356248762697446949407573529996955224135760342422259061068512044369")) in
    (curve, dom, basep)

let secp384r1 =
    let p384 = new BigInteger("39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319", 10) in
    let curve =
        new FpCurve(p384,
                    new BigInteger("39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112316"),
                    new BigInteger("b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef", 16)) in
    let basepx = new FpFieldElement(p384, new BigInteger("aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7", 16)) in
    let basepy = new FpFieldElement(p384, new BigInteger("3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f", 16)) in
    let basep = new FpPoint(curve, basepx, basepy) in
    let dom = new ECDomainParameters(curve, basep, new BigInteger("39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643")) in
    (curve, dom, basep)

let secp521r1 =
    let p384 = new BigInteger("6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151", 10)
    let curve =
        new FpCurve(p384,
                    new BigInteger("6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057148"),
                    new BigInteger("051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00", 16))
    let basepx = new FpFieldElement(p384, new BigInteger("0c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66", 16))
    let basepy = new FpFieldElement(p384, new BigInteger("11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650", 16))
    let basep = new FpPoint(curve, basepx, basepy)
    let dom = new ECDomainParameters(curve, basep, new BigInteger("6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449"))
    (curve, dom, basep)

let getprimecurve (ec:ecprime) =
    let p = new BigInteger(ec.ecp_prime, 10)
    let curve =
        new FpCurve(p,
                    new BigInteger(ec.ecp_a, 10),
                    new BigInteger(ec.ecp_b, 16))
    let basepx = new FpFieldElement(p, new BigInteger(ec.ecp_gx, 16))
    let basepy = new FpFieldElement(p, new BigInteger(ec.ecp_gy, 16))
    let basep = new FpPoint(curve, basepx, basepy)
    let dom = new ECDomainParameters(curve, basep, new BigInteger(ec.ecp_order))
    (curve, dom, basep)

let getcurve =
    function
    | EC_PRIME ecp -> getprimecurve ecp

let ptlength =
    function
    | EC_PRIME ecp -> ecp.ecp_bytelen

let bytes_to_bigint (b : bytes) = new BigInteger(1, cbytes b)
let bytes_of_bigint (b : BigInteger) (p:ecdhparams) =
    let rec pad (b:bytes) =
        function
        | n when n>0 -> pad ((abyte 0uy) @| b) (n-1)
        | _ -> b in
    let cl = ptlength p.curve in
    let b = abytes (b.ToByteArrayUnsigned()) in
    let l = length b in
    pad b (cl-l)

let gen_key (p:ecdhparams) : (ecdhskey * ecdhpkey) =
    let curve, ecdom, basep = getcurve p.curve
    let ecparam = new ECKeyGenerationParameters(ecdom, new SecureRandom())
    let gen = new ECKeyPairGenerator()
    gen.Init(ecparam)
    let keys = gen.GenerateKeyPair()
    let pk = (keys.Public :?> ECPublicKeyParameters)
    let sk = (keys.Private :?> ECPrivateKeyParameters)
    let x = pk.Q.X.ToBigInteger()
    let y = pk.Q.Y.ToBigInteger()
    let pub = { ecx = bytes_of_bigint x p; ecy = bytes_of_bigint y p; }
    let priv = abytes (sk.D.ToByteArrayUnsigned())
    (priv, pub)

let serialize (p:ecpoint) : bytes =
    abyte 4uy @| p.ecx @| p.ecy

let agreement (p:ecdhparams) (sk : ecdhskey) (pk : ecdhpkey) : bytes =
    let curve, ecdom, basep = getcurve p.curve
    let pubx = new FpFieldElement(curve.Q, bytes_to_bigint pk.ecx)
    let puby = new FpFieldElement(curve.Q, bytes_to_bigint pk.ecy)
    let pubP = new FpPoint(curve, pubx, puby)
    let mul = pubP.Multiply(bytes_to_bigint sk)
    bytes_of_bigint (mul.X.ToBigInteger()) p

let is_on_curve (p:ecdhparams) (e:ecpoint) : bool =
    try
        let curve, ecdom, basep = getcurve p.curve
        let X = bytes_to_bigint e.ecx
        let Y = bytes_to_bigint e.ecy
        if X.CompareTo(curve.Q) > 0 || Y.CompareTo(curve.Q) > 0 then false
        else
            (* ADL: TODO XXX Looks like this doesn't check that the point is on curve *)
            let P = curve.CreatePoint(X, Y, false)
            not P.IsInfinity
    with
        _ -> false
