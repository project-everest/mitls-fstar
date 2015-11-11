(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module CoreACiphers
open Bytes

open Org.BouncyCastle.Math
open Org.BouncyCastle.Crypto
open Org.BouncyCastle.Security
open Org.BouncyCastle.Crypto.Generators
open Org.BouncyCastle.Crypto.Encodings
open Org.BouncyCastle.Crypto.Engines
open Org.BouncyCastle.Crypto.Parameters

type modulus  = bytes
type exponent = bytes

type sk = RSASKey of CoreKeys.rsaskey
type pk = RSAPKey of CoreKeys.rsapkey

type plain = bytes
type ctxt  = bytes

//needs to be peer-reviewed and pen-tested
let gen_key () : sk * pk =
    let kparams  = new RsaKeyGenerationParameters(BigInteger("65537"),new SecureRandom(), 2048, 80) in
    let kgen     = new RsaKeyPairGenerator() in
        kgen.Init(kparams);
        let kpair = kgen.GenerateKeyPair() in
        let pkey  = (kpair.Public  :?> RsaKeyParameters ) in
        let skey  = (kpair.Private :?> RsaPrivateCrtKeyParameters) in
            (RSASKey(abytes (skey.Modulus.ToByteArrayUnsigned()), abytes(skey.Exponent.ToByteArrayUnsigned())), 
             RSAPKey(abytes (pkey.Modulus.ToByteArrayUnsigned()), abytes(pkey.Exponent.ToByteArrayUnsigned()))
            )

let encrypt_pkcs1 (RSAPKey (m, e)) (plain : plain) =
    let m, e   = new BigInteger(1, cbytes m), 
                 new BigInteger(1, cbytes e) in
    let engine = new RsaEngine() in
    let engine = new Pkcs1Encoding(engine) in

    engine.Init(true, new RsaKeyParameters(false, m, e))
    abytes (engine.ProcessBlock(cbytes plain, 0, length plain))

let decrypt_pkcs1 (RSASKey (m, e)) (ctxt : ctxt) =
    let m, e   = new BigInteger(1, cbytes m), 
                 new BigInteger(1, cbytes e) in
    let engine = new RsaEngine() in
    let engine = new Pkcs1Encoding(engine) in

    try
        engine.Init(false, new RsaKeyParameters(true, m, e))
        Some (abytes (engine.ProcessBlock(cbytes ctxt, 0, length ctxt)))
    with :? InvalidCipherTextException ->
        None
