(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module CoreDH

open Bytes
open Error

(* ------------------------------------------------------------------------ *)
open System
open System.IO
open System.Text

open Org.BouncyCastle.Math
open Org.BouncyCastle.Security
open Org.BouncyCastle.Crypto.Generators
open Org.BouncyCastle.Crypto.Parameters
open Org.BouncyCastle.Utilities.IO.Pem
open Org.BouncyCastle.Asn1

(* ------------------------------------------------------------------------ *)
open CoreKeys

let defaultPQMinLength = (1024, 160)

(* ------------------------------------------------------------------------ *)
let check_element dhp (ebytes:bytes) =
    let p   = new BigInteger(1, cbytes dhp.dhp)
    let e   = new BigInteger(1, cbytes ebytes)
    let pm1 = p.Subtract(BigInteger.One)
    // check e in [2,p-2]
    if ((e.CompareTo BigInteger.One) > 0) && ((e.CompareTo pm1) < 0) then
        if dhp.safe_prime then
            true
        else
            let q = new BigInteger(1, cbytes dhp.dhq)
            let r = e.ModPow(q, p)
            // For OpenSSL-generated parameters order(g) = 2q, so e^q mod p = p-1
            r.Equals(BigInteger.One) || r.Equals(pm1)
    else
        false

let check_p_g conf minPl minQl pbytes gbytes =
    let p = new BigInteger(1, cbytes pbytes)
    let g = new BigInteger(1, cbytes gbytes)
    let pm1 = p.Subtract(BigInteger.One)
    if (g.CompareTo BigInteger.One) > 0 && (g.CompareTo pm1) < 0 then
        let q = pm1.Divide(BigInteger.Two) in
        if minPl <= p.BitLength && minQl <= q.BitLength then
            if p.IsProbablePrime(conf) && q.IsProbablePrime(conf) then
                correct (abytes (q.ToByteArrayUnsigned()))
            else
                Error (perror __SOURCE_FILE__ __LINE__ "Group with unknown order")
        else
            Error(perror __SOURCE_FILE__ __LINE__ "Subgroup too small")
    else
        Error (perror __SOURCE_FILE__ __LINE__ "Group with small order")

let check_p_g_q conf minPl minQl pbytes gbytes qbytes =
    let p = new BigInteger(1, cbytes pbytes)
    let q = new BigInteger(1, cbytes qbytes)
    let pm1 = p.Subtract(BigInteger.One) in
    let q' = pm1.Divide(BigInteger.Two) in
    if q.Equals(q') then
        // Potentially a safe prime, do the light check
        match check_p_g conf minPl minQl pbytes gbytes with
        | Error(x) -> Error(x)
        | Correct(_) -> correct(true)
    else
        if minPl <= p.BitLength && minQl <= q.BitLength then
            if p.IsProbablePrime(conf) && q.IsProbablePrime(conf) then
                if check_element
                    {dhp=pbytes; dhg=gbytes; dhq=qbytes; safe_prime=false}
                    gbytes then
                    correct(false)
                else
                    Error (perror __SOURCE_FILE__ __LINE__ "Group with small order")
            else
                Error (perror __SOURCE_FILE__ __LINE__ "Group with unknown order")
        else
            Error(perror __SOURCE_FILE__ __LINE__ "Subgroup too small")

let check_params dhdb conf minSize (pbytes:bytes) (gbytes:bytes) =
    match DHDB.select dhdb (pbytes, gbytes) with
    | None -> // unknown group
        let (minPl,minQl) = minSize in
        match check_p_g conf minPl minQl pbytes gbytes with
        | Error(x) -> Error(x)
        | Correct(qbytes) ->
            let dhdb = DHDB.insert dhdb (pbytes, gbytes) (qbytes, true) in
            correct (dhdb,{dhp = pbytes; dhg = gbytes; dhq = qbytes; safe_prime = true})
    | Some(qbytes,safe_prime) -> // known group
        let p = new BigInteger(1, cbytes pbytes) in
        let q = new BigInteger(1, cbytes qbytes) in
        let (minPl,minQl) = minSize in
        if p.BitLength < minPl || q.BitLength < minQl then
            Error(perror __SOURCE_FILE__ __LINE__ "Subgroup too small")
        else
            correct (dhdb,{dhp = pbytes; dhg = gbytes ; dhq = qbytes ; safe_prime = safe_prime})


(* ------------------------------------------------------------------------ *)
let gen_key_int dhparams =
    let kparams  = new DHKeyGenerationParameters(new SecureRandom(), dhparams) in
    let kgen     = new DHKeyPairGenerator() in
    kgen.Init(kparams);
    let kpair = kgen.GenerateKeyPair() in
    let pkey  = (kpair.Public  :?> DHPublicKeyParameters ) in
    let skey  = (kpair.Private :?> DHPrivateKeyParameters) in
    (abytes (skey.X.ToByteArrayUnsigned()), abytes (pkey.Y.ToByteArrayUnsigned()))

let gen_key dhp: dhskey * dhpkey =
    // TODO: Other BC constructors for DHParameters could provide even better performances.
    let dhparams = new DHParameters(new BigInteger(1, cbytes dhp.dhp), new BigInteger(1, cbytes dhp.dhg), new BigInteger(1, cbytes dhp.dhq)) in
    gen_key_int dhparams

let gen_key_pg p g =
    let dhparams = new DHParameters(new BigInteger(1, cbytes p), new BigInteger(1, cbytes g)) in
    gen_key_int dhparams

(* ------------------------------------------------------------------------ *)
let agreement p (x : dhskey) (y : dhpkey) : bytes =
    let x = new BigInteger(1, cbytes x) in
    let y = new BigInteger(1, cbytes y) in
    let p = new BigInteger(1, cbytes p) in
        abytes (y.ModPow(x, p).ToByteArrayUnsigned())
