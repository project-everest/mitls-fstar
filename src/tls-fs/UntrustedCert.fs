(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module UntrustedCert

(* ------------------------------------------------------------------------ *)
open System.Text
open System.Collections.Generic
open System.Security.Cryptography
open System.Security.Cryptography.X509Certificates

open Bytes
open TLSConstants
open Error
open TLSError

let OID_RSAEncryption           = "1.2.840.113549.1.1.1"
let OID_MD5WithRSAEncryption    = "1.2.840.113549.1.1.4"
let OID_SHAWithRSAEncryption    = "1.2.840.113549.1.1.5"
let OID_SHA256WithRSAEncryption = "1.2.840.113549.1.1.11"
let OID_DSASignatureKey         = "1.2.840.10040.4.1"
let OID_DSASignature            = "1.2.840.10040.4.3"

(* ------------------------------------------------------------------------ *)
type X509Certificate2 = | C of System.Security.Cryptography.X509Certificates.X509Certificate2
type hint = string
type cert = bytes
type chain = list<cert>

let x509_to_public_key (C x509 : X509Certificate2) =
    match x509.GetKeyAlgorithm() with
    | x when x = OID_RSAEncryption ->
        (try
            let pkey = (x509.PublicKey.Key :?> RSA).ExportParameters(false) in
                Some (CoreSig.PK_RSA (abytes pkey.Modulus, abytes pkey.Exponent))
        with :? CryptographicException -> None)

    | x when x = OID_DSASignatureKey ->
        (try
            let pkey = (x509.PublicKey.Key :?> DSA).ExportParameters(false) in
            let dsaparams : CoreKeys.dsaparams =
                { p = abytes pkey.P; q = abytes pkey.Q; g = abytes pkey.G }
            in
                Some (CoreSig.PK_DSA (abytes pkey.Y, dsaparams))
        with :? CryptographicException -> None)

    | _ -> None

let x509_to_secret_key (C x509 : X509Certificate2) =
    match x509.GetKeyAlgorithm() with
    | x when x = OID_RSAEncryption ->
        (try
            let skey = (x509.PrivateKey :?> RSA).ExportParameters(true) in
                Some (CoreSig.SK_RSA (abytes skey.Modulus, abytes skey.D))
        with :? CryptographicException -> None)

    | x when x = OID_DSASignatureKey ->
        (try
            let skey = (x509.PrivateKey :?> DSA).ExportParameters(true) in
            let dsaparams : CoreKeys.dsaparams =
                { p = abytes skey.P; q = abytes skey.Q; g = abytes skey.G }
            in
                Some (CoreSig.SK_DSA (abytes skey.X, dsaparams))
        with :? CryptographicException -> None)

    | _ -> None

(* ------------------------------------------------------------------------ *)

let OID_of_keyalg = function
| SA_RSA   -> OID_RSAEncryption
| SA_DSA   -> OID_DSASignatureKey
| SA_ECDSA -> Error.unexpected "SA_ECDSA"

(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
let x509_has_key_usage_flag strict flag (C x509 : X509Certificate2) =
    try
        let kue =
            x509.Extensions
                |> Seq.cast
                |> Seq.find (fun (e : X509Extension) -> e.Oid.Value = "2.5.29.15") in
        let kue = kue :?> X509KeyUsageExtension in

            kue.KeyUsages.HasFlag(flag)

    with :? KeyNotFoundException ->
        not strict

(* ------------------------------------------------------------------------ *)
let x509_check_key_sig_alg (sigkeyalg : Sig.alg) (C x509 : X509Certificate2) =
    match x509.SignatureAlgorithm with (* AP: WARN: OID_MD5WithRSAEncryption is obsolete - removed *)
    | o when o.Value = OID_SHAWithRSAEncryption ->
         (* We are not strict, to comply with TLS < 1.2 *)
            sigkeyalg = (SA_RSA, MD5SHA1)
         || sigkeyalg = (SA_RSA, SHA    )
         || sigkeyalg = (SA_RSA, NULL   )
    | o when o.Value = OID_SHA256WithRSAEncryption ->
        (* XXX Antoine *)
        (* Unfortunately a certificate signed with SHA-256 must still be usable with the TLS PRF (MD5SHA1) *)
        (* The logic here isn't so clear, we want to correlate with the supported algorithms extension no? *)
        (* The connection between the certificate signature and cipher hash algorithms seems far-fetched *)
            sigkeyalg = (SA_RSA, MD5SHA1)
         || sigkeyalg = (SA_RSA, SHA)
         || sigkeyalg = (SA_RSA, SHA256)
    | o when o.Value = OID_DSASignature ->
        sigkeyalg = (SA_DSA, SHA)
    | _ -> false

let x509_check_key_sig_alg_one (sigkeyalgs : list<Sig.alg>) (x509 : X509Certificate2) =
    List.exists (fun a -> x509_check_key_sig_alg a x509) sigkeyalgs

(* ------------------------------------------------------------------------ *)
let x509_verify (C x509 : X509Certificate2) =
    let chain = new X509Chain() in
        chain.ChainPolicy.RevocationMode <- X509RevocationMode.NoCheck;
        chain.Build(x509)

(* ------------------------------------------------------------------------ *)
let x509_chain (C x509 : X509Certificate2) = (* FIXME: Is certs. store must be opened ? *)
    let chain = new X509Chain() in
        chain.ChainPolicy.RevocationMode <- X509RevocationMode.NoCheck;
        ignore (chain.Build(x509));
        chain.ChainElements
            |> Seq.cast
            |> Seq.map (fun (ce : X509ChainElement) -> C ce.Certificate)
            |> Seq.toList

(* ------------------------------------------------------------------------ *)
let x509_export_public (C x509 : X509Certificate2) : bytes =
    abytes (x509.Export(X509ContentType.Cert))

(* ------------------------------------------------------------------------ *)
let x509_is_for_signing (C x509 : X509Certificate2) =
       x509.Version >= 3
    && x509_has_key_usage_flag false X509KeyUsageFlags.DigitalSignature (C x509)

let x509_is_for_key_encryption (C x509 : X509Certificate2) =
    x509.Version >= 3
    && x509_has_key_usage_flag false X509KeyUsageFlags.KeyEncipherment (C x509)

(* ------------------------------------------------------------------------ *)
let cert_to_x509 (c : cert ) = 
    try
        Some(C (new System.Security.Cryptography.X509Certificates.X509Certificate2(cbytes c)))
    with :? CryptographicException -> None

let chain_to_x509list (chain : chain) =
    try
        Some(List.map (fun (c : cert) -> ( C (new System.Security.Cryptography.X509Certificates.X509Certificate2(cbytes c)))) chain)
    with :? CryptographicException -> None

let x509list_to_chain (chain : list<X509Certificate2>): chain  = List.map x509_export_public chain


let rec validate_x509list (C c : X509Certificate2) (issuers : list<X509Certificate2>) =
    try
        let chain = new X509Chain () in
            chain.ChainPolicy.ExtraStore.AddRange(List.toArray (List.map (fun (C c) -> c) issuers));
            chain.ChainPolicy.RevocationMode <- X509RevocationMode.NoCheck;

            chain.Build(c)
    with :? CryptographicException -> false

(* ------------------------------------------------------------------------ *)

let validate_x509_chain (sigkeyalgs : list<Sig.alg>) (chain : chain) =
    match chain_to_x509list chain with
    | Some(x509list) ->
        (match x509list with
        | [] -> false
        | c::issuers ->
                Seq.forall (x509_check_key_sig_alg_one sigkeyalgs) x509list
                && validate_x509list c issuers)
    | None -> false

let is_for_signing (c : cert) =
    try
        x509_is_for_signing (C (new System.Security.Cryptography.X509Certificates.X509Certificate2(cbytes c)))
    with :? CryptographicException -> false

let is_for_key_encryption (c : cert) =
    try
        x509_is_for_key_encryption (C (new System.Security.Cryptography.X509Certificates.X509Certificate2(cbytes c)))
    with :? CryptographicException -> false

let find_sigcert_and_alg (sigkeyalgs : list<Sig.alg>) (h : hint) (algs : list<Sig.alg>) =
    let store = new X509Store(StoreName.My, StoreLocation.CurrentUser) in

    store.Open(OpenFlags.ReadOnly ||| OpenFlags.OpenExistingOnly);
    try
        (try
            let pick_wrt_req_alg (C x509 : X509Certificate2) =
                    let testalg ((asig, _) : Sig.alg) =
                        x509.GetKeyAlgorithm() = OID_of_keyalg asig
                    in

                    if x509.HasPrivateKey && x509_is_for_signing (C x509) then
                        match List.tryFind testalg algs with
                        | None     -> None
                        | Some alg -> Some (C x509, alg)
                    else
                        None
                in
                    Some(store.Certificates.Find(X509FindType.FindBySubjectName, h, false)
                            |> Seq.cast
                            |> Seq.map (fun c -> C c)
                            |> Seq.filter (fun (x509 : X509Certificate2) -> x509_verify x509)
                            |> Seq.filter (x509_check_key_sig_alg_one sigkeyalgs)
                            |> Seq.pick pick_wrt_req_alg)
        with :? KeyNotFoundException -> None)
    finally
        store.Close()

let find_enccert (sigkeyalgs : list<Sig.alg>) (h : hint) =
    let store = new X509Store(StoreName.My, StoreLocation.CurrentUser) in

    store.Open(OpenFlags.ReadOnly ||| OpenFlags.OpenExistingOnly);
    try
        try
            let x509 =
                store.Certificates.Find(X509FindType.FindBySubjectName, h, false)
                    |> Seq.cast
                    |> Seq.map (fun c -> C c)
                    |> Seq.filter (fun (x509 : X509Certificate2) -> x509_verify x509)
                    |> Seq.filter (fun (C x509 : X509Certificate2) -> x509.HasPrivateKey)
                    |> Seq.filter (fun (x509 : X509Certificate2) -> x509_is_for_key_encryption x509)
                    |> Seq.filter (fun (C x509 : X509Certificate2) -> x509.GetKeyAlgorithm() = OID_RSAEncryption)
                    |> Seq.filter (x509_check_key_sig_alg_one sigkeyalgs)
                    |> Seq.pick   Some
            in Some(x509)
        with
        | :? KeyNotFoundException -> None
    finally
        store.Close()

(* ------------------------------------------------------------------------ *)

let get_chain_key_algorithm (chain : chain) =
    match chain with
    | []     -> None
    | c :: _ ->
        match cert_to_x509 c with 
        | Some(C x509) ->
                (match x509.GetKeyAlgorithm () with
                | x when x = OID_RSAEncryption   -> Some SA_RSA
                | x when x = OID_DSASignatureKey -> Some SA_DSA
                | _ -> None)
        | None -> None

let get_name_info (C x509 : X509Certificate2) = x509.GetNameInfo (System.Security.Cryptography.X509Certificates.X509NameType.SimpleName, false)
