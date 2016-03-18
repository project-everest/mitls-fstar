(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module RSA
open FStar.Seq
open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSInfo
open RSAKey

(*  RSAKey manages RSA encryption keys. 
    Conceptually RSAKey and RSA are one module. 
    They are separated only to manage module dependencies. 
    Except for RSA, no module should call RSAKey.repr_of_rsaskey. *)

(*  Idealization strategy: to make sure that in the ideal world
    no information about the (ideal) pre-master secret (pms) value 
    is leaked, we encrypt a dummy pms instead of the real pms. 
    
    The ideal pms is stored into a table during
    idealized encryption and read from the table during idealized decryption.
    This is only done when the cryptography warrants idealization,
    as indicated by PMS.honestRSAPMS.
    
    Taken on its own our assumption would be somewhat related to 
    RCCA security: http://eprint.iacr.org/2003/174.pdf. This would however still be 
    too strong an assumption for PKCS1. We weaken the assumption by 
    allowing any attacker to accessthe RSA module only through the 
    KEF module. This has two effects:

     i) ideal PMS are sampled rather than chosen by the adversary.
    ii) only the hash values of PMS are made available to the adversary. *)  

#if ideal
// We maintain a table from dummy_pms to ideal_pms.
// (the protocolVersion can also be extracted from dummy_pms)
type entry = pk * protocolVersion * PMS.rsarepr *  PMS.rsapms
let log = ref []
#endif

(*  Encrypts a pms value under a particular key and for a proposed 
    client version. We require that every ideal pms be encrypted 
    only once (in TLS, by the client immediately after generation).
    Otherwise we would require a stronger cryptographic assumption.
    The ideal functionality would change to reuse the corresponding 
    dummy_pms value for reused ideal pms.
 *)
let encrypt pk cv pms =
    //#begin-ideal1
    let plaintext = 
    #if ideal
      if PMS.honestRSAPMS pk cv pms then
        let dummy_pms = versionBytes cv @| Nonce.random 46 in
        log := (pk,cv,dummy_pms,pms)::!log;
        dummy_pms
      else
    #endif
        PMS.leakRSA pk cv pms
    in     
    //#end-ideal1
    let ciphertext = CoreCrypto.rsa_encrypt (RSAKey.repr_of_rsapkey pk) CoreCrypto.Pad_PKCS1 plaintext in
    ciphertext
    
(*  Decrypts a ciphertext concretely to obtain a pms value. 
    This can be either a real or a dummy pms.

    The code implements several heuristic countermeasures:
    1)  a fake pms (!= dummy pms) is created in advance, 
        to be returned instead of errors
    2)  the pms value is used to 'authenticate the ClientHello.client_version 
        See http://tools.ietf.org/html/rfc5246#section-7.4.7.1
   
        The version number in the PreMasterSecret is the version
        offered by the client in the ClientHello.client_version, not the
        version negotiated for the connection.  This feature is designed to
        prevent rollback attacks.  

       Client implementations MUST always send the correct version number in
       PreMasterSecret.  If ClientHello.client_version is TLS 1.1 or higher,
       server implementations MUST check the version number as described in
       the note below.  If the version number is TLS 1.0 or earlier, server
       implementations SHOULD check the version number, but MAY have a
       configuration option to disable the check.  
*)

//#begin-real_decrypt
let real_decrypt dk si cv cvCheck ciphertext =
  (* Security measures described in RFC 5246, section 7.4.7.1 *)
  (* 1. Generate 46 random bytes, for fake PMS except client version *)
  let fakepms = Nonce.random 46 in
  let expected = versionBytes cv in
  (* 2. Decrypt the message to recover plaintext *)
    match CoreCrypto.rsa_decrypt (RSAKey.repr_of_rsaskey dk) CoreCrypto.Pad_PKCS1 (ciphertext) with
    | Some pms when (length pms = 48) ->
        let (clVB,postPMS) = split pms 2 in
        (match si.protocol_version with
            | TLS_1p1 | TLS_1p2 ->
                (* 3. If new TLS version, just go on with client version and true pms.
                    This corresponds to a check of the client version number, but we'll fail later. *)
                expected @| postPMS
          
            | SSL_3p0 | TLS_1p0 ->
                (* 3. If check disabled, use client provided PMS, otherwise use our version number *)
                if cvCheck 
                then expected @| postPMS
                else pms)
    | _  -> 
        (* 3. in case of decryption length error, continue with fake PMS *) 
        expected @| fakepms
//#end-real_decrypt

#if ideal
let rec assoc (pk:RSAKey.pk) (cv:protocolVersion) (dummy_pms:bytes) (pmss:list<entry>) = 
    match pmss with 
    | [] -> None 
    | (pk',cv',dummy_pms',ideal_pms)::mss' when (pk=pk' && cv=cv' && dummy_pms=dummy_pms') -> Some(ideal_pms) 
    | _::mss' -> assoc pk cv dummy_pms mss'
#endif

(* Decrypts a ciphertext either in the real world or the ideal world to obtain a pms value. 
   This can be either a real or an ideal pms. An ideal pms is decrypted by first decrypting 
   its dummy_pms and then doing a table lookup.
   *)

let decrypt (sk:RSAKey.sk) si cv check_client_version_in_pms_for_old_tls encPMS =
    match Cert.get_chain_public_encryption_key si.serverID with
    | Error z  -> unexpected (perror __SOURCE_FILE__ __LINE__ "The server identity should contain a valid certificate")
    | Correct(pk) ->
        let pmsb = real_decrypt sk si cv check_client_version_in_pms_for_old_tls encPMS in
        //#begin-ideal2
        #if ideal
        match assoc pk cv pmsb !log with
          | Some(ideal_pms) -> ideal_pms
          | None            -> 
        #endif
            PMS.coerceRSA pk cv pmsb
        //#end-ideal2
        
