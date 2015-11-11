(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

(* Handshake protocol messages *)
module HandshakeMessages
open FStar.Seq
open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSExtensions
open TLSInfo
open Range

(* External functions, locally annotated for speed *)
assume val vlsplit: lSize:nat{lSize <= 4}
  -> vlb:bytes{lSize <= length vlb}
  -> Tot (Result (b:(bytes * bytes){
                      repr_bytes (length (fst b)) <= lSize
                  /\  Seq.Eq vlb (vlbytes lSize (fst b) @| (snd b))}))

assume val split: b:bytes -> n:nat{length b >= n} -> x:(bytes*bytes){Seq.Eq b ((fst x) @| (snd x)) /\ length (fst x) = n}

assume val split2: b:bytes -> n1:nat -> n2:nat{length b >= n1 + n2} -> x:(lbytes n1 * lbytes n2 * bytes){forall x1. forall x2. forall x3. x = (x1,x2,x3) ==> Seq.Eq b (x1 @| x2 @| x3)}

(*** Following RFC5246 A.4 *)

type PreHandshakeType =
    | HT_hello_request
    | HT_client_hello
    | HT_server_hello
    | HT_certificate
    | HT_server_key_exchange
    | HT_certificate_request
    | HT_server_hello_done
    | HT_certificate_verify
    | HT_client_key_exchange
    | HT_finished

type HandshakeType = PreHandshakeType

val htBytes : HandshakeType -> Tot (lbytes 1)
let htBytes t =
    match t with
    | HT_hello_request       -> abyte   0uy
    | HT_client_hello        -> abyte   1uy
    | HT_server_hello        -> abyte   2uy
    | HT_certificate         -> abyte  11uy
    | HT_server_key_exchange -> abyte  12uy
    | HT_certificate_request -> abyte  13uy
    | HT_server_hello_done   -> abyte  14uy
    | HT_certificate_verify  -> abyte  15uy
    | HT_client_key_exchange -> abyte  16uy
    | HT_finished            -> abyte  20uy

val parseHt : pinverse Seq.Eq htBytes
let parseHt b =
    match cbyte b with
    |   0uy  -> Correct (HT_hello_request      )
    |   1uy  -> Correct (HT_client_hello       )
    |   2uy  -> Correct (HT_server_hello       )
    |  11uy  -> Correct (HT_certificate        )
    |  12uy  -> Correct (HT_server_key_exchange)
    |  13uy  -> Correct (HT_certificate_request)
    |  14uy  -> Correct (HT_server_hello_done  )
    |  15uy  -> Correct (HT_certificate_verify )
    |  16uy  -> Correct (HT_client_key_exchange)
    |  20uy  -> Correct (HT_finished           )
    | _   -> let reason = perror __SOURCE_FILE__ __LINE__ "" in Error(AD_decode_error, reason)

/// Messages

type CH = {
  ch_protocol_version:ProtocolVersion;
  ch_client_random:TLSInfo.random;
  ch_sessionID:sessionID;
  ch_cipher_suites:(k:known_cipher_suites{List.length k < 256});
  ch_compressions:(cl:list Compression{List.length cl <= 1});
  ch_extensions:(ce:list clientExtension{List.length ce < 256});
}

type SH = {
  sh_protocol_version:ProtocolVersion;
  sh_server_random:TLSInfo.random;
  sh_sessionID:sessionID;
  sh_cipher_suite:known_cipher_suite;
  sh_compression:Compression;
  sh_extensions:(se:list serverExtension{List.length se < 256});
}

type CRT = {
  crt_chain: Cert.chain
}

type SCR = {
  scr_cert_types: (cl:list certType{List.length cl < 256});
  scr_sig_hash_algs: option (shs:list Sig.alg{List.length shs < 256});
  scr_distinguished_names: (dl:list dn{List.length dl < 128});
}


type KEX_S =
| KEX_S_DHE of CoreCrypto.dh_key
| KEX_S_ECDHE of CoreCrypto.ec_key
| KEX_S_RSA of CoreCrypto.rsa_key

type KEX_S_PRIV =
| KEX_S_PRIV_DHE of CoreCrypto.dh_key
| KEX_S_PRIV_ECDHE of CoreCrypto.ec_key
| KEX_S_PRIV_RSA of CoreCrypto.rsa_key

type SKE = {
  ske_kex_s: KEX_S;
  ske_sig : (b:bytes{length b < 65536})
}

type KEX_C =
| KEX_C_DHE of (b:bytes{length b < 65536})
| KEX_C_ECDHE of (b:bytes{length b < 256})
| KEX_C_RSA of (b:bytes{length b < 4096})
| KEX_C_DH 

type CKE = {
  cke_kex_c: KEX_C
}

type CCV = {
  ccv_sig: (l:bytes{length l < 65536});
}

type FIN = {
  fin_vd: (l:bytes{length l < 65536});
}

type hs_msg =
  | ClientHello of CH
  | ServerHello of SH
  | ServerCertificate of CRT
  | ServerKeyExchange of SKE
  | ServerCertificateRequest of SCR
  | ServerHelloDone
  | ClientCertificate of CRT
  | ClientKeyExchange of CKE
  | ClientCertificateVerify of CCV
  | ClientFinished of FIN
  | ServerFinished of FIN

/// Handshake message format

val messageBytes : ht:HandshakeType -> data:bytes{ repr_bytes (length data) <= 3 } -> Tot (lbytes (4+(length data))) 
let messageBytes ht data =
    let htb = htBytes ht in
    let vldata = vlbytes 3 data in
    htb @| vldata


val parseMessage : buf:bytes -> Result (option (rem:bytes & hstype:HandshakeType & payload:bytes & to_log:bytes{ (repr_bytes (length payload) <= 3 ) /\ (to_log = messageBytes hstype payload) /\ (Seq.Eq buf (to_log @| rem)) } )) 
let parseMessage buf =
    (* Somewhat inefficient implementation:
       we repeatedly parse the first 4 bytes of the incoming buffer until we have a complete message;
       we then remove that message from the incoming buffer. *)
    if length buf < 4 then Correct(None) (* not enough data to start parsing *)
    else
        let (hstypeb,rem) = split buf 1 in
        match parseHt hstypeb with
        | Error z ->  Error z
        | Correct(hstype) ->
            (match vlsplit 3 rem with
            | Error z -> Correct(None) // not enough payload, try next time
            | Correct(payload,rem) ->
                let to_log = messageBytes hstype payload in
                Correct (Some (|rem,hstype,payload,messageBytes hstype payload|)))


(** A.4.1 Hello Messages *)

val clientHelloBytes : CH -> Tot bytes
let clientHelloBytes ch =
  let verB      = versionBytes ch.ch_protocol_version in
  let sidB = vlbytes 1 ch.ch_sessionID in
  let csb = cipherSuitesBytes ch.ch_cipher_suites in
  let csB = vlbytes 2 csb in
  let cmb = compressionMethodsBytes ch.ch_compressions in
  let cmB = vlbytes 1 cmb in
  let extB = clientExtensionsBytes ch.ch_extensions in
  let data = verB @| (ch.ch_client_random @| (sidB @| (csB @| (cmB @| extB)))) in
  messageBytes HT_client_hello data


val parseClientHello : data:bytes{repr_bytes(length data) <= 3} -> 
                       r:Result (x:CH{exists (x':CH). Seq.Eq (clientHelloBytes x') (messageBytes HT_client_hello data)
                                                     /\ x.ch_protocol_version = x'.ch_protocol_version 
                                                     /\ x.ch_client_random = x'.ch_client_random
                                                     /\ x.ch_sessionID = x'.ch_sessionID })
let parseClientHello data =
    let ld = length data in
    if ld >= 34 then
        let (clVerBytes,cr,data) = split2 data 2 32 in
       (match parseVersion clVerBytes with
        | Error z -> Error z
        | Correct(cv) ->
        if length data >= 1 then
           (match vlsplit 1 data with
            | Error z -> Error z
            | Correct (sid,data) ->
            if length sid <= 32 then
                if length data >= 2 then
                   (match vlsplit 2 data with
                    | Error z -> Error z
                    | Correct (res) ->
                    let (clCiphsuitesBytes,data) = res in
                   (match parseCipherSuites clCiphsuitesBytes with
                    | Error(z) -> Error(z)
                    | Correct (clientCipherSuites) ->
                    if length data >= 1 then
                       (match vlsplit 1 data with
                        | Error(z) -> Error(z)
                        | Correct (res) ->
                        let (cmBytes,extensions) = res in
                        let cm = parseCompressions cmBytes in
                       (match parseClientExtensions extensions clientCipherSuites with
                        | Error(z) -> Error(z) 
                        | Correct (exts) -> 
                        if List.length exts < 256 &&
                           List.length cm <= 1 &&
                           List.length clientCipherSuites < 256 then
                        Correct ({ch_protocol_version = cv;
                                  ch_client_random = cr;        
                                  ch_sessionID = sid;
                                  ch_cipher_suites = clientCipherSuites;
                                  ch_compressions = cm;
                                  ch_extensions = exts})
                        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")))
                    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")))
                else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
            else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


val serverHelloBytes: SH -> Tot bytes
let serverHelloBytes sh = 
    let verB = versionBytes sh.sh_protocol_version in
    let sidB = vlbytes 1 sh.sh_sessionID in
    let csB = cipherSuiteBytes sh.sh_cipher_suite in
    let cmB = compressionBytes sh.sh_compression in
    let extB = serverExtensionsBytes sh.sh_extensions in
    let data = verB @| sh.sh_server_random @| sidB @| csB @| cmB @| extB in
    messageBytes HT_server_hello data

val parseServerHello: data:bytes{repr_bytes(length data)<=3}  -> 
                      r:Result (x:SH{Seq.Eq (serverHelloBytes x) (messageBytes HT_server_hello data)})
let parseServerHello data =
    if length data >= 34 then
        let (serverVerBytes,serverRandomBytes,data) = split2 data 2 32 in
        match parseVersion serverVerBytes with
        | Error z -> Error z
        | Correct(serverVer) ->
            if length data >= 1 then
                match vlsplit 1 data with
                | Error z -> Error z
                | Correct (res) ->
                    let (sid,data) = res in
                    if length sid <= 32 then
                        if length data >= 3 then
                            let (csBytes,cmBytes,data) = split2 data 2 1 in
                            match parseCipherSuite csBytes with
                            | Error(z) -> Error(z)
                            | Correct(cs) ->
                                (match parseCompression cmBytes with
                                | Error(z) -> Error(z)
                                | Correct(cm) ->
                                (match parseServerExtensions data with
                                | Error(z) -> Error(z)
                                | Correct(exts) ->
                                correct({sh_protocol_version = serverVer;       
                                         sh_server_random = serverRandomBytes;
                                         sh_sessionID = sid;
                                         sh_cipher_suite = cs;
                                         sh_compression = cm;
                                         sh_extensions = exts})))
                        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
                    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
            else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val helloRequestBytes: bytes
let helloRequestBytes = messageBytes HT_hello_request empty_bytes

val ccsBytes: bytes
let ccsBytes = abyte 1uy

val serverHelloDoneBytes: bytes
let serverHelloDoneBytes = messageBytes HT_server_hello_done empty_bytes

(** A.4.2 Server Authentication and Key Exchange Messages *)

val certificateBytes: CRT -> Tot bytes
let certificateBytes crt = messageBytes HT_certificate (Cert.certificateListBytes crt.crt_chain)

val parseCertificate: data:bytes{repr_bytes (length data) <= 3} -> 
                      Result (r:CRT{Seq.Eq (certificateBytes r) (messageBytes HT_certificate data)})
let parseCertificate data = 
    if length data >= 3 then
        match vlparse 3 data with
        | Error z -> let (x,y) = z in Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ y)
        | Correct (certList) -> {crt_chain = Cert.parseCertificateList certList}
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val certificateRequestBytes: SCR -> Tot bytes
let certificateRequestBytes scr = 
    let ctb = certificateTypeListBytes scr.scr_cert_types in  
    let ctB = vlbytes 1 ctb in
    let saB = match scr.scr_sig_hash_algs with
              | None -> empty_bytes
              | Some sal -> sigHashAlgListBytes sal in
    let dnb = distinguishedNameListBytes scr.scr_distinguished_names in
    let dnB = vlbytes 2 dnb in
    let data = ctB
            @| saB
            @| dnB in
    messageBytes HT_certificate_request data

val parseCertificateRequest: pv:ProtocolVersion -> data:bytes{repr_bytes(length data) <= 3} -> 
                             Result SCR
let parseCertificateRequest version data =
    if length data >= 1 then
        match vlsplit 1 data with
        | Error(z) -> Error(z)
        | Correct (res) ->
        let (certTypeListBytes,data) = res in
        let certTypeList = parseCertificateTypeList certTypeListBytes in
        if length data >= 2 then
            match version with
            | TLS_1p2 -> 
            (match vlsplit 2 data with
            | Error(z) -> Error(z)
            | Correct  (x,y) ->
            if length y > 0 then 
               match parseSigHashAlgList x with
               | Error(z) -> Error(z)
               | Correct (sigAlgs) -> 
               match parseDistinguishedNameList y [] with
               | Error(z) -> Error(z)
               | Correct (distNamesList) ->
                 correct (
                 {scr_cert_types = certTypeList;
                  scr_sig_hash_algs = Some sigAlgs;
                  scr_distinguished_names = distNamesList})
            else      
               Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
            | _ ->
               match parseDistinguishedNameList data [] with
               | Error(z) -> Error(z)
               | Correct (distNamesList) ->
                 correct (
                 {scr_cert_types = certTypeList;
                  scr_sig_hash_algs = None;
                  scr_distinguished_names = distNamesList})
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let mk_certificateRequestBytes sign cs version =
    certificateRequestBytes (
    {scr_cert_types = defaultCertTypes sign cs;
     scr_sig_hash_algs = (match version with 
                         | TLS_1p2 -> Some (default_sigHashAlg version cs) 
                         | _ -> None);
     scr_distinguished_names = []})                    


(** A.4.3 Client Authentication and Key Exchange Messages *)

val clientKeyExchangeBytes: ProtocolVersion -> CKE -> Tot bytes
let clientKeyExchangeBytes pv cke = 
  let kexB =              
    match pv,cke.cke_kex_c with
    | _,KEX_C_DHE b -> vlbytes 2 b 
    | _,KEX_C_ECDHE b -> vlbytes 1 b
    | SSL_3p0,KEX_C_RSA(encpms) -> encpms
    | _,KEX_C_RSA(encpms) -> vlbytes 2 encpms 
    | _,KEX_C_DH -> empty_bytes in
  messageBytes HT_client_key_exchange kexB

val parseClientKeyExchange: p:ProtocolVersion -> kex:kexAlg -> b:bytes{repr_bytes(length b) <= 3} -> 
    Result (cke:CKE{Seq.Eq (clientKeyExchangeBytes p cke) (messageBytes HT_client_key_exchange b)})
let parseClientKeyExchange pv kex data = 
  match pv,kex with
  | _,Kex_DH -> 
      if length data = 0 
      then Correct({cke_kex_c = KEX_C_DH})
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | _,Kex_DHE -> 
      if length data >= 2
      then (match vlparse 2 data with
           | Error(z) -> Error(z)
           | Correct(y) -> Correct({cke_kex_c = KEX_C_DHE y}))
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | _,Kex_ECDHE -> 
      if length data >= 1
      then (match vlparse 1 data with
           | Error(z) -> Error(z)
           | Correct(y) -> Correct({cke_kex_c = KEX_C_ECDHE y}))
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | SSL_3p0,Kex_RSA -> 
      if length data < 4096 then
         Correct({cke_kex_c = KEX_C_RSA data})
      else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
  | _,Kex_RSA  -> 
        if length data >= 2 then
            match vlparse 2 data with
            | Correct (encPMS) -> correct({cke_kex_c = KEX_C_RSA encPMS})
            | Error(z) -> Error(z)
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

(* ServerKeyExchange *)

open CoreCrypto
val serverKeyExchangeBytes: SKE -> Tot bytes
let serverKeyExchangeBytes ske =
    let kexB = 
        match ske.ske_kex_s with
        | KEX_S_DHE dhp -> (vlbytes 2 dhp.dh_params.dh_p) @| (vlbytes 2 dhp.dh_params.dh_g) @| (vlbytes 2 dhp.dh_public)
        | KEX_S_ECDHE ecp -> 
                 abyte 3uy (* Named curve *)
              @| ECGroup.curve_id ecp.ec_params
              @| ECGroup.serialize_point ecp.ec_params ecp.ec_point 
        | KEX_S_RSA pk -> (*TODO: Ephemeral RSA*) empty_bytes
    in
    let payload = kexB @| ske.ske_sig in
    messageBytes HT_server_key_exchange payload

val parseServerKeyExchange: kex:kexAlg -> b:bytes{repr_bytes(length b) <= 3} -> 
    Result (s:SKE{Seq.Eq (serverKeyExchangeBytes s) (messageBytes HT_server_key_exchange b)})
let parseServerKeyExchange kex payload : Result SKE = 
    match kex with
    | Kex_DH -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | Kex_RSA -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | Kex_DHE -> 
        if length payload >= 2 then
            match vlsplit 2 payload with
            | Error(z) -> Error(z)
            | Correct(res) ->
            let (p,payload) = res in
            if length payload >= 2 then
                match vlsplit 2 payload with
                | Error(z) -> Error(z)
                | Correct(res) ->
                let (g,payload) = res in
                if length payload >= 2 then
                    match vlsplit 2 payload with
                    | Error(z) -> Error(z)
                    | Correct(res) ->
                    let (y,sig) = res in
                    Correct (
                    {ske_kex_s = KEX_S_DHE (
                         {dh_params = {dh_p = p; dh_g = g; dh_q = None; safe_prime = false};
                          dh_public = y;
                          dh_private = None});
                     ske_sig = sig})
                else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
            else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    | Kex_ECDHE -> 
        if length payload >= 7 then
            let (curve, point) = split payload 3 in
            match ECGroup.parse_curve curve with
            | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Unsupported curve")
            | Some(ecp) ->
                match vlsplit 1 point with
                | Error(z) -> Error(z)
                | Correct(rawpoint, payload) ->
                    match ECGroup.parse_point ecp rawpoint with
                    | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Invalid EC point received")
                    | Some p -> correct (None, CommonDH.DHP_EC(ecp), {CommonDH.dhe_nil with CommonDH.dhe_ec = Some p;}, payload)
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


(* Certificate Verify *)
val certificateVerifyBytes: CCV -> Tot bytes
let certificateVerifyBytes ccv = 
    messageBytes HT_certificate_verify ccv.ccv_sig

val parseCertificateVerify: data:bytes{repr_bytes(length data) <= 3} ->
    Result (c:CCV{Seq.Eq (certificateVerifyBytes c) (messageBytes HT_certificate_verify data)})
let parseCertificateVerify data = 
    correct ({ccv_sig = data})

val finishedBytes: FIN -> Tot bytes
let finishedBytes fin = 
    messageBytes HT_finished fin.fin_vd

val parseFinished: data:bytes{repr_bytes(length data)<=3} ->
    Result(f:FIN{Seq.Eq (finishedBytes f) (messageBytes HT_finished data)})
let parseFinished data = 
    Correct ({fin_vd = data})

