(*--build-config
  options:--codegen-lib CoreCrypto --codegen-lib Platform --codegen-lib Classical --codegen-lib SeqProperties --codegen-lib HyperHeap  --admit_fsi FStar.Char --admit_fsi FStar.HyperHeap --admit_fsi FStar.Set --admit_fsi FStar.Map --admit_fsi FStar.Seq --admit_fsi SessionDB --admit_fsi UntrustedCert --admit_fsi DHDB --admit_fsi CoreCrypto --admit_fsi Cert --lax;
  other-files:FStar.FunctionalExtensionality.fst FStar.Classical.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst FStar.HyperHeap.fsi stHyperHeap.fst allHyperHeap.fst char.fsi FStar.String.fst FStar.List.fst FStar.ListProperties.fst seq.fsi FStar.SeqProperties.fst /home/jkz/dev/FStar/contrib/Platform/fst/Bytes.fst /home/jkz/dev/FStar/contrib/Platform/fst/Date.fst /home/jkz/dev/FStar/contrib/Platform/fst/Error.fst /home/jkz/dev/FStar/contrib/Platform/fst/Tcp.fst /home/jkz/dev/FStar/contrib/CoreCrypto/fst/CoreCrypto.fst /home/jkz/dev/FStar/contrib/CoreCrypto/fst/DHDB.fst TLSError.fst TLSConstants-redux.fst Nonce.fst RSAKey.fst DHGroup.p.fst ECGroup.fst CommonDH.fst PMS.p.fst HASH.fst HMAC.fst Sig.p.fst UntrustedCert.fsti Cert.fsti TLSInfo.fst TLSExtensions_Redux.p.fst Range.p.fst DataStream.fst TLSPRF.fst Alert.fst Content.fst StatefulPlain.fst LHAEPlain.fst AEAD_GCM.fst StatefulLHAE.fst PRF-redux.p.fst;
  --*)
    
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
(*
assume val vlsplit: lSize:nat{lSize <= 4}
  -> vlb:bytes{lSize <= length vlb}
  -> Tot (Result (b:(bytes * bytes){
                      repr_bytes (length (fst b)) <= lSize
                  /\  Seq.Eq vlb (vlbytes lSize (fst b) @| (snd b))}))

assume val split: b:bytes -> n:nat{length b >= n} -> Tot (x:(bytes*bytes){Seq.Eq b ((fst x) @| (snd x)) /\ length (fst x) = n})

assume val split2: b:bytes -> n1:nat -> n2:nat{length b >= n1 + n2} -> Tot (x:(lbytes n1 * lbytes n2 * bytes){forall x1. forall x2. forall x3. x = (x1,x2,x3) ==> Seq.Eq b (x1 @| x2 @| x3)})
*)

(*** Following RFC5246 A.4 *)

type PreHandshakeType =
    | HT_hello_request
    | HT_client_hello
    | HT_server_hello
    | HT_session_ticket
    | HT_hello_retry_request
    | HT_encrypted_extensions
    | HT_certificate
    | HT_server_key_exchange
    | HT_certificate_request
    | HT_server_hello_done
    | HT_certificate_verify
    | HT_client_key_exchange
    | HT_server_configuration
    | HT_next_protocol
    | HT_finished

type HandshakeType = PreHandshakeType

val htBytes : HandshakeType -> Tot (lbytes 1)
let htBytes t =
    match t with
    | HT_hello_request       -> abyte   0uy
    | HT_client_hello        -> abyte   1uy
    | HT_server_hello        -> abyte   2uy
    | HT_session_ticket      -> abyte   4uy
    | HT_hello_retry_request -> abyte   6uy
    | HT_encrypted_extensions -> abyte  8uy
    | HT_certificate         -> abyte  11uy
    | HT_server_key_exchange -> abyte  12uy
    | HT_certificate_request -> abyte  13uy
    | HT_server_hello_done   -> abyte  14uy
    | HT_certificate_verify  -> abyte  15uy
    | HT_client_key_exchange -> abyte  16uy
    | HT_server_configuration -> abyte 17uy
    | HT_next_protocol       -> abyte  67uy
    | HT_finished            -> abyte  20uy

(* TODO: inversion lemmas *)
val parseHt : pinverse_t htBytes
let parseHt b =
    match cbyte b with
    |   0uy  -> Correct (HT_hello_request      )
    |   1uy  -> Correct (HT_client_hello       )
    |   2uy  -> Correct (HT_server_hello       )
    |   4uy  -> Correct (HT_session_ticket     )
    |   8uy  -> Correct (HT_encrypted_extensions)
    |  11uy  -> Correct (HT_certificate        )
    |  12uy  -> Correct (HT_server_key_exchange)
    |  13uy  -> Correct (HT_certificate_request)
    |  14uy  -> Correct (HT_server_hello_done  )
    |  15uy  -> Correct (HT_certificate_verify )
    |  16uy  -> Correct (HT_client_key_exchange)
    |  18uy  -> Correct (HT_server_configuration)
    |  20uy  -> Correct (HT_finished           )
    |  67uy  -> Correct (HT_next_protocol      )
    | _   -> let reason = perror __SOURCE_FILE__ __LINE__ "" in Error(AD_decode_error, reason)

/// Messages

type CH = {
  ch_protocol_version:ProtocolVersion;
  ch_client_random:TLSInfo.random;
  ch_sessionID:sessionID;
  ch_cipher_suites:(k:known_cipher_suites{List.length k < 256});
  ch_raw_cipher_suites: option bytes;
  ch_compressions:(cl:list Compression{List.length cl <= 1});
  ch_extensions:option (ce:list extension{List.length ce < 256});
}

let ch_is_resumption { ch_sessionID = sid } =
  length sid > 0

type SH = {
  sh_protocol_version:ProtocolVersion;
  sh_server_random:TLSInfo.random;
  sh_sessionID:option sessionID;  // JK : made optional because not present in TLS 1.3
  sh_cipher_suite:known_cipher_suite;
  sh_compression:option Compression; // JK : made optional because not present in TLS 1.3
  sh_extensions:option (se:list extension{List.length se < 256});
}

(* Hello retry request *)
type HRR = {
  hrr_protocol_version:ProtocolVersion;
  hrr_cipher_suite:known_cipher_suite;
  hrr_named_group: namedGroup; // JK : is it the expected type here ?
  hrr_extensions:(he:list extension{List.length he < 256});
}

type STICKET = {
  sticket_ticket_lifetime_hint:(b:bytes{length b = 4});
  sticket_ticket:bytes;
}

type EE = {
  ee_extensions:(ee:list extension{List.length ee < 256});
}

type CRT = {
  crt_chain: Cert.chain
}

type CR = {
  cr_cert_types: (cl:list certType{List.length cl < 256});
  cr_sig_hash_algs: option (shs:list Sig.alg{List.length shs < 256});
  cr_distinguished_names: (dl:list dn{List.length dl < 128});
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

type CV = {
  cv_sig: (l:bytes{length l < 65536});
}

type SC = {
  sc_configuration_id:configurationId;
  sc_expiration_date:uint32;
  sc_named_group:namedGroup;
  sc_server_key:KEX_C; // JK : use another type ?
  sc_early_data_type:earlyDataType;
  sc_configuration_extensions:(l:list configurationExtension{List.length l < 65536});
}

type FIN = {
  fin_vd: (l:bytes{length l < 65536});
}

// Next protocol message, see https://tools.ietf.org/id/draft-agl-tls-nextprotoneg-03.html
// TODO: replace shallow implemntation by more precise one
type NP = {
  np_selected_protocol: bytes;
  np_padding: bytes;
  }

// TODO: unify, either keep separate finished messages for client and servers or 
// merge them into single "finished" as it is the case for certificates
type hs_msg =
  | ClientHello of CH 
  | ServerHello of SH  
  | SessionTicket of STICKET 
  | EncryptedExtensions of EE 
  | ServerKeyExchange of SKE 
  | CertificateRequest of CR 
  | ServerHelloDone 
  | Certificate of CRT 
  | ClientKeyExchange of CKE  
  | CertificateVerify of CV
  | ServerConfiguration of SC
  | Finished of FIN
  | NextProtocol of NP
  | HelloRequest
  | HelloRetryRequest of HRR

/// Handshake message format

val messageBytes : ht:HandshakeType -> data:bytes{ repr_bytes (length data) <= 3 } -> Tot (lbytes (4+(length data))) 
let messageBytes ht data =
    let htb = htBytes ht in
    let vldata = vlbytes 3 data in
    htb @| vldata


val parseMessage : buf:bytes -> Tot (Result (option (rem:bytes & 
    		   	     	       	        hstype:HandshakeType & 
    		   	     	       	        payload:bytes & 
						to_log:bytes{ (repr_bytes (length payload) <= 3 ) /\ (to_log = messageBytes hstype payload) /\ (Seq.Eq buf (to_log @| rem)) } )) )
let parseMessage buf =
    (* Somewhat inefficient implementation:
       we repeatedly parse the first 4 bytes of the incoming buffer until we have a complete message;
       we then remove that message from the incoming buffer. *)
    if length buf < 4 then Correct(None) (* not enough data to start parsing *)
    else
        let (hstypeb,rem) = split buf 1 in
        resultMap (parseHt hstypeb) 
	(fun hstype -> 
            (match vlsplit 3 rem with
            | Error z -> None // not enough payload, try next time
            | Correct(payload,rem) ->
                let to_log = messageBytes hstype payload in
		let x = (|rem,hstype,payload,messageBytes hstype payload|) in
                Some x))


(** A.4.1 Hello Messages *)

val clientHelloBytes : CH -> Tot bytes
let clientHelloBytes ch =
  let verB      = versionBytes ch.ch_protocol_version in
  let sidB = vlbytes 1 ch.ch_sessionID in
  let csb =
     match ch.ch_raw_cipher_suites with
     | None -> cipherSuitesBytes ch.ch_cipher_suites
     | Some csb -> csb in
  let csB = vlbytes 2 csb in
  let cmb = compressionMethodsBytes ch.ch_compressions in
  let cmB = vlbytes 1 cmb in
  let extB =
     match ch.ch_extensions with
     | Some ext -> extensionsBytes ext
     | None -> empty_bytes in
  let data = verB @| (ch.ch_client_random @| (sidB @| (csB @| (cmB @| extB)))) in
  messageBytes HT_client_hello data

(* 
   This function adds an "first connection" renegotiation info extension to the client hello 
   when parsing it.
   The cipher suite parsing ignores some of them.
   For those two reasons, the serialization function is not an inverse of the parsing function 
   as it is now 
*)
val parseClientHello : data:bytes{repr_bytes(length data) <= 3} -> 
                       Tot (Result (x:CH{exists (x':CH). Seq.Eq (clientHelloBytes x') (messageBytes HT_client_hello data)
                                                     /\ x.ch_protocol_version = x'.ch_protocol_version 
                                                     /\ x.ch_client_random = x'.ch_client_random
                                                     /\ x.ch_sessionID = x'.ch_sessionID }))
let parseClientHello data =
    let ld = length data in
    if ld >= 34 then
      let (clVerBytes,cr,data) = split2 data 2 32 in
      (match parseVersion clVerBytes with
       | Error z -> Error z
       | Correct(cv) ->
         if length data >= 1 then
           (match vlsplit 1 data with
            | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse session id")
            | Correct (sid,data) ->
              if length sid <= 32 then
                (if length data >= 2 then
                   (match vlsplit 2 data with
                    | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse cipher suite bytes")
                    | Correct (res) ->
                      let (clCiphsuitesBytes,data) = res in
                      (match parseCipherSuites clCiphsuitesBytes with
			| Error(z) -> Error(z)
			| Correct clientCipherSuites ->
			  if length data >= 1 then
			    (match vlsplit 1 data with
                            | Error(z) -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse compression bytes")
                            | Correct (res) ->
                              let (cmBytes,extensions) = res in
                              let cm = parseCompressions cmBytes in
			      (match parseOptExtensions extensions with
				| Error(z) -> Error(z) 
				| Correct (exts) ->
                                  let eok = (match exts with
                                    | None -> true
                                    | Some l -> List.length l < 256) in
			          if eok && List.length cm <= 256 && List.length clientCipherSuites < 256 then
				    Correct ({ch_protocol_version = cv;
                                      ch_client_random = cr;        
                                      ch_sessionID = sid;
                                      ch_cipher_suites = clientCipherSuites;
                                      ch_raw_cipher_suites = Some clCiphsuitesBytes;
                                      ch_compressions = cm;
                                      ch_extensions = exts})
				   else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
			   )
                         else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
		      )
		   )
		else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
              else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
         else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")


val serverHelloBytes: SH -> Tot bytes
let serverHelloBytes sh = 
    let verB = versionBytes sh.sh_protocol_version in
    let sidB = 
      match sh.sh_sessionID with
      | Some sid -> vlbytes 1 sid 
      | _ -> empty_bytes in
    let csB = cipherSuiteBytes sh.sh_cipher_suite in
    let cmB = 
      match sh.sh_compression with
      | Some compression -> compressionBytes compression
      | _ -> empty_bytes in
    let extB = 
      match sh.sh_extensions with
      | Some ext -> extensionsBytes ext
      | None -> empty_bytes in
    let data = verB @| sh.sh_server_random @| sidB @| csB @| cmB @| extB in
    messageBytes HT_server_hello data

val parseServerHello: data:bytes{repr_bytes(length data)<=3}  -> 
                      Tot (Result (x:SH{Seq.Eq (serverHelloBytes x) (messageBytes HT_server_hello data)}))
let parseServerHello data =
    if length data >= 34 then
        let (serverVerBytes,serverRandomBytes,data) = split2 data 2 32 in
        match parseVersion serverVerBytes with
        | Error z -> Error z
        | Correct(serverVer) ->
	  match serverVer with
	  | TLS_1p3 -> 
	    if length data >= 1 then 
	      let (csBytes, data) = split data 2 in
	      match parseCipherSuite csBytes with
	      | Error(z) -> Error(z)
	      | Correct(cs) -> 
		(match parseOptExtensions data with
		| Error(z) -> Error(z)
                | Correct(exts) ->
                    correct({sh_protocol_version = serverVer;       
                      sh_server_random = serverRandomBytes;
                      sh_sessionID = None;
                      sh_cipher_suite = cs;
                      sh_compression = None;
                      sh_extensions = exts}))
	     else  Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
	  | _ ->
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
                                let cm = parseCompression cmBytes in
                                (match cm with
                                | UnknownCompression _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "server selected a compression mode")
                                | NullCompression ->
                                (match parseOptExtensions data with
                                | Error(z) -> Error(z)
                                | Correct(exts) ->
                                correct({sh_protocol_version = serverVer;       
                                         sh_server_random = serverRandomBytes;
                                         sh_sessionID = Some sid;
                                         sh_cipher_suite = cs;
                                         sh_compression = Some cm;
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
                      Tot (Result (r:CRT{Seq.Eq (certificateBytes r) (messageBytes HT_certificate data)}))
let parseCertificate data = 
    if length data >= 3 then
        match vlparse 3 data with
        | Error z -> let (x,y) = z in Error(AD_bad_certificate_fatal, perror __SOURCE_FILE__ __LINE__ y)
	| Correct (certList) -> 
	    let chain_res = Cert.parseCertificateList certList in
	    let chain = resT chain_res in // JK : need of pattern matching here ?
	    Correct ({crt_chain = chain})
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

val certificateRequestBytes: CR -> Tot bytes
let certificateRequestBytes cr = 
    let ctb = certificateTypeListBytes cr.cr_cert_types in  
    let ctB = vlbytes 1 ctb in
    let saB = match cr.cr_sig_hash_algs with
              | None -> empty_bytes
              | Some sal -> sigHashAlgsBytes sal in
    let dnb = distinguishedNameListBytes cr.cr_distinguished_names in
    let dnB = vlbytes 2 dnb in
    let data = ctB
            @| saB
            @| dnB in
    messageBytes HT_certificate_request data

val parseCertificateRequest: pv:ProtocolVersion -> data:bytes{repr_bytes(length data) <= 3} -> 
                             Tot (Result CR)
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
               match parseSigHashAlgs (vlbytes 2 x) with
               | Error(z) -> Error(z)
               | Correct (sigAlgs) -> 
	       match vlparse 2 y with
	       | Error(z) -> Error(z)
	       | Correct(y) ->
               match parseDistinguishedNameList y [] with
               | Error(z) -> Error(z)
               | Correct (distNamesList) ->
                 correct (
                 {cr_cert_types = certTypeList;
                  cr_sig_hash_algs = Some sigAlgs;
                  cr_distinguished_names = distNamesList})
            else      
               Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ ""))
            | _ ->
               match parseDistinguishedNameList data [] with
               | Error(z) -> Error(z)
               | Correct (distNamesList) ->
                 correct (
                 {cr_cert_types = certTypeList;
                  cr_sig_hash_algs = None;
                  cr_distinguished_names = distNamesList})
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

let mk_certificateRequestBytes sign cs version =
    certificateRequestBytes (
    {cr_cert_types = defaultCertTypes sign cs;
     cr_sig_hash_algs = (match version with 
                         | TLS_1p2 -> Some (default_sigHashAlg version cs) 
                         | _ -> None);
     cr_distinguished_names = []})                    


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
    Tot (Result (cke:CKE{Seq.Eq (clientKeyExchangeBytes p cke) (messageBytes HT_client_key_exchange b)}))
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
    Tot (Result (s:SKE{Seq.Eq (serverKeyExchangeBytes s) (messageBytes HT_server_key_exchange b)}))
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
                    let (y,sign) = res in
                    Correct (
                    {ske_kex_s = KEX_S_DHE (
                         {dh_params = {dh_p = p; dh_g = g; dh_q = None; safe_prime = false};
                          dh_public = y;
                          dh_private = None});
                     ske_sig = sign})
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
                    | Some p -> Correct (
			{ ske_kex_s = KEX_S_ECDHE (
			    {ec_priv = None;
			    ec_params = ecp;
			    ec_point = p;});
			  ske_sig =  payload})
        else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

(* Certificate Verify *)
val certificateVerifyBytes: CV -> Tot bytes
let certificateVerifyBytes cv = 
    messageBytes HT_certificate_verify cv.cv_sig

val parseCertificateVerify: data:bytes{repr_bytes(length data) <= 3} ->
    Tot (Result (c:CV{Seq.Eq (certificateVerifyBytes c) (messageBytes HT_certificate_verify data)}))
let parseCertificateVerify data = 
    correct ({cv_sig = data})

val finishedBytes: FIN -> Tot bytes
let finishedBytes fin = 
    messageBytes HT_finished fin.fin_vd

val parseFinished: data:bytes{repr_bytes(length data)<=3} ->
    Tot (Result(f:FIN{Seq.Eq (finishedBytes f) (messageBytes HT_finished data)}))
let parseFinished data = 
    Correct ({fin_vd = data})

(* Session ticket *)
val sessionTicketBytes: STICKET -> Tot bytes
let sessionTicketBytes sticket =
    let payload = sticket.sticket_ticket_lifetime_hint @| sticket.sticket_ticket in
    messageBytes HT_session_ticket payload

val parseSessionTicket: b:bytes{repr_bytes(length b) <= 3} -> 
    Tot (Result (s:STICKET{Seq.Eq (sessionTicketBytes s) (messageBytes HT_session_ticket b)}))
let parseSessionTicket payload : Result STICKET = 
  if length payload >= 4 && length payload < 65542 then
    let (lifetime_hint, ticket) = split payload 4 in
    Correct({sticket_ticket_lifetime_hint = lifetime_hint; sticket_ticket = ticket})
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Inappropriate size in received session ticket")

(* Hello retry request *)
val helloRetryRequestBytes: HRR -> Tot bytes
let helloRetryRequestBytes hrr =
  let pv = versionBytes hrr.hrr_protocol_version in
  let cs_bytes = cipherSuiteBytes hrr.hrr_cipher_suite in
  let ng = namedGroupBytes hrr.hrr_named_group in
  let exts = extensionsBytes hrr.hrr_extensions in
  pv @| cs_bytes @| ng @| exts

(* TODO: inversion lemmas *)
val parseHelloRetryRequest: pinverse_t helloRetryRequestBytes
let parseHelloRetryRequest b = 
  if length b >= 4 then 
    let pv, cs, data = split2 b 2 2 in
    (match TLSConstants.parseVersion pv with
    | Correct(pv) -> 
      (match parseCipherSuite cs with
      | Correct(cs) -> 
	if length data >= 2 then
	  let ng, data = split data 2 in
	  (match parseNamedGroup ng with
	  | Correct(ng) ->
	    (match parseExtensions data with
	    | Correct(exts) -> 
	      Correct ({ hrr_protocol_version = pv;
			hrr_cipher_suite = cs;
			hrr_named_group = ng;
			hrr_extensions = exts })
	    | Error(z) -> Error(z))
	  | Error(z) -> Error(z))
	else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong hello retry request format")
      | Error(z) -> Error(z))  
    | Error(z) -> Error(z))
  else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Wrong hello retry request format")

(* Encrypted_extensions *)
val encryptedExtensionsBytes: EE -> Tot bytes
let encryptedExtensionsBytes ee =
    let payload = extensionsBytes ee.ee_extensions in
    messageBytes HT_encrypted_extensions payload

val parseEncryptedExtensions: b:bytes{repr_bytes(length b) <= 3} -> 
    Tot (Result (s:EE{Seq.Eq (encryptedExtensionsBytes s) (messageBytes HT_encrypted_extensions b)}))
let parseEncryptedExtensions payload : Result EE = 
  match parseExtensions payload with
  | Error(z) -> Error(z)
  | Correct(exts) -> Correct({ee_extensions = exts;})

(* Server configuration *)
val serverConfigurationBytes: SC -> Tot bytes
let serverConfigurationBytes sc =
  let cid = sc.sc_configuration_id in
  let date = sc.sc_expiration_date in
  let ng = namedGroupBytes sc.sc_named_group in
  let sk = 
    match sc.sc_server_key with
    | KEX_C_DHE b -> b
    | KEX_C_ECDHE b -> b in
  let edt = earlyDataTypeBytes sc.sc_early_data_type in 
  let exts = configurationExtensionsBytes sc.sc_configuration_extensions in
  let payload = cid @| date @| ng @| sk @| edt @| exts in
  messageBytes HT_server_configuration payload

val parseServerConfiguration: b:bytes{repr_bytes(length b) <= 3} -> 
    Tot (Result (s:SC{Seq.Eq (serverConfigurationBytes s) (messageBytes HT_server_configuration b)}))
let parseServerConfiguration payload : Result SC = 
  match vlsplit 2 payload with
  | Correct(config_id, data) -> (
      if length data >= 6 then
	let (date, ng, data) = split2 data 4 2 in
	match parseNamedGroup ng with
	| Correct(ng) -> 
	  match vlsplit 2 data with
	  | Correct(sk, data) ->
	      let sk = match ng with
		      | SEC _ | ECDHE_PRIVATE_USE _ -> KEX_C_ECDHE sk
		      | FFDHE _ | FFDHE_PRIVATE_USE _ -> KEX_C_DHE sk in	      
	      if length data >= 2 then
		let (edt, exts) = split data 2 in
		match parseEarlyDataType edt with
		| Correct(edt) ->
		  match vlsplit 2 exts with
		  | Correct(exts, tail) -> 
		      if equalBytes tail empty_bytes then
		        match parseConfigurationExtensions exts with
			| Correct(exts) ->
			    Correct({ sc_configuration_id = config_id;
				      sc_expiration_date = date;
				      sc_named_group = ng;
				      sc_server_key = sk;
				      sc_early_data_type = edt;
				      sc_configuration_extensions = exts;})
		        | Error(z) -> Error(z)
		      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
		  | Error(z) -> Error(z)
		| Error(z) -> Error(z)
	      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
	  | Error(z) -> Error(z)
	| Error(z) -> Error(z)
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "") )
 | Error(z) -> Error(z)

(* Next protocol message *)
val nextProtocolBytes: NP -> Tot bytes
let nextProtocolBytes np =
  let selected_protocol = vlbytes 1 np.np_selected_protocol in
  let padding = vlbytes 1 np.np_padding in
  messageBytes HT_next_protocol (selected_protocol @| padding)

val parseNextProtocol: b:bytes -> 
    Tot (Result (s:NP{Seq.Eq (nextProtocolBytes s) (messageBytes HT_next_protocol b)}))
let parseNextProtocol payload : Result NP = 
  match vlsplit 1 payload with
  | Error(z) -> Error(z)
  | Correct(selected_protocol, data) ->
  match vlparse 1 data with
  | Error(z) -> Error(z)
  | Correct(padding) -> 
      Correct( { np_selected_protocol = selected_protocol;
		 np_padding = padding;})
		 
val parseHandshakeMessage: option ProtocolVersion -> option kexAlg -> HandshakeType -> bytes -> Tot (Result hs_msg)
let parseHandshakeMessage pv kex hstype pl = 
    match hstype,pv,kex with
    | HT_hello_request,_,_       -> if (length pl = 0) then Correct(HelloRequest) else Error(AD_decode_error, "HelloRequest with non-empty body")
    | HT_client_hello,_,_        -> mapResult ClientHello (parseClientHello pl)
    | HT_server_hello,_,_        -> mapResult ServerHello (parseServerHello pl)
    | HT_session_ticket,_,_      -> mapResult SessionTicket (parseSessionTicket pl)
    | HT_hello_retry_request,_,_ -> mapResult HelloRetryRequest (parseHelloRetryRequest pl)
    | HT_encrypted_extensions,_,_ -> mapResult EncryptedExtensions (parseEncryptedExtensions pl)
    | HT_certificate,_,_         -> mapResult Certificate (parseCertificate pl)
    | HT_server_key_exchange,_,Some kex -> mapResult ServerKeyExchange (parseServerKeyExchange kex pl)
    | HT_certificate_request,Some pv,_ -> mapResult CertificateRequest (parseCertificateRequest pv pl)
    | HT_server_hello_done,_,_   -> if (length pl = 0) then Correct(ServerHelloDone) else Error(AD_decode_error, "ServerHelloDone with non-empty body")
    | HT_certificate_verify,_,_  -> mapResult CertificateVerify (parseCertificateVerify pl)
    | HT_client_key_exchange,Some pv,Some kex -> mapResult ClientKeyExchange (parseClientKeyExchange pv kex pl)
    | HT_server_configuration,_,_ -> mapResult ServerConfiguration (parseServerConfiguration pl)
    | HT_next_protocol,_,_       -> mapResult NextProtocol (parseNextProtocol pl)
    | HT_finished,_,_            -> mapResult Finished (parseFinished pl)

