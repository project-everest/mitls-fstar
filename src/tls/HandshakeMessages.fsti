(* Copyright (C) 2012--2018 Microsoft Research and INRIA *)
(**
Handshake protocol messages
*)
module HandshakeMessages
open FStar.Seq
open FStar.Bytes
open FStar.Error
open TLSError
open TLSConstants
open Extensions
open TLSInfo
open Range
open CommonDH

// e18-02-21 carved out an interface, far from perfect...  
// In particular, it exposes the separate parsing of message headers
// and payloads; I would prefer entirely avoid [handshakeType] or at
// least keep it private

/// Handshake types

type handshakeType =
  | HT_hello_request
  | HT_client_hello
  | HT_server_hello
  | HT_session_ticket
  | HT_end_of_early_data
  | HT_hello_retry_request
  | HT_encrypted_extensions
  | HT_certificate
  | HT_server_key_exchange
  | HT_certificate_request
  | HT_server_hello_done
  | HT_certificate_verify
  | HT_client_key_exchange
  | HT_finished
  | HT_key_update
  | HT_message_hash

val htBytes: handshakeType -> Tot (lbytes 1)
val htBytes_is_injective: 
  ht1:handshakeType -> ht2:handshakeType -> 
  Lemma (requires (True)) (ensures (htBytes ht1 = htBytes ht2 ==> ht1 = ht2))
  [SMTPat (htBytes ht1); SMTPat (htBytes ht2)]
val parseHt: pinverse_t htBytes
val inverse_ht: x:_ -> Lemma
  (requires True)
  (ensures lemma_inverse_g_f htBytes parseHt x)
  [SMTPat (parseHt (htBytes x))]
val pinverse_ht: x:_ -> Lemma
  (requires True)
  (ensures (lemma_pinverse_f_g equal htBytes parseHt x))
  [SMTPat (htBytes (Correct?._0 (parseHt x)))]


// We follow the structure of the TLS 1.3 RFC, 
// but we also include prior TLS messages

/// Key Exchange Messages
/// https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.1

// ClientHello for all protocol versions
noeq type ch = {
  ch_protocol_version: protocolVersion; // max supported version up to TLS_1p2 (TLS 1.3 uses the supported_versions extension)
  ch_client_random: TLSInfo.random;
  ch_sessionID: sessionID;
  ch_cipher_suites: k:valid_cipher_suites{List.Tot.length k < 256};
  ch_compressions: cl:list compression{List.Tot.length cl > 0 /\ List.Tot.length cl < 256};
  ch_extensions: option (ce:list extension{List.Tot.length ce < 256});
}
let bindersLen_of_ch ch =
  match ch.ch_extensions with
  | None -> 0
  | Some el -> Extensions.bindersLen el

// ServerHello: supporting two different syntaxes depending on the embedded pv
// https://tools.ietf.org/html/rfc5246#section-7.4.1.2
// https://tlswg.github.io/tls13-spec/#rfc.section.4.1.3
noeq type sh = {
  sh_protocol_version: protocolVersion;
  sh_server_random: TLSInfo.random;
  sh_sessionID: sessionID; // omitted in TLS 1.3
  sh_cipher_suite: valid_cipher_suite;
  sh_compression: compression; // omitted in TLS 1.3
  sh_extensions: option (se:list extension{List.Tot.length se < 256});
}
// Hello retry request
noeq type hrr = {
  hrr_sessionID: sessionID;
  hrr_cipher_suite: valid_cipher_suite;
  hrr_extensions: he:list extension{List.Tot.length he < 256};
}

// TLS 1.2 KeyExchange 
noeq type kex_s =
| KEX_S_DHE of (g:CommonDH.group & CommonDH.pre_share g)
| KEX_S_RSA of (pk:CoreCrypto.rsa_key{False}) // Unimplemented
noeq type kex_s_priv =
| KEX_S_PRIV_DHE of (g:CommonDH.group & CommonDH.ikeyshare g)
| KEX_S_PRIV_RSA of CoreCrypto.rsa_key
type kex_c =
| KEX_C_DHE of b:bytes{length b < 65536}
| KEX_C_ECDHE of b:bytes{length b < 256}
| KEX_C_RSA of b:bytes{length b < 4096}
| KEX_C_DH
noeq type cke = {cke_kex_c: kex_c}


/// Server Parameters
/// https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.3

type ee = l:list extension{List.Tot.length l < 256}

// CertificateRequest
(** CertificateRequest for TLS 1.0-1.2
 https://tools.ietf.org/html/rfc2246#section-7.4.4
 https://tools.ietf.org/html/rfc4346#section-7.4.4
 https://tools.ietf.org/html/rfc5246#section-7.4.4
*)
type cr = {
  cr_cert_types: cl:list certType{0 < List.Tot.length cl /\ List.Tot.length cl < 256};
  cr_sig_algorithms: option signatureSchemeList; // None for 1.0,1.1; Some for 1.2
  cr_certificate_authorities: dl:list dn{List.Tot.length dl < 65536};
}
type cr13 = cr //17-05-05 TBC


/// Authentication Messages
/// https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.4

// Certificate payloads (the format changed deeply)
noeq type crt = {crt_chain: Cert.chain}
noeq type crt13 = {
  crt_request_context: b:bytes {length b <= 255};
  crt_chain13: Cert.chain13;}

// REMARK: The signature algorithm field is absent in digitally-signed structs in TLS < 1.2
type signature = {
  sig_algorithm: option signatureScheme;
  sig_signature: b:bytes{length b < 65536} }
noeq type ske = {
  ske_kex_s: kex_s;
  ske_signed_params: signature }

type cv = sig:signature

//17-03-11 Finished payload, carrying a fixed-length MAC; share with binders?
type fin = { fin_vd: b:bytes{length b < 65536}; }


/// Post-Handshake Messages 
/// https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.6

// NewSessionTicket payload for RFC5077 (https://tools.ietf.org/html/rfc5077)
type sticket = {
  sticket_lifetime: UInt32.t;
  sticket_ticket: b:bytes{length b < 65536}; }

// NewSessionTicket payload for TLS 1.3 (https://tlswg.github.io/tls13-spec/#NSTMessage)
noeq type sticket13 = {
  ticket13_lifetime: UInt32.t;
  ticket13_age_add: UInt32.t;
  ticket13_nonce: (b:bytes{length b > 0 /\ length b < 256});
  ticket13_ticket: (b:bytes{length b < 65535});
  ticket13_extensions: es: list extension; }


noeq type hs_msg =
  // shared
  | ClientHello of ch
  | ServerHello of sh
  | CertificateVerify of cv
  | Finished of fin

  // up to TLS 1.2
  | ClientKeyExchange of cke
  | ServerKeyExchange of ske
  | ServerHelloDone
  | Certificate of crt
  | CertificateRequest of cr
  | HelloRequest
  | NewSessionTicket of sticket

  // new formats for TLS 1.3
  | EndOfEarlyData // client
  | EncryptedExtensions of ee // server
  | Certificate13 of crt13
  | CertificateRequest13 of cr13
  | HelloRetryRequest of hrr
  | NewSessionTicket13 of sticket13
  | KeyUpdate of bool  // true when the sender is the requester

  // formatted, but never parsed as messages
  | Binders of Extensions.binders
  | MessageHash of Hashing.Spec.anyTag


/// Handshake message format (minimized)

val messageBytes:
  ht:handshakeType -> 
  data:bytes {repr_bytes (length data) <= 3} -> 
  Tot (lbytes (4 + length data))

let hs_msg_bytes (ht:handshakeType) (b:bytes) =
  length b >= 4 /\ 
  ( let b' = snd (split b 4ul) in
    repr_bytes (length b') <= 3 /\ 
    b = messageBytes ht b')

val messageBytes_is_injective_strong:
  ht1:handshakeType -> data1:bytes{ repr_bytes (length data1) <= 3 } -> s1:bytes ->
  ht2:handshakeType -> data2:bytes{ repr_bytes (length data2) <= 3 } -> s2:bytes ->
  Lemma 
  (ensures 
    equal (messageBytes ht1 data1 @| s1) (messageBytes ht2 data2 @| s2) ==> 
    ht1 = ht2 /\ equal data1 data2 /\ equal s1 s2)

val messageBytes_is_injective:
  ht1:handshakeType -> data1:bytes{ repr_bytes (length data1) <= 3 } ->
  ht2:handshakeType -> data2:bytes{ repr_bytes (length data2) <= 3 } ->
  Lemma
  (ensures 
    equal (messageBytes ht1 data1) (messageBytes ht2 data2) ==> 
    ht1 = ht2 /\ equal data1 data2)
  [SMTPat (messageBytes ht1 data1); SMTPat (messageBytes ht2 data2)]

val parseMessage: buf:bytes -> Tot (result (option (
  rem: bytes &
  hstype: handshakeType &
  payload: bytes {repr_bytes (length payload) <= 3} &
  to_log: bytes {to_log = messageBytes hstype payload /\ equal buf (to_log @| rem) })))

val clientHelloBytes: ch -> Tot (b:bytes{length b >= 41 /\ hs_msg_bytes HT_client_hello b}) 
// JK: used to be 42 but cannot prove it with current specs. Is there
// a minimal length of 1 for the session ID maybe ?

// should this be in TLSConstants?
val versionBytes_is_injective: 
  pv1:protocolVersion -> 
  pv2:protocolVersion ->
  Lemma (versionBytes pv1 = versionBytes pv2 ==> pv1 = pv2)

val clientHelloBytes_is_injective_strong:
  msg1:ch -> s1:bytes -> 
  msg2:ch -> s2:bytes ->
  Lemma
  (ensures (
    equal (clientHelloBytes msg1 @| s1) (clientHelloBytes msg2 @| s2) ==> 
    msg1 == msg2 /\ s1 == s2))

(* This function adds a "first connection" renegotiation info *)
(* extension to the client hello when parsing it. The cipher suite *)
(* parsing ignores some of them. For these two reasons, the *)
(* serialization function is not an inverse of the parsing function as *)
(* it is now *)
//17-05-09 generalized signature (but no binder parsing  yet!)
val parseClientHello: body:bytes -> Pure (result (ch * option binders))
  (requires (repr_bytes(length body) <= 3))
  (ensures (function
    | Error _ -> True
    | Correct(ch, None) -> clientHelloBytes ch == htBytes HT_client_hello @| body
    | Correct(ch, Some binders) ->
        let len = length body - bindersLen_of_ch ch in 
        0 <= len /\
        ( let truncated_body, suffix = split_ body len in
          clientHelloBytes ch == htBytes HT_client_hello @| truncated_body /\
          bindersBytes binders == suffix // ADL: FIXME must strip the length from binders
  )))

val serverHelloBytes: sh -> Tot (b:bytes{length b >= 34 /\ hs_msg_bytes HT_server_hello b})

let valid_sh: Type0 = sh

val serverHelloBytes_is_injective: 
  msg1:valid_sh -> msg2:valid_sh -> Lemma 
  (requires equal (serverHelloBytes msg1) (serverHelloBytes msg2))
  (ensures msg1 == msg2)

val serverHelloBytes_is_injective_strong: 
  msg1:valid_sh -> s1: bytes -> msg2:valid_sh -> s2: bytes -> Lemma
  (requires equal (serverHelloBytes msg1 @| s1) (serverHelloBytes msg2 @| s2))
  (ensures msg1 == msg2 /\ s1 == s2)

(* JK: should return a valid_sh to match the serialization function *)
(* JK: same as parseClientHello, weakening spec to get verification *)
val parseServerHello: 
  data:bytes{repr_bytes(length data) <= 3} -> Tot (result (x:valid_sh))
(* val parseServerHello: data:bytes{repr_bytes(length data) <= 3}   *)
(*   -> Tot (result (x:sh{equal (serverHelloBytes x) (messageBytes HT_server_hello data)})) *)

val helloRequestBytes: b:lbytes 4{hs_msg_bytes HT_hello_request b}

val ccsBytes: lbytes 1

val serverHelloDoneBytes: b:lbytes 4{hs_msg_bytes HT_server_hello_done b}


// TLS 1.2 ServerKeyExchange 

// used in Handshake
// ADL: this is silly, we have uniform support of EC now
val kex_c_of_dh_key: #g:CommonDH.group -> CommonDH.pre_share g -> Tot kex_c

// used in Negotiation
val kex_s_to_bytes: 
  kex_s -> Tot (b:bytes{length b < 16777216 - 65540}) 
  // JK: required for serverKeyExchangeBytes


let associated_to_pv (pv:option protocolVersion) (msg:hs_msg) : GTot bool  =
  match msg with
  | ServerKeyExchange _ | CertificateRequest _ | CertificateVerify _ -> Some? pv
  | _ -> true

let valid_hs_msg_prop (pv:option protocolVersion) (msg:hs_msg): GTot bool =
  associated_to_pv pv msg && (
  match msg, pv with
  | EncryptedExtensions ee, _ -> 
      length (extensionListBytes ee) + bindersLen ee < 65536 &&
       repr_bytes (length (extensionsBytes ee)) <= 3
  | Certificate13 crt, _ -> length (Cert.certificateListBytes13 crt.crt_chain13) < 16777212
  | Certificate crt, _ -> length (Cert.certificateListBytes crt.crt_chain) < 16777212
  | ServerKeyExchange ske, Some pv ->
    if pv `geqPV` TLS_1p2 
    then Some? ske.ske_signed_params.sig_algorithm
    else None? ske.ske_signed_params.sig_algorithm
  | CertificateVerify cv, Some pv ->
    if pv `geqPV` TLS_1p2 
    then Some? cv.sig_algorithm
    else None? cv.sig_algorithm
  | _ -> true )

(** is this message valid? ad hoc value dependency *)
let valid_hs_msg (pv:option protocolVersion): Type0 = 
  msg: hs_msg{valid_hs_msg_prop pv msg}

(** is this message parsed? *)
let parsed = function
  | Binders _ | MessageHash _ -> false
  | _ -> true

val handshakeMessageBytes:
  pvo:option protocolVersion ->
  msg:valid_hs_msg pvo ->
  Tot (b:bytes {parsed msg ==> (exists (ht:handshakeType). hs_msg_bytes ht b)})

val handshakeMessageBytes_is_injective: 
  pv:option protocolVersion -> 
  msg1:valid_hs_msg pv -> 
  msg2:valid_hs_msg pv -> Lemma 
  (requires equal (handshakeMessageBytes pv msg1) (handshakeMessageBytes pv msg2))
  (ensures msg1 == msg2)

val handshakeMessagesBytes: pv:option protocolVersion -> list (msg:valid_hs_msg pv) -> bytes
// we may need to expose its definition to HandshakeLog

val handshakeMessagesBytes_is_injective: 
  pv: option protocolVersion -> 
  l1: list (msg:valid_hs_msg pv) -> 
  l2: list (msg:valid_hs_msg pv) -> Lemma 
  (requires equal (handshakeMessagesBytes pv l1) (handshakeMessagesBytes pv l2))
  (ensures l1 = l2)

val string_of_handshakeMessage: hs_msg -> Tot string

// underspecified?
val parseHandshakeMessage:
  option protocolVersion ->
  option kexAlg ->
  ht:handshakeType ->
  b:bytes{repr_bytes (length b) <= 3} ->
  Tot (result hs_msg)
