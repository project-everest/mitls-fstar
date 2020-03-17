module Negotiation

/// Negotiates the TLS parameters for connection establishment,
/// based on the local configuration and the peer's hello message.
///
/// Application-specific negotation relies on callbacks recorded in
/// the configuration.

open FStar.Error
// open FStar.Bytes // still used for cookies, tickets, signatures...

open Mem
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open TLSError
open TLSInfo
open TLS.Callbacks
open TLSConstants

module HSM = HandshakeMessages
module LP = LowParse.Low.Base

//19-05-04 sample low-level printer, not used so far. Not extracted ?!
val print_namedGroupList
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: UInt32.t)
: HST.Stack unit
  (requires (fun h -> LP.valid Parsers.NamedGroupList.namedGroupList_parser h sl pos))
  (ensures (fun h _ h' -> B.modifies B.loc_none h h'))

val string_of_hrres: Parsers.HRRExtensions.hRRExtensions -> string
val string_of_ees: Parsers.EncryptedExtensions.encryptedExtensions -> string

// duplicating Negotiation.Version, for visibility
let implemented_version = pv:protocolVersion {pv == TLS_1p2 \/ pv == TLS_1p3}

inline_for_extraction
val selected_version: HSM.sh -> result Parsers.ProtocolVersion.protocolVersion

type pre_share = g:CommonDH.group & CommonDH.pre_share g
type share = g:CommonDH.group & CommonDH.share g

let offer = HSM.clientHello

val find_signature_algorithms: offer -> option signatureSchemeList
val find_cookie: offer -> option Extensions.cookie

// [] when not found; pick better representation?
val find_psk_key_exchange_modes: offer -> list Extensions.pskKeyExchangeMode

val find_sessionTicket: offer -> option Extensions.clientHelloExtension_CHE_session_ticket

// finding the pre-shared keys in ClientHello.
// Note we only consider the *last* extension.
// Use instead ch_psks when the extension is known to exist.
val find_clientPske: offer -> option Extensions.offeredPsks

val find_serverPske: HSM.sh -> option UInt16.t
val find_supported_groups: offer -> option Extensions.namedGroupList
val find_serverKeyShare: HSM.sh -> option pre_share
val find_clientKeyShares: offer -> option Extensions.keyShareClientHello
val find_early_data: offer -> bool

// Returns the server hostName, if any, or an empty bytestring; review.
val get_sni: offer -> Tot Bytes.bytes

// for QUIC
val get_alpn: offer -> Tot Extensions.clientHelloExtension_CHE_application_layer_protocol_negotiation

/// HASH ALGORITHM NEGOTIATION.
///
/// We distinguish a "main" offered algorithm, depending on first PSK
/// or first ciphersuite. (Unclear what to do when the two disagree.)

val offered_ha: offer -> EverCrypt.Hash.alg

/// Selected algorithm, overwritten in SH (here) or HRR [HSM.hrr_ha]

// capturing correlation with the selected protocol version.
type selected_cs_t (sh:HSM.sh) = c:cipherSuite {
  match selected_version sh with
  | Correct TLS_1p2 -> CipherSuite? c
  | Correct TLS_1p3 -> CipherSuite13? c
  | _ -> False }
  
val selected_ha: HSM.serverHello -> EverCrypt.Hash.alg
val selected_cipher_suite: sh:HSM.sh -> selected_cs_t sh

/// CLIENT CERTIFICATE REQUESTS are currently disabled.

type cr =
| NoRequest
| CertRequest12 of HSM.certificateRequest12
| CertRequest13 of HSM.certificateRequest13


/// PSK NEGOTIATION.
///
/// The client optionally offers a list of PSKs in its last extension.
/// The server responds with an index into that list iff it selects a
/// PSK-based key exchange.

// the type of correct indexes into the list of PSKs offered by the client
type pski (o:offer) = n:UInt16.t {
  match find_clientPske o with
  | None -> False
  | Some psks ->
    UInt16.v n < List.length psks.Extensions.identities }

// Hide those details in PSK?
type bkey12 = psk_identifier * t:Ticket.ticket{Ticket.Ticket12? t}
type bkey13 = psk_identifier * t:Ticket.ticket{Ticket.Ticket13? t}
type resumeInfo = option bkey12 * list bkey13
let ha_bkey13 (bk:bkey13) =
  let _, Ticket.Ticket13 (CipherSuite13 _ ha) li _ _ nonce created age_add custom = bk in
  ha

val unseal_tickets: config ->
  ST resumeInfo
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> h0 == h1)

(*
val hashAlg: mode -> Hashing.Spec.alg
val kexAlg: mode -> TLSConstants.kexAlg
val aeAlg:
  m:mode{CipherSuite? m.n_cipher_suite \/ CipherSuite13? m.n_cipher_suite} ->
  TLSConstants.aeAlg
val emsFlag: mode -> bool

// used only for TLS 1.2. FIXME: properly negotiate
val chosenGroup: m:mode {
  match kexAlg m with
  | Kex_PSK_DHE
  | Kex_DHE
  | Kex_PSK_ECDHE
  | Kex_ECDHE -> True
  | _ -> False } -> option CommonDH.group

// avoid?
val zeroRTToffer: offer -> bool
val zeroRTT: mode -> bool

val sendticket_12: mode -> bool
val resume_12: mode -> bool

val local_config:
  #region:rgn -> #role:TLSConstants.role -> t region role ->
  Tot config

val nonce:
  #region:rgn -> #role:TLSConstants.role -> t region role ->
  Tot TLSInfo.random

val resume:
  #region:rgn -> #role:TLSConstants.role -> t region role ->
  Tot resumeInfo


let footprint
  (#region:rgn) (#role:TLSConstants.role) (ns:t region role)
: GTot B.loc
= B.loc_mreference ns.state

let inv (#region:rgn) (#role:TLSConstants.role) (ns:t region role) h0 = h0 `HS.contains` ns.state

// signature callback; is it used outside Negotiation?
// TODO 19-01-06 effect of signing
val sign:
  #region:rgn ->
  #role:TLSConstants.role ->
  ns:t region role ->
  bytes ->
  ST (result HandshakeMessages.certificateVerify13)
  (requires fun h0 -> inv ns h0)
  (ensures fun h0 _ h1 -> inv ns h1)
*)

(*** Extensions *)

val server_clientExtensions:
  protocolVersion -> 
  config -> 
  cipherSuite -> 
  option (cVerifyData * sVerifyData) -> 
  option (pski:UInt16.t) -> 
  option Extensions.serverHelloExtension_SHE_key_share -> 
  bool -> 
  Parsers.ClientHelloExtensions.clientHelloExtensions ->
  Parsers.ServerHelloExtensions.serverHelloExtensions

val encrypted_clientExtensions:
  protocolVersion -> 
  config -> 
  cipherSuite -> 
  option (cVerifyData * sVerifyData) -> 
  option (pski:UInt16.t) -> 
  option Extensions.serverHelloExtension_SHE_key_share -> 
  bool -> 
  Parsers.ClientHelloExtensions.clientHelloExtensions ->
  Parsers.EncryptedExtensions.encryptedExtensions

(*** CLIENT *)

let client_config = config * resumeInfo

/// The server's decision to accept or reject 0RTT application data.

val zeroRTT: HSM.sh -> bool

/// What the client initially offers based on its configuration.
/// May fail on misconfigurations, e.g. offering only TLS 1.0.

//lower noextract
val client_offer:
  ccfg: client_config ->
  nonce:TLSInfo.random ->
  oks:option Extensions.keyShareClientHello ->
  now:UInt32.t -> result offer

/// [C_Init ==> C_Offer]
///
/// [ks] are the optional client key shares sampled by
/// [ks_client_init], present when the client offers TLS 1.3 EDH.
///
/// [now] is the current time (an underspecified read effect) used for
/// age obfuscation; we could also pass it in config, or return it
/// ghostly.
///
/// Fails on misconfigurations and (later) on buffer overflows.

val client_ClientHello:
  ccfg: client_config ->
  nonce: TLSInfo.random ->
  oks:option Extensions.keyShareClientHello ->
  ST (result offer)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    B.modifies B.loc_none h0 h1 /\
    (exists (now:UInt32.t). (r == client_offer ccfg nonce oks now)))

//deprecated--use TLS.Cookie.find_keyshare
val group_of_hrr: HSM.hrr -> option CommonDH.namedGroup //(ng: namedGroup {Some? (group_of_namedGroup ng)})

/// In case the client receives an HellowRetryRequest, it tries to
/// issue a revised offer, and it later check the second ServerHello
/// is compatible with the initial ClientHello-HelloRetryRequest
/// roundtrip.

//lower noextract
val client_HelloRetryRequest:
  ch1: offer ->
  hrr: HSM.hrr ->
  s: option share ->
  now: UInt32.t -> // to update obfuscated_age
  resume: resumeInfo -> // to filter PSKs
  result (o:offer { HSM.is_valid_hrr hrr })

val client_accept_second_ServerHello:
  ch1: offer ->
  hrr: HSM.valid_hrr ->
  ch2: offer ->
  sh: HSM.sh ->
  result unit

/// [C_Offer | C_HRR_offer ==> C_Mode]
///
/// Fails if the server's choices are unacceptable
///
/// In case the client receives an actual ServerHello, it checks that
/// the server's choices are compatible with its offer. Those checks
/// apply irrespective of an earlier ClientHello-HelloRetryRequest
/// roundtrip.
///
/// Do we need some spec-level matching with the server's mode?
///
///   let offer = client_offer client cfg in
///   let server_mode = computeServerMode server_cfg offer sr in
///   let sh = Handshake.serverHello server_mode in
///   let client_mode = accept_ServerHello client_cfg offer sh in
///   server_mode == client_mode // excluding encrypted extensions, server_cert, etc

//lower noextract
val client_accept_ServerHello:
  config ->
  offer: offer ->
  sh: HSM.sh ->
  result (c:selected_cs_t sh * option (pski offer))

(*
val accept_ServerHello:
  config ->
  offer: offer ->
  HSM.sh ->
  result (m:mode {m.n_offer == offer})

val client_ServerHello:
  #region:rgn -> ns: t region Client ->
  sh: HSM.sh ->
  ST (result mode)
  (requires fun h0 ->
    inv ns h0 /\
    C_Offer? (HS.sel h0 ns.state))
  (ensures fun h0 r h1 ->
    let C_Offer offer = HS.sel h0 ns.state in
    inv ns h1 /\
    // r == accept_ServerHello ns.cfg offer sh /\
    // would not work (structural subtyping)
    ( match r, accept_ServerHello ns.cfg offer sh with
      | Correct m0, Correct m1 -> HS.sel h1 ns.state == C_Mode m0 /\ m0 == m1
      | Error z0, Error z1     -> z0 == z1
      | _                      -> False))
*)


/// Formatting the server's signed information: called by Handshake
/// for signing; called by Negotiation for verification.
///
/// We can implement the two functions separately, but still need
/// joint injectivity relying on honest nonces never being zero.
///
/// Can we use QD/LP?
///
/// if pv = TLS_1p3
/// then
///   tbs is transcript hash up to Certificate
///   injective on (role and tbs), of total size 64 + 34 + tbs
/// else
///   csr is clientRandom @ serverRandom, tbs is the raw DH share,
///   injective on (csr, tbs), of total size 64 + tbs

val to_be_signed:
  pv:protocolVersion ->
  role ->
  csr:option (Bytes.lbytes 64) ->
  tbs:Bytes.bytes {(None? csr <==> pv == TLS_1p3) /\ Bytes.length tbs <= 128} ->
  Bytes.bytes

(*
val client_ServerKeyExchange:
  serverCert:HandshakeMessages.certificate12 ->
  kex: Parsers.KeyExchangeAlgorithm.keyExchangeAlgorithm ->
  ske: HandshakeMessages.serverKeyExchange kex ->
  ocr:option HandshakeMessages.certificateRequest12 ->
  ST (result mode)
  (requires fun h0 -> inv ns h0)
  (ensures fun h0 _ h1 -> inv ns h1)
  // [C_Mode ==> C_Mode] setting [server_share; client_cert_request; server_cert] in mode,
  // requires mode.n_protocol_version = TLS_1p2
*)

//$ align name to Handshake machine; strengthen post-condition using server Finished1.

/// Process the encrypted server messages:
/// - calls back for the application for processing unknown extensions (may fail)
/// - when present, verify server certificate and signature
///
/// (conversely, the Finished message is verified by Handshake.Client)
///
// val clientComplete_13:
//   // #region:rgn -> ns:t region Client ->
//   config ->
//   offer ->
//   kexAlg ->
//   ee: HandshakeMessages.encryptedExtensions ->
//   // optCertRequest: option HandshakeMessages.certificateRequest13 ->
//   sigdata: option (
//     Cert.chain13 *
//     option HandshakeMessages.certificateVerify13 *
//     (b:bytes{length b <= 32})) ->
//   ST (result unit) // needs to be computed, whether returned or not
//   (requires fun h0 -> True)
//   (ensures fun h0 _ h1 -> B.modifies B.loc_none h0 h1)
//   // [C_Mode ==> C_Complete] setting [sexts optCertRequest schain] in mode and recording [ccert]
//   // ensures schain-based server authentication of the mode (including sexts)
//   // ensures consistency of sexts and schain with the offer.
//   // TODO client sigs; till then ccert=None and optCertRequest is ignored.
//   // 19-04-19 TODO inv preservation through callbacks?




(* SERVER *)

module HRR = Parsers.HelloRetryRequest

let names_group_of gns ((| g, _ |): share) = 
  match CommonDH.namedGroup_of_group g with
  | None -> false 
  | Some gn -> List.Tot.mem gn gns

// TODO: strengten property to prove that the share itself is included
// in the offer.
type selected_share cfg offer = 
  s: share { 
    cfg.named_groups `names_group_of` s /\ 
    ( match find_supported_groups offer with
      | Some ngs -> ngs `names_group_of` s 
      | None -> False ) }

let names_cs13 ncss (cs: cipherSuite): bool =
  CipherSuite13? cs && 
  List.Tot.mem (name_of_cipherSuite cs) ncss 

type selected_cs cfg offer = 
  cs: cipherSuite13 { 
    List.Tot.mem cs cfg.cipher_suites /\ 
    offer.HSM.cipher_suites `names_cs13` cs }

type cs13 server_cert cfg offer =
  | PSK_EDH: 
    j: pski offer -> 
    cks: option (selected_share cfg offer) ->
    cs: selected_cs cfg offer -> cs13 server_cert cfg offer
  | JUST_EDH: 
    cks: selected_share cfg offer -> 
    cs: selected_cs cfg offer { b2t server_cert } ->
    cs13 server_cert cfg offer

// Represents the abstract choice of a certificate by the application
// FIXME refine with TLS.Callbacks.cert_selected cfg o
type cert_choice = cert_type * signatureScheme

// The outcome of server negotiation
type server_choice (cfg:config) (o:offer) =
| ServerAccept12:
  cert: cert_choice ->
  cs: cipherSuite{CipherSuite? cs} ->
  server_choice cfg o
| ServerResume12:
  ticket: bkey12 ->
  server_choice cfg o
| ServerAccept13:
  cert: option cert_choice ->
  cs13: cs13 (Some? cert) cfg o ->
  opsk: option bkey13 ->
  server_choice cfg o
| ServerRetry:
  hrr: HSM.hrr ->
  server_choice cfg o

// Print information about the client offer
val trace_offer: HSM.clientHello ->
  ST unit
  (requires fun h0 -> True)
  (ensures fun h0 () h1 -> h0 == h1)

// When receiving CH1 or CH2[CH1 cookie]
val server_ClientHello:
  cfg: config ->
  offer: HSM.ch ->
  ST (result (server_choice cfg offer))
  (requires fun h0 -> True)
  (ensures fun h0 r h1 ->
    B.modifies B.loc_none h0 h1 /\
    (match r with
    | Correct (ServerResume12 _) -> True
    | Correct (ServerAccept13 _ _ _) -> True
    | Correct (ServerRetry _) -> True
    | _ -> True))

// Still used in Old.Epoch

noeq type session = {
  session_nego: option unit // mode;
}

// represents the outcome of a successful handshake,
// providing context for the derived epoch
noeq type handshake =
  | Fresh of session // was sessionInfo
  | Resumed of session // was abbrInfo * sessionInfo
// We use SessionInfo as unique session indexes.
// We tried using instead hs, but this creates circularities
// We'll probably need a global log to reason about them.
// We should probably do the same in the session store.

/// QUIC uses ch accessors:
/// Negotiation.get_sni
/// Negotiation.get_alpn
/// Negotiation.find_clientPske
/// Negotiation.find_cookie
///
/// Negotiation.zeroRTToffer mode.Negotiation.n_offer
/// Negotiation.zeroRTT mode
