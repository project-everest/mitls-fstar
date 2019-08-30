module Negotiation

/// Negotiates the TLS parameters for connection establishment,
/// based on the local configuration and the peer's hello message.
///
/// Defines datatypes holding the TLS parameters: [offer] and [mode]
/// used in Handshake, FFI, QUIC.

// What's an appropriate abstraction for this interface? Provide both
// pure specs and the supporting state machine? Keep offer and mode
// transparent?

// Application-specific negotation relies on a callback in the
// configuration.

open FStar.Error
open FStar.Bytes // still used for cookies, tickets, signatures... 

open Mem
open TLSError
open TLSInfo
open TLS.Callbacks
open TLSConstants

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

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

let implemented_version = pv:protocolVersion {pv = TLS_1p2 || pv = TLS_1p3}

type pre_share = g:CommonDH.group & CommonDH.pre_share g
type share = g:CommonDH.group & CommonDH.share g

let offer = HSM.clientHello

(*
  After issuing/receiving the second ClientHello, 
  we keep both the server's HelloRetryRequest
  and the overwritten parts of the initial offer.
*)
type retryInfo (offer:offer) =
  HSM.hrr *
  list pre_share (* we should actually keep the raw client extension content *) *
  list Extensions.pskIdentity

val find_cookie: offer -> option Extensions.cookie 
val find_psk_key_exchange_modes: offer -> list Extensions.pskKeyExchangeMode // [] when not found; pick better representation?
val find_sessionTicket: offer -> option Extensions.clientHelloExtension_CHE_session_ticket 
val find_clientPske: offer -> option Extensions.offeredPsks 
val find_serverKeyShare: HSM.sh -> option pre_share 

// the type of correct indexes into the list of PSKs offered by the client
type pski (o:offer) = n:nat {
  // o.ch_protocol_version = TLS_1p3 /\ // 19-01-04  was mistaken?
  (match find_clientPske o with
  | None -> False
  | Some psks -> 
    n < List.length psks.Extensions.identities /\ 
    n < 65536 (* uint16 *)
  )}

type cr =
| NoRequest
| CertRequest12 of HSM.certificateRequest12
| CertRequest13 of HSM.certificateRequest13

(**
  The final negotiated outcome, including key shares and long-term identities.
  mode is the name used in the resilience paper;
  session_info is the one from TLSInfo
*)
// can we make it abstract? get rid of accessor functions? used directly in Handshake. 
noeq type mode =
  | Mode:
    n_offer: offer -> // negotiated client offer
    n_hrr: option (retryInfo n_offer) ->  // optional HRR roundtrip

    // more from SH (both TLS 1.2 and TLS 1.3)
    n_protocol_version: implemented_version ->
    n_server_random: TLSInfo.random ->
    n_sessionID: sessionID ->
    n_cipher_suite: cipherSuite ->

    // redundant with the server extension response?
    n_pski: option (pski n_offer) -> // only for TLS 1.3, result of a tricky stateful computation

    // the server extensions are split. 
    n_server_extensions: Extensions.serverHelloExtensions ->
    n_encrypted_extensions: option Extensions.encryptedExtensions -> 

    // more from SKE in ...ServerHelloDone (1.2) or SH (1.3)
    n_server_share: option share -> 

    // more from either ...ServerHelloDone (1.2) or ServerFinished (1.3)
    n_client_cert_request: cr ->
    n_server_cert: option (Cert.chain13 * signatureScheme) ->

    // more from either CH+SH (1.3) or CKE (1.2)
    n_client_share: option share ->
    // { both shares are in the same negotiated group }
    mode

(* 19-05-28
// are we better off with a concrete mode? 
// in specs, it avoids existentials;
// in the implementation, we can cache the accepted outcomes of the negotiation:
// { pv, sr, ciphersuite, pski, ... } 

noeq type partial_mode_c13 = {
  n_offer: offer; 
  n_sh: Parsers.ServerHello.serverHello;
  // n_retry: option (initial_retry n_offer n_sh) 
  }
  
noeq type complete_mode13 = { 
  n_offer: offer; 
  n_sh: Parsers.ServerHello.serverHello; 
  n_ee: Parsers.EncryptedExtensions.encryptedExtensions; 
  }
*)

//19-01-23 collecting refinements we may need
// m.n_protocol_version is supported 
// m.n_protocol_version = TLS_1p2 ==> CipherSuite? m.n_cipher_suite 

// move to PSK?

type bkey12 = psk_identifier * t:Ticket.ticket{Ticket.Ticket12? t}
type bkey13 = psk_identifier * t:Ticket.ticket{Ticket.Ticket13? t}
type resumeInfo = option bkey12 * list bkey13

let ha_bkey13 (bk:bkey13) = 
  let _, Ticket.Ticket13 (CipherSuite13 _ ha) li _ _ nonce created age_add custom = bk in 
  ha

// main negotation state (why are we duplicating the nonce? to make it clearly stateless?)
// 19-01-06 how to declare an opaque noeq?

type certNego = option (cert_type * signatureScheme)

val find_early_data: offer -> bool 

noeq type negotiationState (r:role) (cfg:config) : Type0 =
  // Have C_Offer_13 and C_Offer? Shares aren't available in C_Offer yet
  | C_Init:     n_client_random: TLSInfo.random ->
                negotiationState r cfg

  | C_Offer:    n_offer: offer ->
                negotiationState r cfg

  | C_WaitFinished1:
                n_partialmode: mode ->
                negotiationState r cfg

  | C_Mode:     n_mode: mode -> // In 1.2, used for resumption and full handshakes
                negotiationState r cfg

  | C_WaitFinished2: // Only 1.2
                n_mode: mode ->
                n_client_certificate: option Cert.chain13 ->
                negotiationState r cfg

  | C_Complete: n_mode: mode ->
                n_client_certificate: option Cert.chain13 ->
                negotiationState r cfg

  | S_Init:     n_server_random: TLSInfo.random ->
                negotiationState r cfg

  | S_ClientHello: // Transitional state to allow Handshake to call KS and generate a share
                n_mode: mode -> // n_server_share and n_server_extensions are None
                // We ask for a certificate from the PKI library - this is just a handle
                // If a certificate is actually used, it appears in network format in mode.n_server_cert
                n_selected_cert: certNego ->
                negotiationState r cfg

  // This state is used to wait for both Finished1 and Finished2
  | S_Mode:     n_mode: mode -> // If 1.2, then client_share is None
                n_selected_cert: certNego ->
                negotiationState r cfg

  | S_Complete: n_mode: mode ->
                n_client_certificate: option Cert.chain13 ->
                negotiationState r cfg

// assume val ns_rel_monotonic: #r:role -> #cfg:config ->
//   Lemma (Preorder.preorder_rel (ns_rel #r #cfg))

// main negotation state (why are we duplicating the nonce? to make it clearly stateless?)

noeq type t (region:rgn) (role:TLSConstants.role) : Type0 =
  | NS:
    cfg: config -> // local configuration
    resume: resumeInfo ->
    nonce: TLSInfo.random ->
    state: HST.reference (negotiationState role cfg) { HS.frameOf state = region }->
    t region role

val create:
  region:rgn -> 
  r:role -> 
  cfg:config -> 
  nonce: TLSInfo.random -> 
  St (t region r)
  // ensures ns.cfg = cfg /\ ns.nonce = nonce /\ initial state. 

inline_for_extraction
type reader 'a = 
  #region:rgn -> #role:TLSConstants.role -> ns:t region role -> ST 'a 
  (requires (fun h0 -> h0 `HS.contains` ns.state ))
  (ensures (fun h0 _ h1 -> h0 == h1))

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

val getOffer: reader offer
val getMode: reader mode

(* Returns the negotiated version, when known, or cfg.max_version *)
val version: reader protocolVersion 

let footprint
  (#region:rgn) (#role:TLSConstants.role) (ns:t region role)
: GTot B.loc 
= B.loc_mreference ns.state

let inv (#region:rgn) (#role:TLSConstants.role) (ns:t region role) h0 = h0 `HS.contains` ns.state

// signature callback; is it used outside Negotiation? 
// TODO 19-01-06 effect of signing
val sign: 
  #region:rgn -> #role:TLSConstants.role -> ns:t region role -> 
  bytes -> 
  ST (result HandshakeMessages.certificateVerify13)
  (requires fun h0 -> inv ns h0)
  (ensures fun h0 _ h1 -> inv ns h1)


(* CLIENT *) 

let client_config = config * resumeInfo

/// What the client offers, abstractly. 
val client_offer: 
  ccfg: client_config -> 
  nonce:TLSInfo.random -> 
  ks:option Extensions.keyShareClientHello -> 
  now:UInt32.t -> result offer

/// [C_Init ==> C_Offer]
///
/// [oks] are the optional client key shares sampled by [ks_client_init]
///
/// [now] is the current time (an underspecified read effect) used for
/// age obfuscation; we could also return it ghostly or pass it in
/// config.
///
/// Fails when the version is misconfigurated 
/// 
val client_ClientHello: 
  ccfg: client_config ->
  nonce: TLSInfo.random -> 
  oks:option Extensions.keyShareClientHello -> 
  ST (result offer)
  (requires fun h0 -> True)  
  (ensures fun h0 r h1 -> 
    B.modifies B.loc_none h0 h1 /\
    (exists (now:UInt32.t). (r = client_offer ccfg nonce oks now)))

// deprecated--use TLS.Cookie.find_keyshare 
val group_of_hrr: HSM.hrr -> option CommonDH.namedGroup

// Pure spec of computing CH2 from CH1+HRR
val client_HelloRetryRequest:
  ch1: offer ->
  hrr: HSM.hrr -> 
  s: share -> 
  result (retryInfo ch1 & offer)

// Pure spec of checking retry consistency
val check_retry:
  ch1: offer ->
  ri: retryInfo ch1 ->
  sh: HSM.sh ->
  (result unit)

/// What the client accepts, abstractly.
///
/// This mode is still partial.
/// Do we need some spec-level matching with the server's mode?
///
///   let offer = client_offer client cfg in 
///   let server_mode = computeServerMode server_cfg offer sr in
///   let sh = Handshake.serverHello server_mode in 
///   let client_mode = accept_ServerHello client_cfg offer sh in
///   server_mode == client_mode // excluding encrypted extensions, server_cert, etc 

//19-08-20  newer simpler call; the two below will probably go
val client_accept_ServerHello: 
  config -> 
  offer: offer -> 
  HSM.sh -> 
  result (cipherSuite * option (pski offer))

val accept_ServerHello: 
  config -> 
  offer: offer -> 
  HSM.sh -> 
  result (m:mode {m.n_offer == offer})

/// [C_Offer ==> C_Mode]
///
/// Fails if the server's choices are unacceptable
/// 
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

/// Formatting of the server's signed information: called by Handshake
/// for signing, called by Negotiation for verification,
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
  csr:option (lbytes 64) -> 
  tbs:bytes {(None? csr <==> pv == TLS_1p3) /\ Bytes.length tbs <= 128} -> 
  bytes


val client_ServerKeyExchange: 
  #region:rgn -> ns: t region Client ->
  serverCert:HandshakeMessages.certificate12 ->
  kex: Parsers.KeyExchangeAlgorithm.keyExchangeAlgorithm ->
  ske: HandshakeMessages.serverKeyExchange kex ->
  ocr:option HandshakeMessages.certificateRequest12 ->
  ST (result mode)
  (requires fun h0 -> inv ns h0) 
  (ensures fun h0 _ h1 -> inv ns h1) 
  // [C_Mode ==> C_Mode] setting [server_share; client_cert_request; server_cert] in mode,
  // requires mode.n_protocol_version = TLS_1p2

//$ align name to Handshake machine; strengthen post-condition using server Finished1.
val clientComplete_13: 
  #region:rgn -> ns:t region Client ->
  ee: HandshakeMessages.encryptedExtensions ->
  optCertRequest: option HandshakeMessages.certificateRequest13 ->
  optServerCert: option Cert.chain13 -> // Not sent with PSK
  optCertVerify: option HandshakeMessages.certificateVerify13 -> // Not sent with PSK
  digest: option (b:bytes{length b <= 32}) ->
  ST (result mode) // it needs to be computed, whether returned or not
  (requires fun h0 -> 
    inv ns h0 /\ (match HS.sel h0 ns.state with
    | C_Mode m -> m.n_protocol_version = TLS_1p3
    | _ -> False ))
  (ensures fun h0 _ h1 -> True)
  // [C_Mode ==> C_Complete] setting [sexts optCertRequest schain] in mode and recording [ccert]
  // ensures schain-based server authentication of the mode (including sexts) 
  // ensures consistency of sexts and schain with the offer.
  // TODO client sigs; till then ccert=None and optCertRequest is ignored.
  // 19-04-19 TODO inv preservation through callbacks?


(* SERVER *) 


//17-03-30 still missing a few for servers.
module HRR = Parsers.HelloRetryRequest

noeq type serverMode =
  | ServerMode: mode -> certNego -> Extensions.unknownExtensions -> serverMode
  | ServerRetry: TLS.Cookie.(hrr_leq extensions_max_length) -> serverMode

(* Returns the server hostName, if any, or an empty bytestring; review. *)
val get_sni: offer -> Tot bytes 

(* for QUIC *) 
val get_alpn: offer -> Tot Extensions.clientHelloExtension_CHE_application_layer_protocol_negotiation

val trace_offer: HSM.clientHello ->
  ST unit
  (requires fun h0 -> True)
  (ensures fun h0 () h1 -> h0 == h1)

// When receiving CH2
val server_ClientHello2:
  #region:rgn -> ns: t region Server ->
  ch1: HSM.clientHello -> 
  hrr: HSM.hrr -> 
  ch2: HSM.clientHello -> 
  app_cookie: bytes ->
  ST (result serverMode)
  (requires fun h0 -> inv ns h0)
  (ensures fun h0 r h1 -> 
    inv ns h1 /\ 
    B.(modifies (loc_mreference ns.state) h0 h1) /\ 
    ( 
    let s1 = HS.sel h1 ns.state in 
    match r, s1 with 
    | Error _, _ -> True
    | Correct _, S_ClientHello _ _ -> True
    | _ -> False ))

// When receiving CH1 or CH2[CH1 cookie]
val server_ClientHello: 
  #region:rgn -> ns: t region Server ->
  HSM.clientHello -> 
  ST (result serverMode)
  (requires fun h0 -> 
    inv ns h0 /\ 
    (let s = HS.sel h0 ns.state in S_Init? s))
  (ensures fun h0 _ h1 -> 
    inv ns h1
    // TODO modifies at least the transcript 
    )
  // [S_Init ==> S_ClientHello m cert] 
  // ensures r = computeServerMode ns.cfg ns.nonce offer (stateful)
  // but [compute_cs13] and [negotiateCipherSuite] are pure. 

/// Complete the server's mode with its DH share
/// (the two-step decomposition enables DH generation from partial mode in-between)
/// 
val server_ServerShare: 
  #region:rgn -> ns: t region Server ->
  oks:option (g:CommonDH.group & CommonDH.pre_share g) -> //19-01-22 to be refined?
  app_exts: Extensions.unknownExtensions ->
  ST (result mode)
  (requires fun h0 -> 
    inv ns h0 /\ 
    (let s = HS.sel h0 ns.state in S_ClientHello? s))
  (ensures fun h0 _ h1 -> inv ns h1) 
  // [S_ClientHello ==> S_Mode] setting [sexts, oks] in mode
  // requires oks is consistent with mode (?)
  // ensures sexts = server_negotiateExtensions ns mode cexts @ app_exts
  // review their ordering, and how QD separates them









//17-03-30 get rid of this wrapper?
noeq type session = {
  session_nego: option mode;
}

/// Still used in Old.Epoch

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
