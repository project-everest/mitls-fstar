module Negotiation

/// Negotiates the TLS parameters for connection establishment, based
/// on the local configuration and the peer's hello message.
///
/// Defines datatypes holding the TLS parameters: [offer] and [mode]
/// used in Handshake, FFI, QUIC.

// What's an appropriate abstraction for this interface? Provide both
// pure specs and the supporting state machine? Keep offer and mode
// transparent?

// application-specific negotation relies on a callback in the
// configuration.

open FStar.Error
open FStar.Bytes

open Mem
open TLSError
open TLSInfo
open TLSConstants
open HandshakeMessages

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module LP = LowParse.Low.Base
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

val print_namedGroupList
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
: HST.Stack unit
  (requires (fun h -> LP.valid Parsers.NamedGroupList.namedGroupList_parser h sl pos))
  (ensures (fun h _ h' -> B.modifies B.loc_none h h'))


type pre_share = g:CommonDH.group & CommonDH.pre_share g
type share = g:CommonDH.group & CommonDH.share g

let offer = HandshakeMessages.ch 

(*
  We keep both the server's HelloRetryRequest
  and the overwritten parts of the initial offer
*)
type retryInfo (offer:offer) =
  hrr *
  list pre_share (* we should actually keep the raw client extension content *) *
  list Extensions.pskIdentity

val find_cookie: offer -> option (b:bytes {0 < length b /\ length b < 65536})
val find_psk_key_exchange_modes: offer -> list Extensions.pskKeyExchangeMode // [] when not found; pick better representation?
val find_sessionTicket: offer -> option bytes // TODO refine
val find_clientPske: offer -> option Extensions.offeredPsks 

// index in the list of PSKs offered by the client
type pski (o:offer) = n:nat {
  // o.ch_protocol_version = TLS_1p3 /\ // 19-01-04  was mistaken?
  (match find_clientPske o with
  | Some psks -> n < List.length psks.Extensions.identities
  | _ -> False) }

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
    n_protocol_version: protocolVersion ->
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
    n_client_cert_request: option HandshakeMessages.cr ->
    n_server_cert: option (Cert.chain13 * signatureScheme) ->

    // more from either CH+SH (1.3) or CKE (1.2)
    n_client_share: option share ->
    // { both shares are in the same negotiated group }
    mode

//19-01-23 collecting refinements we may need
// m.n_protocol_version is supported 
// m.n_protocol_version = TLS_1p2 ==> CipherSuite? m.n_cipher_suite 


type resumeInfo =
  option (psk_identifier * t:Ticket.ticket{Ticket.Ticket12? t}) *
  list (psk_identifier * t:Ticket.ticket{Ticket.Ticket13? t})

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

  | C_HRR:      n_offer: offer ->
                n_hrr: retryInfo n_offer ->
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

  // Waiting for ClientHello2
  | S_HRR:      n_offer: offer ->
                n_hrr: hrr ->
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

type reader 'a = 
  #region:rgn -> #role:TLSConstants.role -> ns:t region role -> ST 'a 
  (requires (fun h0 -> h0 `HS.contains` ns.state ))
  (ensures (fun h0 _ h1 -> h0 == h1))

// For QUIC, the handshake signals it is returning HRR (to issue a special packet type)
val is_server_hrr: reader bool 

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

val getMode: reader mode

(* Returns the negotiated version, when known, or cfg.max_version *)
val version: reader protocolVersion 
val is_hrr: reader bool

// TODO 19-01-06 effect of signing
val sign: 
  #region:rgn -> #role:TLSConstants.role -> ns:t region role -> 
  bytes -> 
  ST (result HandshakeMessages.signature)
  (requires (fun h0 -> h0 `HS.contains` ns.state ))
  (ensures (fun h0 _ h1 -> h0 == h1))


(* CLIENT *) 

val client_ClientHello: 
  #region:rgn -> t region Client -> 
  oks:option Extensions.keyShareClientHello -> 
  St (result offer)
  // [C_Init ==> C_Offer]
  // ensures offer = client_offer ns.cfg ns.nonce oks ns.resume now [used e.g. for binder auth] 
  // oks: optional client key shares created by ks_client_init
  // now: stateful time for age obfuscation (return it ghostly?)

val group_of_hrr: HandshakeMessages.hrr -> option CommonDH.namedGroup

val client_HelloRetryRequest:
  #region:rgn -> t region Client -> 
  hrr -> 
  option share -> 
  St (result offer) 
  // [C_Offer ==> C_HRR] TODO separate pure spec
  
val client_ServerHello: 
  #region:rgn -> 
  t region Client ->
  HandshakeMessages.sh ->
  St (result mode) 
  // [C_Offer | C_HRR_offer ==> C_Mode] with TODO hrr.  
  // ensures client_mode ns offer sh == Correct mode

// used internally, but also directly called by Handshake 
val to_be_signed: 
  pv:protocolVersion -> 
  role -> 
  csr:option (lbytes 64) -> 
  tbs:bytes {(None? csr <==> pv == TLS_1p3) /\ Bytes.length tbs <= 128} -> 
  bytes

val client_ServerKeyExchange: 
  #region:rgn -> t region Client ->
  serverCert:HandshakeMessages.crt ->
  HandshakeMessages.ske ->
  ocr:option HandshakeMessages.cr ->
  St (result mode)
  // [C_Mode ==> C_Mode] setting [server_share; client_cert_request; server_cert] in mode,
  // requires mode.n_protocol_version = TLS_1p2

val clientComplete_13: 
  #region:rgn -> t region Client ->
  ee: HandshakeMessages.ee ->
  optCertRequest: option HandshakeMessages.cr13 ->
  optServerCert: option Cert.chain13 -> // Not sent with PSK
  optCertVerify: option HandshakeMessages.cv -> // Not sent with PSK
  digest: option (b:bytes{length b <= 32}) ->
  St (result mode) // it needs to be computed, whether returned or not
  // [C_Mode ==> C_Complete] setting [sexts optCertRequest schain] in mode and recording [ccert]
  // ensures schain-based server authentication of the mode (including sexts) 
  // ensures consistency of sexts and schain with the offer.
  // TODO client sigs; till then ccert=None and optCertRequest is ignored.


(* SERVER *) 

// For application-handled extensions set by nego callback,
// such as QUIC transport parameters
type extra_sext = list (s:Extensions.encryptedExtension{Extensions.EE_Unknown_extensionType? s})

//17-03-30 still missing a few for servers.
noeq type serverMode =
  | ServerHelloRetryRequest: hrr:hrr ->
    cs:cipherSuite{name_of_cipherSuite cs = hrr.hrr_cipher_suite} ->
    serverMode
  | ServerMode: mode -> certNego -> extra_sext -> serverMode

(* Returns the server name, if any, or an empty bytestring; review. *)
val get_sni: offer -> Tot bytes 

(* for QUIC *) 
val get_alpn: offer -> Tot Extensions.clientHelloExtension_CHE_application_layer_protocol_negotiation

val server_ClientHello: 
  #region:rgn -> t region Server ->
  HandshakeMessages.ch -> 
  log:HandshakeLog.t ->
  St (result serverMode)
  // [S_Init | S_HRR ==> S_ClientHello m cert] 
  // ensures r = computeServerMode ns.cfg ns.nonce offer (stateful)
  // but [compute_cs13] and [negotiateCipherSuite] are pure. 

/// Complete the server's mode with its DH share
/// (the two-step decomposition enables DH generation from partial mode in-between)
/// 
val server_ServerShare: 
  #region:rgn -> 
  t region Server ->
  oks:option (g:CommonDH.group & CommonDH.pre_share g) -> //19-01-22 to be refined?
  app_exts: extra_sext ->
  St (result mode)
  // [S_ClientHello ==> S_Mode] setting [sexts, oks] in mode
  // requires oks is consistent with mode (?)
  // ensures sexts = server_negotiateExtensions ns mode cexts @ app_exts
  // review their ordering, and how QD separates them


//17-03-30 get rid of this wrapper?
noeq type session = {
  session_nego: option mode;
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
