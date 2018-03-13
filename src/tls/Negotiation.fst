module Negotiation

open FStar.Error
open FStar.Bytes

open Mem
open TLSError
open TLSInfo
open TLSConstants
open HandshakeMessages

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

//16-05-31 these opens are implementation-only; overall we should open less
open Extensions
open CoreCrypto

(**
  Debugging flag.
  F* normalizer will erase debug prints at extraction when set to false.
*)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("NGO| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_NGO then print else (fun _ -> ())


//17-05-01 relocate these printing functions?!
let string_of_option_extensions (o: option extensions) = match o with
  | None -> "None"
  | Some es -> "[ "^Extensions.string_of_extensions es^"]"

let string_of_ciphersuite (cs:cipherSuite) =
  match name_of_cipherSuite cs with
  | Correct TLS_NULL_WITH_NULL_NULL -> "TLS_NULL_WITH_NULL_NULL"

  | Correct TLS_AES_128_GCM_SHA256 -> "TLS_AES_128_GCM_SHA256"
  | Correct TLS_AES_256_GCM_SHA384 -> "TLS_AES_256_GCM_SHA384"
  | Correct TLS_CHACHA20_POLY1305_SHA256 -> "TLS_CHACHA20_POLY1305_SHA256"
  | Correct TLS_AES_128_CCM_SHA256 -> "TLS_AES_128_CCM_SHA256"
  | Correct TLS_AES_128_CCM_8_SHA256 -> "TLS_AES_128_CCM_8_SHA256"

  | Correct TLS_RSA_WITH_NULL_MD5 -> "TLS_RSA_WITH_NULL_MD5"
  | Correct TLS_RSA_WITH_NULL_SHA -> "TLS_RSA_WITH_NULL_SHA"
  | Correct TLS_RSA_WITH_NULL_SHA256 -> "TLS_RSA_WITH_NULL_SHA256"
  | Correct TLS_RSA_WITH_RC4_128_MD5 -> "TLS_RSA_WITH_RC4_128_MD5"
  | Correct TLS_RSA_WITH_RC4_128_SHA -> "TLS_RSA_WITH_RC4_128_SHA"
  | Correct TLS_RSA_WITH_3DES_EDE_CBC_SHA -> "TLS_RSA_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_RSA_WITH_AES_128_CBC_SHA -> "TLS_RSA_WITH_AES_128_CBC_SHA"
  | Correct TLS_RSA_WITH_AES_256_CBC_SHA -> "TLS_RSA_WITH_AES_256_CBC_SHA"
  | Correct TLS_RSA_WITH_AES_128_CBC_SHA256 -> "TLS_RSA_WITH_AES_128_CBC_SHA256"
  | Correct TLS_RSA_WITH_AES_256_CBC_SHA256 -> "TLS_RSA_WITH_AES_256_CBC_SHA256"

  | Correct TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA -> "TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA -> "TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA -> "TLS_DHE_DSS_WITH_AES_128_CBC_SHA"
  | Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA -> "TLS_DHE_RSA_WITH_AES_128_CBC_SHA"
  | Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA -> "TLS_DHE_DSS_WITH_AES_256_CBC_SHA"
  | Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA -> "TLS_DHE_RSA_WITH_AES_256_CBC_SHA"
  | Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA256 -> "TLS_DHE_DSS_WITH_AES_128_CBC_SHA256"
  | Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA256 -> "TLS_DHE_RSA_WITH_AES_128_CBC_SHA256"
  | Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA256 -> "TLS_DHE_DSS_WITH_AES_256_CBC_SHA256"
  | Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA256 -> "TLS_DHE_RSA_WITH_AES_256_CBC_SHA256"

  | Correct TLS_ECDHE_RSA_WITH_RC4_128_SHA -> "TLS_ECDHE_RSA_WITH_RC4_128_SHA"
  | Correct TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA -> "TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA -> "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA"
  | Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256 -> "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256"
  | Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA -> "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA"
  | Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384 -> "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384"

  | Correct TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 -> "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 -> "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 -> "TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384"
  | Correct TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 -> "TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384"

  | Correct TLS_DH_anon_WITH_RC4_128_MD5 -> "TLS_DH_anon_WITH_RC4_128_MD5"
  | Correct TLS_DH_anon_WITH_3DES_EDE_CBC_SHA -> "TLS_DH_anon_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_DH_anon_WITH_AES_128_CBC_SHA -> "TLS_DH_anon_WITH_AES_128_CBC_SHA"
  | Correct TLS_DH_anon_WITH_AES_256_CBC_SHA -> "TLS_DH_anon_WITH_AES_256_CBC_SHA"
  | Correct TLS_DH_anon_WITH_AES_128_CBC_SHA256 -> "TLS_DH_anon_WITH_AES_128_CBC_SHA256"
  | Correct TLS_DH_anon_WITH_AES_256_CBC_SHA256 -> "TLS_DH_anon_WITH_AES_256_CBC_SHA256"

  | Correct TLS_RSA_WITH_AES_128_GCM_SHA256 -> "TLS_RSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_RSA_WITH_AES_256_GCM_SHA384 -> "TLS_RSA_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DHE_RSA_WITH_AES_128_GCM_SHA256 -> "TLS_DHE_RSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DHE_RSA_WITH_AES_256_GCM_SHA384 -> "TLS_DHE_RSA_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DH_RSA_WITH_AES_128_GCM_SHA256 -> "TLS_DH_RSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DH_RSA_WITH_AES_256_GCM_SHA384 -> "TLS_DH_RSA_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DHE_DSS_WITH_AES_128_GCM_SHA256 -> "TLS_DHE_DSS_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DHE_DSS_WITH_AES_256_GCM_SHA384 -> "TLS_DHE_DSS_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DH_DSS_WITH_AES_128_GCM_SHA256 -> "TLS_DH_DSS_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DH_DSS_WITH_AES_256_GCM_SHA384 -> "TLS_DH_DSS_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DH_anon_WITH_AES_128_GCM_SHA256 -> "TLS_DH_anon_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DH_anon_WITH_AES_256_GCM_SHA384 -> "TLS_DH_anon_WITH_AES_256_GCM_SHA384"

  | Correct TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_PSK_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_PSK_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256"

  | Error z -> "Unknown ciphersuite"

let string_of_signatureScheme = function
  | RSA_PKCS1_SHA256       -> "RSA_PKCS1_SHA256"
  | RSA_PKCS1_SHA384       -> "RSA_PKCS1_SHA384"
  | RSA_PKCS1_SHA512       -> "RSA_PKCS1_SHA512"
  | ECDSA_SECP256R1_SHA256 -> "ECDSA_SECP256R1_SHA256"
  | ECDSA_SECP384R1_SHA384 -> "ECDSA_SECP384R1_SHA384"
  | ECDSA_SECP521R1_SHA512 -> "ECDSA_SECP521R1_SHA512"
  | RSA_PSS_SHA256         -> "RSA_PSS_SHA256"
  | RSA_PSS_SHA384         -> "RSA_PSS_SHA384"
  | RSA_PSS_SHA512         -> "RSA_PSS_SHA512"
  //| ED25519                -> "ED25519"
  //| ED448                  -> "ED448"
  | RSA_PKCS1_SHA1         -> "RSA_PKCS1_SHA1"
  | RSA_PKCS1_MD5SHA1         -> "RSA_PKCS1_MD5SHA1"
  | ECDSA_SHA1             -> "ECDSA_SHA1"
  | DSA_SHA1               -> "DSA_SHA1"
  | DSA_SHA256             -> "DSA_SHA256"
  | DSA_SHA384             -> "DSA_SHA384"
  | DSA_SHA512             -> "DSA_SHA512"
  | SIG_UNKNOWN codepoint  -> "UNKNOWN " ^ (print_bytes codepoint)

private
let accum_string_of_signatureSchemes s sa =
    s^(string_of_signatureScheme sa)^" "
let string_of_signatureSchemes sal =
  List.Tot.fold_left accum_string_of_signatureSchemes "" sal

private
let accum_string_of_ciphersuite s cs =
    s ^ "; " ^ string_of_ciphersuite cs
let string_of_ciphersuites csl =
  List.Tot.fold_left accum_string_of_ciphersuite "" csl

(* Negotiation: HELLO sub-module *)
type ri = cVerifyData * sVerifyData

type resumption_offer_12 = // part of resumeInfo
  | OfferNothing
  | OfferTicket of b:bytes{ length b <> 0 }
  | OfferSid of b:bytes { length b <> 0 }
// type resumption_mode_12 (o: resumption_offer_12) = b:bool { OfferNothing? o ==> b = false }

let valid_offer ch =
  True
// There is a pure function computing a ClientHello from an offer (minus the PSK binders)
type offer = ch:HandshakeMessages.ch { valid_offer ch }

let find_client_extension filter o =
  match o.ch_extensions with
  | None -> None
  | Some es -> List.Tot.find filter es

let find_client_extension_aux env filter o =
  match o.ch_extensions with
  | None -> None
  | Some es -> List.Helpers.find_aux env filter es

let find_supported_versions o =
  match find_client_extension Extensions.E_supported_versions? o with
  | None -> None
  | Some (Extensions.E_supported_versions vs) -> Some vs

let find_signature_algorithms o : option signatureSchemeList =
  match find_client_extension Extensions.E_signature_algorithms? o with
  | None -> None
  | Some (Extensions.E_signature_algorithms algs) -> Some algs

let find_signature_algorithms_cert o : option signatureSchemeList =
  match find_client_extension Extensions.E_signature_algorithms_cert? o with
  | None -> None
  | Some (Extensions.E_signature_algorithms_cert algs) -> Some algs

let find_cookie o =
  match find_client_extension Extensions.E_cookie? o with
  | None -> None
  | Some (Extensions.E_cookie c) -> Some c

// finding the pre-shared keys in ClientHello
let find_pske o =
  match find_client_extension Extensions.E_pre_shared_key? o with
  | Some (Extensions.E_pre_shared_key (Extensions.ClientPSK psks _)) -> Some psks
  | _ -> None

let find_psk_key_exchange_modes o =
  match find_client_extension Extensions.E_psk_key_exchange_modes? o with
  | Some (Extensions.E_psk_key_exchange_modes l) -> l
  | _ -> []

let find_sessionTicket o =
  match find_client_extension Extensions.E_session_ticket? o with
  | None -> None
  | Some (Extensions.E_session_ticket b) -> Some b

let find_clientPske o =
  match find_client_extension Extensions.E_pre_shared_key? o with
  | None -> None
  | Some (Extensions.E_pre_shared_key psk) ->
    match psk with
    | ServerPSK _ -> None
    | ClientPSK ids tlen -> Some (ids,tlen)

let find_serverPske sh =
  match sh.sh_extensions with
  | None -> None
  | Some exts ->
    match List.Tot.find E_pre_shared_key? exts with
    | Some (E_pre_shared_key (ServerPSK idx)) -> Some (UInt16.v idx)
    | _ -> None

let find_serverKeyShare sh =
  match sh.sh_extensions with
  | None -> None
  | Some exts ->
    match List.Tot.find E_key_share? exts with
    | Some (E_key_share (CommonDH.ServerKeyShare ks)) -> Some ks
    | _ -> None

// index in the list of PSKs offered by the client
type pski (o:offer) = n:nat {
  o.ch_protocol_version = TLS_1p3 /\
  (match find_clientPske o with
  | Some (ids,_) -> n < List.length ids
  | _ -> False) }

let find_supported_groups o =
  match find_client_extension Extensions.E_supported_groups? o with
  | None -> None
  | Some (Extensions.E_supported_groups gns) -> Some gns

type share = g:CommonDH.group & CommonDH.share g
type pre_share = g:CommonDH.group & CommonDH.pre_share g

let find_key_shares (o:offer)
  : Tot (option (CommonDH.clientKeyShare))
  =
  match find_client_extension Extensions.E_key_share? o with
  | Some (Extensions.E_key_share (CommonDH.ClientKeyShare ks)) -> Some ks
  | _ -> None

private let rec list_of_ClientKeyShare (ks:CommonDH.clientKeyShare)
  : Tot (list pre_share)
  =
  match ks with
  | [] -> []
  | CommonDH.Share g s :: tl -> (|g, s|) :: list_of_ClientKeyShare tl
  | CommonDH.UnknownShare _ _  :: tl -> list_of_ClientKeyShare tl

let gs_of (o:offer) : Tot (list pre_share) =
  match find_key_shares o with
  | Some ksl -> list_of_ClientKeyShare ksl
  | _ -> []

let find_early_data o =
  match find_client_extension Extensions.E_early_data? o with
  | None -> None
  | Some (Extensions.E_early_data maxl) -> Some maxl

(**
  We keep both the server's HelloRetryRequest
  and the overwritten parts of the initial offer
*)
type retryInfo (offer:offer) =
  hrr *
  list pre_share (* we should actually keep the raw client extension content *) *
  list Extensions.pskIdentity

(**
  The final negotiated outcome, including key shares and long-term identities.
  mode is the name used in the resilience paper;
  session_info is the one from TLSInfo
*)
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

    // concatenating SH and EE extensions for 1.3, in wire order.
    n_server_extensions: option (se:list extension{List.Tot.length se < 256}) ->

    // more from SKE in ...ServerHelloDone (1.2) or SH (1.3)
    n_server_share: option share ->

    // more from either ...ServerHelloDone (1.2) or ServerFinished (1.3)
    n_client_cert_request: option HandshakeMessages.cr ->
    n_server_cert: option (Cert.chain13 * signatureScheme) ->

    // more from either CH+SH (1.3) or CKE (1.2)
    n_client_share: option share ->
    // { both shares are in the same negotiated group }
    mode

let find_server_extension filter m =
  match m.n_server_extensions with
  | None -> None
  | Some es -> List.Tot.find filter es

let is_resumption12 m =
  not (is_pv_13 m.n_protocol_version)  &&
  m.n_sessionID = m.n_offer.ch_sessionID

let is_cacheable12 m =
  not (is_pv_13 m.n_protocol_version)  &&
  ( let sid = m.n_sessionID in
    sid <> m.n_offer.ch_sessionID &&
    sid <> empty_bytes)

type certNego = option (cert_type * signatureScheme)

noeq type negotiationState (r:role) (cfg:config) (resume:resumeInfo r) : Type0 =
  // Have C_Offer_13 and C_Offer? Shares aren't available in C_Offer yet
  | C_Init:     n_client_random: TLSInfo.random ->
                negotiationState r cfg resume

  | C_Offer:    n_offer: offer ->
                negotiationState r cfg resume

  | C_HRR:      n_offer: offer ->
                n_hrr: retryInfo n_offer ->
                negotiationState r cfg resume

  | C_WaitFinished1:
                n_partialmode: mode ->
                negotiationState r cfg resume

  | C_Mode:     n_mode: mode -> // In 1.2, used for resumption and full handshakes
                negotiationState r cfg resume

  | C_WaitFinished2: // Only 1.2
                n_mode: mode ->
                n_client_certificate: option Cert.chain13 ->
                negotiationState r cfg resume

  | C_Complete: n_mode: mode ->
                n_client_certificate: option Cert.chain13 ->
                negotiationState r cfg resume

  | S_Init:     n_server_random: TLSInfo.random ->
                negotiationState r cfg resume

  // Waiting for ClientHello2
  | S_HRR:      n_offer: offer ->
                n_hrr: hrr ->
                negotiationState r cfg resume

  | S_ClientHello: // Transitional state to allow Handshake to call KS and generate a share
                n_mode: mode -> // n_server_share and n_server_extensions are None
                // We ask for a certificate from the PKI library - this is just a handle
                // If a certificate is actually used, it appears in network format in mode.n_server_cert
                n_selected_cert: certNego ->
                negotiationState r cfg resume

  // This state is used to wait for both Finished1 and Finished2
  | S_Mode:     n_mode: mode -> // If 1.2, then client_share is None
                n_selected_cert: certNego ->
                negotiationState r cfg resume

  | S_Complete: n_mode: mode ->
                n_client_certificate: option Cert.chain13 ->
                negotiationState r cfg resume

let ns_step (#r:role) (#cfg:config) (#resume:resumeInfo r)
  (ns:negotiationState r cfg resume) (ns':negotiationState r cfg resume) =
  match ns, ns' with
  | C_Init nonce, C_Offer offer -> nonce == offer.ch_client_random
  | C_Offer offer, C_Mode mode -> mode.n_offer == offer
  | C_Offer _, C_Complete _ _ -> True
  | C_Mode _, C_WaitFinished2 _ _ -> True
  | C_Mode _, C_Complete _ _ -> True
  | S_Init _, S_ClientHello _ _ -> True
  | S_ClientHello _ _, S_Mode _ _ -> True
  | _, _ -> ns == ns'

let ns_rel (#r:role) (#cfg:config) (#resume:resumeInfo r)
  (ns:negotiationState r cfg resume) (ns':negotiationState r cfg resume) =
  ns_step ns ns' \/
  (exists ns0. ns_step ns ns0 /\ ns_step ns0 ns')

assume val ns_rel_monotonic: #r:role -> #cfg:config -> #resume:resumeInfo r ->
  Lemma (Preorder.preorder_rel (* (negotiationState r cfg resume) *) (ns_rel #r #cfg #resume))

noeq type t (region:rgn) (role:TLSConstants.role) : Type0 =
  | NS:
    cfg: config -> // local configuration
    resume: TLSInfo.resumeInfo role ->
    nonce: TLSInfo.random ->
    state: HST.m_rref region (negotiationState role cfg resume) ns_rel ->
    t region role

#set-options "--lax"
val computeOffer: r:role -> cfg:config -> resume:TLSInfo.resumeInfo r -> nonce:TLSInfo.random
  -> ks:option CommonDH.keyShare -> list (PSK.pskid * PSK.pskInfo) -> UInt32.t
  -> Tot offer
let computeOffer r cfg resume nonce ks pskinfo now =
  let ticket12, sid =
    match resume, cfg.enable_tickets, cfg.min_version with
    | _, _, TLS_1p3 -> None, empty_bytes // Don't bother sending session_ticket
    // Similar to what OpenSSL does, when we offer a 1.2 ticket
    // we send the hash of the ticket as SID to disambiguate the state machine
    | (Some t, _), true, _ ->
      // FIXME Cannot compute hash in Tot
      //let sid = Hashing.compute Hashing.Spec.SHA256 t
      let sid = if length t <= 32 then t else fst (split t 32ul) in
      Some t, sid
    | (None, _), true, _ -> Some (empty_bytes), empty_bytes
    | _ -> None, empty_bytes in
  // Don't offer EDI if there is no PSK or first PSK doesn't have ED enabled
  let compatible_psk =
    match pskinfo with
    | (_, i) :: _ -> i.allow_early_data // Must be the first PSK
    | _ -> false in
  let extensions =
    Extensions.prepareExtensions
      cfg.min_version
      cfg.max_version
      cfg.cipher_suites
      cfg.peer_name
      cfg.alpn
      cfg.custom_extensions
      // qp
      cfg.extended_master_secret
      cfg.safe_renegotiation
      (compatible_psk && Some? cfg.max_early_data)
      ticket12
      cfg.signature_algorithms
      cfg.named_groups
      None // : option (cVerifyData * sVerifyData)
      ks
      pskinfo
      now
  in
  {
    ch_protocol_version = minPV TLS_1p2 cfg.max_version; // legacy for 1.3
    ch_client_random = nonce;
    ch_sessionID = sid;
    ch_cipher_suites = cfg.cipher_suites;
    // This file is reconstructed from ch_cipher_suites in HandshakeMessages.clientHelloBytes;
    ch_compressions = [NullCompression];
    ch_extensions = Some extensions
  }

val create:
  region:rgn -> r:role -> cfg:config -> resume:TLSInfo.resumeInfo r -> TLSInfo.random ->
  St (t region r)
let create region r cfg resume nonce =
  match r with
  | Client ->
    let state = Mem.ralloc region (C_Init nonce) in
    NS cfg resume nonce state
  | Server ->
    let state = Mem.ralloc region (S_Init nonce) in
    NS cfg resume nonce state

// For QUIC: we need a different signal when returning HRR (special packet type)
let is_server_hrr (#region:rgn) (#role:TLSConstants.role) (ns:t region role) =
  match HST.op_Bang ns.state with
  | S_HRR _ _ -> true
  | _ -> false

// a bit too restrictive: use a single Hash in any given offer
val hashAlg: mode -> Hashing.Spec.alg
let hashAlg m =
  verifyDataHashAlg_of_ciphersuite m.n_cipher_suite

val kexAlg: mode -> TLSConstants.kexAlg
let kexAlg m =
  if is_pv_13 m.n_protocol_version then
    (match m.n_pski with
    | None -> Kex_ECDHE
    | Some _ ->
      if Some? m.n_server_share then Kex_PSK_ECDHE
      else Kex_PSK)
  else
    let CipherSuite kex _ _ = m.n_cipher_suite in
    kex

val aeAlg:
  m:mode{CipherSuite? m.n_cipher_suite \/ CipherSuite13? m.n_cipher_suite} ->
  TLSConstants.aeAlg
let aeAlg m =
  TLSConstants.get_aeAlg m.n_cipher_suite

val emsFlag: mode -> bool
let emsFlag mode =
  if is_pv_13 mode.n_protocol_version then
    true
  else
    match mode.n_offer.ch_extensions with
    | None -> false
    | Some cexts ->
      List.Tot.mem Extensions.E_extended_ms cexts &&
      (match mode.n_server_extensions with
       // called from server_ClientHello
       | None -> true
       // called from client_ServerHelloDone
       | Some sexts -> List.Tot.mem Extensions.E_extended_ms sexts)

// used only for TLS 1.2. FIXME: properly negotiate
val chosenGroup: mode -> option CommonDH.group
let chosenGroup mode =
  match kexAlg mode with
  | Kex_PSK_DHE
  | Kex_DHE -> CommonDH.group_of_namedGroup CommonDH.FFDHE2048
  | Kex_PSK_ECDHE
  | Kex_ECDHE -> CommonDH.group_of_namedGroup CommonDH.SECP256R1

val zeroRTToffer: offer -> bool
let zeroRTToffer o = Some? (find_early_data o)

val zeroRTT: mode -> bool
let zeroRTT mode =
  zeroRTToffer mode.n_offer &&
  Some? mode.n_pski &&
  Some? mode.n_server_extensions &&
  List.Tot.existsb E_early_data? (Some?.v mode.n_server_extensions)

val sendticket_12: mode -> bool
let sendticket_12 mode =
  Some? mode.n_server_extensions &&
  List.Tot.existsb E_session_ticket? (Some?.v mode.n_server_extensions)

val resume_12: mode -> bool
let resume_12 mode =
  not (is_pv_13 mode.n_protocol_version) &&
  Some? (find_sessionTicket mode.n_offer) &&
  length mode.n_offer.ch_sessionID > 0 &&
  mode.n_sessionID = mode.n_offer.ch_sessionID

val local_config: #region:rgn -> #role:TLSConstants.role -> t region role -> config
let local_config #region #role ns =
  ns.cfg

val nonce: #region:rgn -> #role:TLSConstants.role -> t region role -> Tot TLSInfo.random
let nonce #region #role ns =
  ns.nonce

val resume: #region:rgn -> #role:TLSConstants.role -> t region role -> TLSInfo.resumeInfo role
let resume #region #role ns =
  ns.resume

val getMode: #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST mode
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let getMode #region #role ns =
  match HST.op_Bang ns.state with
  | C_Mode mode
  | C_WaitFinished2 mode _
  | C_Complete mode _
  | S_ClientHello mode _
  | S_Mode mode _
  | S_Complete mode _ ->
  mode

(** Returns cfg.max_versionsion or the negotiated version, when known *)
val version: #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST protocolVersion
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let version #region #role ns =
  match HST.op_Bang ns.state with
  | C_Init _ -> ns.cfg.max_version
  | C_Offer _ -> ns.cfg.max_version
  | C_HRR o _ -> ns.cfg.max_version
  | C_WaitFinished1 _ -> ns.cfg.max_version
  | C_Mode mode
  | C_WaitFinished2 mode _
  | C_Complete mode _ -> mode.n_protocol_version
  | S_Init _ -> ns.cfg.max_version
  | S_HRR o _ -> ns.cfg.max_version
  | S_ClientHello mode _
  | S_Mode mode _
  | S_Complete mode _ -> mode.n_protocol_version

(** Returns cfg.max_versionsion or the negotiated version, when known *)
val is_hrr: #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST bool
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let is_hrr #region #role ns =
  C_HRR? (!ns.state)

(*
val getSigningKey: #a:Signature.alg -> #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST (option (Signature.skey a))
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let getSigningKey #a #region #role ns =
  Signature.lookup_key #a ns.cfg.private_key_file
*)

val sign: #region:rgn -> #role:TLSConstants.role -> t region role -> bytes ->
  ST (result HandshakeMessages.signature)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
private
let const_true _ = true

let sign #region #role ns tbs =
  // TODO(adl) make the pattern below a static pre-condition
  let S_Mode mode (Some (cert, sa)) = HST.op_Bang ns.state in
  match cert_sign_cb ns.cfg cert sa tbs with
  | None -> Error (AD_no_certificate, perror __SOURCE_FILE__ __LINE__ "Failed to sign with selected certificate.")
  | Some sigv ->
    let alg = if mode.n_protocol_version `geqPV` TLS_1p2 then Some sa else None in
    Correct ({sig_algorithm = alg; sig_signature = sigv})

(* CLIENT *)

effect ST0 (a:Type) = ST a (fun _ -> True) (fun h0 _ h1 -> modifies_none h0 h1)
val map_ST: ('a -> ST0 'b) -> list 'a -> ST0 (list 'b)
let rec map_ST f x = match x with
  | [] -> []
  | a::tl -> f a :: map_ST f tl

let i_psk_info i = (i, PSK.psk_info i)

val client_ClientHello: #region:rgn -> t region Client
  -> option CommonDH.clientKeyShare
  -> St offer
let client_ClientHello #region ns oks =
  //17-04-22 fix this in the definition of offer?
  let oks' =
    match oks with
    | Some ks -> Some (CommonDH.ClientKeyShare ks)
    | None -> None in
  let _, pskid = ns.resume in
  let pskinfo = map_ST i_psk_info pskid in
  match HST.op_Bang ns.state with
  | C_Init _ ->
      trace(if
        (match pskinfo with
        | (_, i) :: _ -> i.allow_early_data && Some? ns.cfg.max_early_data // Must be the first PSK
        | _ -> false)
      then "Offering a PSK compatible with 0-RTT" else "No PSK or 0-RTT disabled");
      let now = CoreCrypto.now () in
      let offer = computeOffer Client ns.cfg ns.resume ns.nonce oks' pskinfo now in
      trace ("offering client extensions "^string_of_option_extensions offer.ch_extensions);
      trace ("offering cipher suites "^string_of_ciphersuites offer.ch_cipher_suites);
      HST.op_Colon_Equals ns.state (C_Offer offer);
      offer

let group_of_hrr hrr : option CommonDH.group =
  match List.Tot.find (Extensions.E_key_share?) hrr.hrr_extensions with
  | Some (Extensions.E_key_share (CommonDH.HRRKeyShare ng)) ->
    CommonDH.group_of_namedGroup ng
  | _ -> None

private
let choose_extension (s:option share)
                     (e:Extensions.extension) =
      match e with
      | Extensions.E_key_share (CommonDH.ClientKeyShare sl) ->
        (match s with
         | Some (| g, gx |) ->
           Some (Extensions.E_key_share (CommonDH.ClientKeyShare [CommonDH.Share g gx]))
         | _ -> Some e)
      | Extensions.E_early_data _ ->
        None
      | e -> Some e

let client_HelloRetryRequest #region (ns:t region Client) hrr (s:option share) =
  let { hrr_sessionID = sid;
        hrr_cipher_suite = cs;
        hrr_extensions = el } = hrr in
  trace ("Got HRR, extensions: ["^(Extensions.string_of_extensions el)^"]");
  match ! ns.state with
  | C_Offer offer ->
    let old_shares = gs_of offer in
    let old_psk =
      match find_pske offer with
      | None -> []
      | Some pskl -> pskl in
    // TODO early data not recorded in retryInfo
    let ext' = List.Helpers.choose_aux s choose_extension (Some?.v offer.ch_extensions) in

    // Echo the cookie for QUIC stateless retry
    let ext', no_cookie = match List.Tot.find Extensions.E_cookie? el with
      | Some cookie -> cookie :: ext', false
      | None -> ext', true in

    if sid <> offer.ch_sessionID then
      Error(AD_illegal_parameter, "mismatched session ID in HelloRetryRequest")
    // 2018.03.08 SZ: TODO We must Update PSK extension if present
    // See https://tools.ietf.org/html/draft-ietf-tls-tls13-26#section-4.1.2
    else if None? (group_of_hrr hrr) && no_cookie then
      Error(AD_illegal_parameter, "received a HRR that would yield the same ClientHello")
    else
     begin
      let offer' = {offer with ch_extensions = Some ext'} in
      let ri = (hrr, old_shares, old_psk) in
      ns.state := (C_HRR offer' ri);
      Correct(offer')
     end

(**
  Checks that the protocol version in ClientHello is
  within the range of versions supported by the server configuration
  and outputs the negotiated version if true
*)

// usable on both sides; following https://tlswg.github.io/tls13-spec/#rfc.section.4.2.1
let offered_versions min_pv (o: offer): result (l: list protocolVersion {l <> []}) =
  match find_supported_versions o with
  | Some (ServerPV _)
  | Some (Extensions.ClientPV []) ->
    Error(AD_protocol_version, "protocol version negotiation: empty proposal")
  | Some (ClientPV vs) -> Correct vs  // might check no proposal is below min_pv
  | None -> // use legacy offer
      match o.ch_protocol_version, min_pv with
      | TLS_1p0, TLS_1p0 -> Correct [TLS_1p0]
      | TLS_1p1, TLS_1p0 -> Correct [TLS_1p2; TLS_1p1]
      | TLS_1p1, TLS_1p1 -> Correct [TLS_1p1]
      | TLS_1p2, TLS_1p0 -> Correct [TLS_1p2; TLS_1p1; TLS_1p0]
      | TLS_1p2, TLS_1p1 -> Correct [TLS_1p2; TLS_1p1]
      | TLS_1p2, TLS_1p2 -> Correct [TLS_1p2]
      | _, _ -> Error(AD_protocol_version, "protocol version negotation: bad legacy proposal")

let is_client13 (o:offer) =
  match offered_versions TLS_1p3 o with
  | Correct vs -> List.Tot.existsb is_pv_13 vs
  | Error _ -> false

private let version_within cfg v = geqPV cfg.max_version v && geqPV v cfg.min_version

let negotiate_version cfg offer =
  //17-04-26 TODO pass outer packet PV instead of TLS_1p0
  match offered_versions TLS_1p0 offer with
  | Error z -> Error z
  | Correct vs ->
    match List.Helpers.find_aux cfg version_within vs with
    | Some v -> Correct v
    | None -> Error(AD_protocol_version, "protocol version negotiation: mismatch")

(**
  For use in negotiating the ciphersuite, takes two lists and
  outputs the first ciphersuite in list2 that also is in list
  one and is a valid ciphersuite, or [None]
*)
private
let is_cs_in_l (l1, sa) s = CipherSuite? s && List.Tot.mem s l1 && CipherSuite?._1 s = Some sa
val negotiate: l1:list valid_cipher_suite -> list valid_cipher_suite -> sigAlg
 -> Tot (option (c:valid_cipher_suite{CipherSuite? c && List.Tot.mem c l1}))
let negotiate l1 l2 sa =
  List.Helpers.find_aux (l1, sa) is_cs_in_l l2

(**
  For use in ensuring the result from negotiate is a Correct
  ciphersuite with associated kex, sig and ae algorithms,
  and throws an error if No ciphersuites were supported in both lists
*)
val negotiateCipherSuite: cfg:config -> pv:protocolVersion -> ccs:valid_cipher_suites -> sa:sigAlg -> Tot (result (TLSConstants.kexAlg * option TLSConstants.sigAlg * TLSConstants.aeAlg * valid_cipher_suite))
let negotiateCipherSuite cfg pv ccs sa =
  match negotiate ccs cfg.cipher_suites sa with
  | Some(CipherSuite kex sa ae) -> Correct(kex,sa,ae,CipherSuite kex sa ae)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Cipher suite negotiation failed")

(*
val negotiateGroupKeyShare13
  config ->
  list extension ->
  Tot (result (option (kexAlg * namedGroup * option share))
let rec negotiateGroupKeyShare cfg pv exts =
  // first fetch the two relevant extensions
  let supported, keyshares =
    match o.ch_extensions with
    | None -> None, None
    | Some es ->
      ( match List.Tot.find Extensions.E_supported_groups? es with
        | None -> None
        | Some (Extensions.E_supported_groups gs) -> Some gs)
      ( match List.Tot.find Extensions.E_key_share? es with
        | None -> None
        | Some (Extensions.E_key_share (CommonDH.ClientKeyShare gl)) ->
            let filter (g, gx) =
              List.Tot.mem g cfg.named_groups &&
              ( (SEC? g && (kex = Kex_ECDHE || kex = Kex_PSK_ECDHE)) ||
                (FFDHE? g && (kex = Kex_DHE || kex = Kex_PSK_DHE)) ) in
            Some(match List.Tot.filter filter gl)) in

  if pv = TLS_1p3 then
    match keyshares with
    | None -> Error(AD_decode_error, "no supported group or key share extension found")
    | Some [] -> Error(AD_decode_error, "no shared group between client and server config")
    | Some (share::_) -> Correct (Some share)
    // todo support HRR depending on supported_groups

  else if kex = Kex_ECDHE && Some? supported then
    let filter g = SEC? g && List.Tot.mem g cfg.named_groups in
    let gs = List.Tot.filter

    Correct(Some (match List.Tot.filter filter gs), None)

    match supported with

    | Some
  List.Tot.existsb E_supported_groups? exts


  | Some exts when (kex = Kex_ECDHE && List.Tot.existsb E_supported_groups? exts) ->
    let Some (E_supported_groups gl) = List.Tot.find E_supported_groups? exts in

    let filter g =
    (match List.Tot.filter filter gl with
    | gn :: _ -> Correct (Some gn, None)
    | [] -> Error(AD_decode_error, "no shared curve configured"))
  | _ ->
    let filter x =
      (match kex with | Kex_DHE -> FFDHE? x | Kex_ECDHE -> SEC? x | _ -> false) in
    if kex = Kex_DHE || kex = Kex_ECDHE then
      (match List.Tot.filter filter cfg.named_groups with
      | gn :: _ -> Correct (Some gn, None)
      | [] -> Error(AD_decode_error, "no valid group is configured for the selected cipher suite"))
    else Correct(None, None)
*)

(**
  Determines if the server random value contains a downgrade flag
  AND if there has been a downgrade
  The downgrade flag is a random value set by RFC (6.3.1.1)
*)
val isSentinelRandomValue: protocolVersion -> protocolVersion -> TLSInfo.random -> Tot bool
let isSentinelRandomValue c_pv s_pv s_random =
  let down = bytes_of_string "DOWNGRD" in
  geqPV c_pv TLS_1p3 && geqPV TLS_1p2 s_pv && (down @| abyte 1z) = s_random ||
  geqPV c_pv TLS_1p2 && geqPV TLS_1p1 s_pv && (down @| abyte 0z) = s_random


(** Confirms that the version negotiated by the server was:
  - within the range specified by client config AND
  - is not an unnecessary downgrade AND
  - is not a newer version than offered by the client
*)
val acceptableVersion: config -> protocolVersion -> TLSInfo.random -> Tot bool
let acceptableVersion cfg pv sr =
  // we statically know that the offered versions are compatible with our config
  // (we may prove e.g. acceptableVersion pv ==> pv in offered_versions
  geqPV pv cfg.min_version &&
  geqPV cfg.max_version pv &&
  not (isSentinelRandomValue cfg.max_version pv sr)

(** Confirms that the ciphersuite negotiated by the server was:
  - consistent with the client config;
  - TODO: [s_cs] is supported by the protocol version (e.g. no GCM with
    TLS<1.2).
 BD: Removed that the ciphersuite is acceptable given CHELO
 given that the clientOffer is prepared with the entire list
 of valid cipher suites in the client config
*)
val acceptableCipherSuite: config -> protocolVersion -> valid_cipher_suite -> Tot bool
let is_cs (cs:valid_cipher_suite) x = x = cs
let acceptableCipherSuite cfg spv cs =
  List.Helpers.exists_b_aux cs is_cs cfg.cipher_suites

let is_share_eq (g:CommonDH.group) share = CommonDH.Share?.g share = g

let matching_share
  (cext:option (ce:list extension{List.Tot.length ce < 256})) (g:CommonDH.group) :
   option (g:CommonDH.group & CommonDH.share g) =
  match cext with
  | Some cext ->
    begin
    match List.Tot.find Extensions.E_key_share? cext with
    | Some (E_key_share (CommonDH.ClientKeyShare shares)) ->
      begin
      match List.Helpers.find_aux g is_share_eq shares with
      | Some (CommonDH.Share g gx) -> Some (|g, gx|)
      | _ -> None
      end
    | _ -> None
    end
  | None -> None

// for this kind of function, can we just rely on type inference?
val client_ServerHello: #region:rgn -> t region Client ->
  HandshakeMessages.sh ->
  St (result mode) // it needs to be computed, whether returned or not
let client_ServerHello #region ns sh =
  match HST.op_Bang ns.state with
  | C_HRR offer _ // -> FIXME validation
  //  .....
  | C_Offer offer ->
    let spv  = sh.sh_protocol_version in
    let sr   = sh.sh_server_random in
    let cs   = sh.sh_cipher_suite in
    let sext = sh.sh_extensions in
    let ssid = sh.sh_sessionID in
    let cext = offer.ch_extensions in
    let sig  = CoreCrypto.RSASIG in
    let resume = ssid = offer.ch_sessionID && length offer.ch_sessionID > 0 in
    trace ("processing server extensions "^string_of_option_extensions sext);
    (match Extensions.negotiateClientExtensions spv ns.cfg cext sext cs None resume with
    | Error z -> Error z
    | Correct spv ->
      if not (acceptableVersion ns.cfg spv sr) then
        Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
      else if not (acceptableCipherSuite ns.cfg spv cs) then
        Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
      else (
        trace ("negotiated "^string_of_pv spv^" "^string_of_ciphersuite cs);
        match cs with
        | CipherSuite13 ae ha ->
          begin
          let pski =
            match find_clientPske offer, find_serverPske sh with
            | Some (ids,_), Some idx ->
              if idx < List.Tot.length ids then
                Correct (Some idx) // REMARK: we can't check yet consistency with early_data in EE
              else
                Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "PSK out of bounds")
            | None, Some _ ->
              Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "PSK not offered")
            | _, _ -> Correct None
          in
          match pski with
          | Error z -> Error z
          | Correct pski ->
            begin
            match spv, find_serverKeyShare sh with
            | TLS_1p3, Some (CommonDH.Share g gy) ->
              let server_share = (|g, gy|) in
              let client_share = matching_share cext g in
              let mode = Mode
                offer
                None // n_hrr
                spv
                sr
                ssid
                cs
                pski
                sext
                (Some server_share)
                None // n_client_cert_request
                None // n_server_cert
                client_share
               in
               HST.op_Colon_Equals ns.state (C_Mode mode);
               Correct mode
            | TLS_1p3, None ->
              // Pure PSK
              let mode = Mode offer None spv sr ssid cs pski sext None None None None in
              HST.op_Colon_Equals ns.state (C_Mode mode);
              Correct mode
            | _ ->
              Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Impossible: TLS 1.3 PSK")
            end
          end
        | CipherSuite kex sa ae ->
          let mode = Mode
            offer
            None
            spv
            sr
            ssid
            cs
            None // pski
            sext
            None // n_server_share; unknwon before SKE is received
            None // n_client_cert_request
            None // n_server_cert
            None // n_client_share
          in
          HST.op_Colon_Equals ns.state (C_Mode mode);
          Correct mode
        | _ -> Error (AD_decode_error, "ServerHello ciphersuite is not a real ciphersuite")))

(* ---------------- signature stuff, to be removed from Handshake -------------------- *)

// why an option?
val to_be_signed: pv:protocolVersion -> role -> csr:option bytes{None? csr <==> pv == TLS_1p3} -> bytes -> bytes
let to_be_signed pv role csr tbs =
  match pv, csr with
  | TLS_1p3, None ->
      let pad = Bytes.create_ 64 32uy in
      let ctx =
        match role with
        | Server -> "TLS 1.3, server CertificateVerify"
        | Client -> "TLS 1.3, client CertificateVerify"  in
      pad @| bytes_of_string ctx @| abyte 0z @| tbs
  | TLS_1p2, Some csr -> csr @| tbs
  | _, Some csr -> csr @| tbs

private let matches_sigHashAlg_of_signatureScheme sa alg =
      let (sa',_) = sigHashAlg_of_signatureScheme alg in
      sa' = sa

// Used for clients to verify the server's signature scheme
let supported_signatureSchemes_12 mode =
  let ha0 = sessionHashAlg mode.n_protocol_version mode.n_cipher_suite in
  let sa = sigAlg_of_ciphersuite mode.n_cipher_suite in
  match mode.n_protocol_version with
  | TLS_1p0 | TLS_1p1 | SSL_3p0 -> [signatureScheme_of_sigHashAlg sa ha0]
  | TLS_1p2 ->
    match find_signature_algorithms mode.n_offer with
    | None -> [signatureScheme_of_sigHashAlg sa ha0]
    | Some algs -> List.Helpers.filter_aux sa matches_sigHashAlg_of_signatureScheme algs

// TLS 1.2 only
val client_ServerKeyExchange: #region:rgn -> t region Client ->
  serverCert:HandshakeMessages.crt ->
  HandshakeMessages.ske ->
  ocr:option HandshakeMessages.cr ->
  St (result mode)
let client_ServerKeyExchange #region ns crt ske ocr =
  let mode = getMode ns in
  match ske.ske_kex_s with
  | KEX_S_RSA _ ->
    Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Illegal message")
  | KEX_S_DHE gy ->
    let ske_tbs = kex_s_to_bytes ske.ske_kex_s in
    let salgs = supported_signatureSchemes_12 mode in
    let salgs =
      match ske.ske_signed_params.sig_algorithm with
      | None -> salgs
      | Some sa' -> List.Helpers.filter_aux sa' op_Equality salgs in
    match salgs with
    | [] ->
      Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Signature algorithm negotiation failed")
    | sa::_ ->
      let csr = ns.nonce @| mode.n_server_random in
      let tbs = to_be_signed mode.n_protocol_version Server (Some csr) ske_tbs in
      let valid = cert_verify_cb ns.cfg crt.crt_chain sa tbs ske.ske_signed_params.sig_signature in
      trace ("ServerKeyExchange signature: " ^ (if valid then "Valid" else "Invalid"));
      if not valid then
        Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Failed to check SKE signature")
      else
        let Mode offer hrr pv sr sid cs pski sext _ _ _ gx = mode in
        let scert = Some (Cert.chain_up crt.crt_chain, sa) in
        let mode = Mode offer hrr pv sr sid cs pski sext (Some gy) ocr scert gx in
        let ccert = None in // TODO
        HST.op_Colon_Equals ns.state (C_WaitFinished2 mode ccert);
        Correct mode

val clientComplete_13: #region:rgn -> t region Client ->
  HandshakeMessages.ee ->
  optCertRequest: option HandshakeMessages.cr13 ->
  optServerCert: option Cert.chain13 -> // Not sent with PSK
  optCertVerify: option HandshakeMessages.cv -> // Not sent with PSK
  digest: option (b:bytes{length b <= 32}) ->
  St (result mode) // it needs to be computed, whether returned or not
let clientComplete_13 #region ns ee optCertRequest optServerCert optCertVerify digest =
  trace "Nego.clientComplete_13";
  match HST.op_Bang ns.state with
  | C_Mode mode ->
    let ccert = None in
    trace ("EE: "^(Extensions.string_of_extensions ee));
    let sexts =
      match mode.n_server_extensions, ee with
      | Some el, ee -> Some (List.Tot.append el ee)
      | None, [] -> None
      | None, ee -> Some ee
      in
    let nego_cb = ns.cfg.nego_callback in
    let exts = Extensions.app_ext_filter sexts in
    let exts_bytes = HandshakeMessages.optionExtensionsBytes exts in
    trace ("Negotiation callback to process application extensions.");
    match nego_cb.negotiate nego_cb.nego_context mode.n_protocol_version exts_bytes None with
    | Nego_abort -> Error(AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "application requested to abort the handshake")
    | Nego_retry _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "client application requested a server retry")
    | Nego_accept _ ->
      let validSig, schain =
        match kexAlg mode, optServerCert, optCertVerify, digest with
        | Kex_DHE, Some c, Some cv, Some digest
        | Kex_ECDHE, Some c, Some cv, Some digest ->
          // TODO ensure that valid_offer mandates signature extensions for 1.3
          let Some sal = find_signature_algorithms mode.n_offer in
          let sa = Some?.v cv.sig_algorithm in
          let chain = Some (c, sa) in
          if List.Tot.mem sa sal then
            let tbs = to_be_signed mode.n_protocol_version Server None digest in
            cert_verify_cb ns.cfg (Cert.chain_down c) sa tbs cv.sig_signature, chain
          else false, None // The server signed with an algorithm we did not offer
        | Kex_PSK_ECDHE, None, None, None
        | Kex_PSK, None, None, None -> true, None // FIXME recall chain from PSK
        | _ -> false, None
        in
      trace ("Certificate & signature 1.3 callback result: " ^ (if validSig then "valid" else "invalid"));
      if validSig then
        let mode = Mode
          mode.n_offer
          mode.n_hrr
          mode.n_protocol_version
          mode.n_server_random
          mode.n_sessionID
          mode.n_cipher_suite
          mode.n_pski
          sexts
          mode.n_server_share
          optCertRequest
          schain
          mode.n_client_share
        in
        HST.op_Colon_Equals ns.state (C_Complete mode ccert);
        Correct mode
      else
        Error(AD_bad_certificate_fatal, "Failed to validate signature or certificate")

(* SERVER *)

type cs13 offer =
  | PSK_EDH: j:pski offer -> oks: option share -> cs: cipherSuite -> cs13 offer
  | JUST_EDH: oks: share -> cs: cipherSuite -> cs13 offer

private
let rec just_edh_x (o:offer) (oks:share) (l:list cipherSuite) : list (cs13 o) =
  match l with
  | [] -> []
  | hd::tl -> JUST_EDH oks hd :: just_edh_x o oks tl

// Work around #1016
private let rec compute_cs13_aux (i:nat) (o:offer)
  (psks:list (PSK.pskid * PSK.pskInfo))
  (g_gx:option share) ncs psk_kex server_cert : list (cs13 o) =
  if i = List.length psks then
    match g_gx, server_cert with
    | Some x, true -> just_edh_x o x ncs
    | _ -> []
  else
    let choices =
      match List.Tot.index psks i with
      | (id, info) ->
        let cs = CipherSuite13 info.early_ae info.early_hash in
        if List.Tot.mem cs ncs then
          let r =
            if List.Tot.mem Extensions.PSK_KE psk_kex then
              [PSK_EDH i None cs]
            else [] in
          let r =
            if List.Tot.mem Extensions.PSK_DHE_KE psk_kex then
              (PSK_EDH i g_gx cs) :: r
            else r in
          r
        else []
      | _ -> []
    in
    choices @ (compute_cs13_aux (i+1) o psks g_gx ncs psk_kex server_cert)

private
let is_cs13_in_cfg cfg cs =
  CipherSuite13? cs && List.Tot.mem cs cfg.cipher_suites

private
let is_in_cfg_named_groups cfg g =
  List.Tot.mem g cfg.named_groups

private
let group_of_named_group (x:_{Some? (CommonDH.group_of_namedGroup x)}) =
  Some?.v (CommonDH.group_of_namedGroup x)

private
let share_in_named_group gl (x :share) =
    let (| g, _ |) = x in
    List.Tot.mem g gl

// returns a list of negotiable "core modes" for TLS 1.3
// and an optional group and ciphersuite suitable for HRR
// the key exchange can be derived from cs13
// (we could stop after finding the first)
val compute_cs13:
  cfg: config ->
  o: offer ->
  psks: list (PSK.pskid * PSK.pskInfo) ->
  shares: list share (* pre-registered *) ->
  server_cert: bool (* is a certificate available for signing? *) ->
  result (list (cs13 o) * option (CommonDH.namedGroup * cs:cipherSuite))
let compute_cs13 cfg o psks shares server_cert =
  // pick acceptable record ciphersuites
  let ncs =  List.Helpers.filter_aux cfg is_cs13_in_cfg o.ch_cipher_suites in
  // pick the (potential) group to use for DHE/ECDHE
  // also remember if there is a supported group with no share provided
  // in case we want to to a HRR
  let g_gx, g_hrr =
    match find_supported_groups o with
    | None -> None, None // No offered group, only PSK
    | Some gs ->
      match List.Helpers.filter_aux cfg is_in_cfg_named_groups gs with
      | [] -> None, None // No common group, only PSK
      | gl ->
        let csg = match ncs with | [] -> None | cs :: _ -> Some (List.Tot.hd gl, cs) in
        let gl' = List.Tot.map group_of_named_group gl in
        let s = List.Helpers.find_aux gl' share_in_named_group shares in
        s, (if server_cert then csg else None) // Can't do HRR without a certificate
    in
  let psk_kex = find_psk_key_exchange_modes o in
  Correct (compute_cs13_aux 0 o psks g_gx ncs psk_kex server_cert, g_hrr)

let rec iutf8 (m:bytes) : St (s:string{String.length s < pow2 30 /\ utf8_encode s = m}) =
    match iutf8_opt m with
    | None -> trace ("Not a utf8 encoding of a string"); iutf8 m
    | Some s -> s

// Registration and filtering of PSK identities
let rec filter_psk (l:list Extensions.pskIdentity)
  : St (list (PSK.pskid * PSK.pskInfo))
  =
  match l with
  | [] -> []
  | (id, _) :: t ->
    //18-02-26 ?? review
    let id8 = iutf8 id in
    let id = utf8_encode id8 in // FIXME FStar.Bytes
    match Ticket.check_ticket13 id with
    | Some info -> (id, info) :: (filter_psk t)
    | None ->
      (match PSK.psk_lookup id with
      | Some info -> trace ("Loaded PSK from ticket <"^print_bytes id^">"); (id, info) :: (filter_psk t)
      | None -> trace ("WARNING: the PSK <"^print_bytes id^"> has been filtered"); filter_psk t)

// Registration of DH shares
let rec register_shares (l:list pre_share)
  : St (list share) =
  match l with
  | [] -> []
  | (| g, gx |) :: t -> (| g, CommonDH.register_dhi #g gx |) :: (register_shares t)

// For application-handled extensions set by nego callback,
// such as QUIC transport parameters
type extra_ext = // list (e:Extensions.extension{E_unknown_extension? e})
  list Extensions.extension

//17-03-30 still missing a few for servers.
type serverMode =
  | ServerHelloRetryRequest: hrr -> serverMode
  | ServerMode: mode -> certNego -> extra_ext -> serverMode

let get_sni (o:offer) : bytes =
  match find_client_extension Extensions.E_server_name? o with
  | Some (Extensions.E_server_name ((SNI_DNS sni)::_)) -> sni
  | _ -> empty_bytes

let nego_alpn (o:offer) (cfg:config) : bytes =
  match cfg.alpn with
  | None -> empty_bytes
  | Some sal ->
    match find_client_extension Extensions.E_alpn? o with
    | None -> empty_bytes
    | Some (Extensions.E_alpn cal) ->
      match TLSConstants.filter_aux sal List.Helpers.mem_rev cal with
      | a :: _ -> a
      | _ -> empty_bytes

irreducible val computeServerMode:
  cfg: config ->
  co: offer ->
  serverRandom: TLSInfo.random ->
  St (result serverMode)
let computeServerMode cfg co serverRandom =
  match negotiate_version cfg co with
  | Error z -> Error z
  | Correct TLS_1p3 ->
    begin
    let pske = // Filter and register offered PSKs
      match find_clientPske co with
      | Some (pske,_) -> filter_psk pske
      | None -> [] in
    let shares = register_shares (gs_of co) in
    let scert =
      match find_signature_algorithms co with
      | None -> None
      | Some sigalgs ->
        let sigalgs =
          List.Helpers.filter_aux cfg.signature_algorithms List.Helpers.mem_rev sigalgs
        in
        if sigalgs = [] then None
        // FIXME(adl) workaround for a bug in TLSConstants that causes signature schemes list to be parsed in reverse order
        else cert_select_cb cfg TLS_1p3 (get_sni co) (nego_alpn co cfg) (List.Tot.rev sigalgs)
      in
    match compute_cs13 cfg co pske shares (Some? scert) with
    | Error z -> Error z
    | Correct ([], None) -> Error(AD_handshake_failure, "ciphersuite negotiation failed")
    | Correct ([], Some (ng, cs)) ->
      let hrr = {
        hrr_sessionID = co.ch_sessionID;
        hrr_cipher_suite = cs;
        hrr_extensions = [
          Extensions.E_supported_versions (Extensions.ServerPV TLS_1p3);
          Extensions.E_key_share (CommonDH.HRRKeyShare ng);
        ]; } in
      Correct(ServerHelloRetryRequest hrr)
    | Correct ((PSK_EDH j ogx cs)::_, _) ->
      (trace "Negotiated PSK_EDH key exchange";
      Correct (ServerMode (Mode
        co
        None
        TLS_1p3
        serverRandom
        co.ch_sessionID
        cs
        (Some j)
        None // Extensions will be filled in next pass
        None // no server key share yet
        None // TODO: n_client_cert_request
        None
        ogx)
      None [])) // No cert
    | Correct ((JUST_EDH gx cs) :: _, _) ->
      (trace "Negotiated Pure EDH key exchange";
      let Some (cert, sa) = scert in
      let schain = cert_format_cb cfg cert in
      trace ("Negotiated " ^ (string_of_signatureScheme sa));
      Correct
        (ServerMode
          (Mode
          co
          None
          TLS_1p3
          serverRandom
          co.ch_sessionID
          cs
          None // No PSKs, pure (EC)DHE
          None // Extensions will be filled in next pass
          None // no server key share yet
          None // TODO: n_client_cert_request
          (Some (Cert.chain_up schain, sa))
          (Some gx))
        scert []))
    end
  | Correct pv ->
    let valid_ticket =
      match find_sessionTicket co with
      | None -> None
      | Some t ->
        // No tickets if client desn't send an SID (too messy)
        if length co.ch_sessionID = 0 then None
        else Ticket.check_ticket12 t
      in
    (match valid_ticket with
    | Some (pv, cs, ems, _, _) ->
      Correct (ServerMode (Mode
        co
        None // TODO: no HRR
        pv
        serverRandom
        co.ch_sessionID
        cs
        None
        None // Extensions
        None
        None
        None
        None) None [])
    | _ ->
      // Make sure NullCompression is offered
      if not (List.Tot.mem NullCompression co.ch_compressions)
      then Error(AD_illegal_parameter, "Compression is deprecated") else
      let salgs =
        match find_signature_algorithms co with
        | None -> [SIG_UNKNOWN (twobytes (0xFFz, 0xFFz)); ECDSA_SHA1]
        | Some sigalgs -> List.Helpers.filter_aux cfg.signature_algorithms List.Helpers.mem_rev sigalgs
        in
      match cert_select_cb cfg pv (get_sni co) (nego_alpn co cfg) salgs with
      | None -> Error(AD_no_certificate, perror __SOURCE_FILE__ __LINE__ "No compatible certificate can be selected")
      | Some (cert, sa) ->
        let schain = cert_format_cb cfg cert in
        let sig, _ = sigHashAlg_of_signatureScheme sa in
        match negotiateCipherSuite cfg pv co.ch_cipher_suites sig with
        | Error z -> Error z
        | Correct (kex, _, ae, cs) ->
          Correct (
            ServerMode
              (Mode
                co
                None // no HRR before TLS 1.3
                pv
                serverRandom
                (CoreCrypto.random 32)
                cs
                None
                None // Extensions will be filled later
                None // no server key share yet
                None
                (Some (Cert.chain_up schain, sa))
                None) // no client key share yet for 1.2
              (Some(cert, sa)) []
            ))

private
let accum_string_of_pv s pv = s ^ " " ^ string_of_pv pv

private
let aux_extension_ok (o1, hrr) (e:Extensions.extension) =
    match e with
    | Extensions.E_key_share (CommonDH.ClientKeyShare ecl) ->
          (match ecl, group_of_hrr hrr with
          | [CommonDH.Share g _], Some g' -> g = g'
          | _, None ->
            let shares1 = find_key_shares o1 in
            Some? shares1 &&
            CommonDH.clientKeyShareBytes (Some?.v shares1) = CommonDH.clientKeyShareBytes ecl
          | _ -> false)
    | Extensions.E_early_data _ -> false // Forbidden
    | Extensions.E_cookie c -> true // FIXME we will send cookie
        // If we add cookie support we need to treat this case separately
        // | Extensions.E_cookie c -> c = S_HRR?.cookie ns.state
    | e ->
          (match find_client_extension_aux e Extensions.sameExt o1 with
          | None -> (IO.debug_print_string "Extra extension\n") && false
          // This allows the client to send less extensions,
          // but the ones that are sent must be exactly the same
          | Some e' ->
            //FIXME: Extensions.E_pre_shared_key "may be updated" 4.1.2
            true) // FIXME
            //(extensionBytes e) = (extensionBytes e'))

let rec forall_aux (#a:Type) (#b:Type) (env:b) (f: b -> a -> Tot bool) (l:list a)
  : Tot bool
  = match l with
    | [] -> true
    | hd::tl -> if f env hd then forall_aux env f tl else false

val server_ClientHello: #region:rgn -> t region Server ->
  HandshakeMessages.ch -> log:HandshakeLog.t ->
  St (result serverMode)
let server_ClientHello #region ns offer log =
  trace ("offered client extensions "^string_of_option_extensions offer.ch_extensions);
  trace ("offered cipher suites "^(string_of_ciphersuites offer.ch_cipher_suites));
  trace (match (offered_versions TLS_1p0 offer) with
        | Error z -> "Error: "^string_of_error z
        | Correct v -> List.Tot.fold_left accum_string_of_pv "offered versions" v);
  match HST.op_Bang ns.state with
  | S_HRR o1 hrr ->
    trace ("Processing second offer based on existing HRR state (staeful HRR).");
    let o2 = offer in
    if
      o1.ch_protocol_version = o2.ch_protocol_version &&
      o1.ch_client_random = o2.ch_client_random &&
      o1.ch_sessionID = o2.ch_sessionID &&
      o1.ch_sessionID = hrr.hrr_sessionID &&
      List.Tot.mem hrr.hrr_cipher_suite o2.ch_cipher_suites &&
      o1.ch_compressions = o2.ch_compressions &&
      Some? o2.ch_extensions && Some? o1.ch_extensions &&
      forall_aux (o1, hrr) aux_extension_ok (Some?.v o2.ch_extensions)
    then
      let sm = computeServerMode ns.cfg offer ns.nonce in
      match sm with
      | Error z ->
        trace ("negotiation failed: "^string_of_error z);
        Error z
      | Correct (ServerHelloRetryRequest hrr) ->
        Error(AD_illegal_parameter, "client sent the same hello in response to hello retry")
      | Correct (ServerMode m cert _) ->
        trace ("negotiated after HRR "^string_of_pv m.n_protocol_version^" "^string_of_ciphersuite m.n_cipher_suite);
        let nego_cb = ns.cfg.nego_callback in
        let exts = Extensions.app_ext_filter offer.ch_extensions in
        let exts_bytes = HandshakeMessages.optionExtensionsBytes exts in
        trace ("Negotiation callback to handle extra extensions.");
        match nego_cb.negotiate nego_cb.nego_context m.n_protocol_version exts_bytes (Some empty_bytes) with
        | Nego_accept sexts ->
          let el = Extensions.ext_of_custom sexts in
          HST.op_Colon_Equals ns.state (S_ClientHello m cert);
          Correct (ServerMode m cert el)
        | _ ->
          trace ("Application requested to abort the handshake after internal HRR.");
          Error (AD_handshake_failure, "application aborted the handshake by callback")
    else
      Error(AD_illegal_parameter, "Inconsistant parameters between first and second client hello")
  | S_Init _ ->
    let sm = computeServerMode ns.cfg offer ns.nonce in
    let previous_cookie = // for stateless HRR
      match find_cookie offer with
      | None -> None
      | Some c ->
        match Ticket.check_cookie c with
        | None -> trace ("WARNING: ignorning invalid cookie "^(hex_of_bytes c)); None
        | Some (hrr, digest, extra) ->
          trace ("Loaded stateless retry cookie "^(hex_of_bytes c));
          let hrr = { hrr with hrr_extensions =
            (Extensions.E_cookie c) :: hrr.hrr_extensions; } in
          // Overwrite the current transcript digest with values from cookie
          trace ("Overwriting the transcript digest with CH1 hash "^(hex_of_bytes digest));
          HandshakeLog.load_stateless_cookie log hrr digest;
          Some extra // for the server nego callback
      in
    match sm with
    | Error z ->
      trace ("negotiation failed: "^string_of_error z);
      Error z
    | Correct (ServerHelloRetryRequest hrr) ->
      // Internal HRR caused by group negotiation
      // We do not invoke the server nego callback in this case
      // record the initial offer and return the HRR to HS
      let ha = verifyDataHashAlg_of_ciphersuite hrr.hrr_cipher_suite in
      let digest = HandshakeLog.hash_tag #ha log in
      let cookie = Ticket.create_cookie hrr digest empty_bytes in
      let hrr = { hrr with hrr_extensions =
        (Extensions.E_cookie cookie) :: hrr.hrr_extensions; } in
      HST.op_Colon_Equals ns.state (S_HRR offer hrr);
      sm
    | Correct (ServerMode m cert _) ->
      let nego_cb = ns.cfg.nego_callback in
      let exts = Extensions.app_ext_filter offer.ch_extensions in
      let exts_bytes = HandshakeMessages.optionExtensionsBytes exts in
      trace ("Negotiation callback to handle extra extensions and query for stateless retry.");
      trace ("Application data in cookie: "^(match previous_cookie with | Some c -> hex_of_bytes c | _ -> "none"));
      match nego_cb.negotiate nego_cb.nego_context m.n_protocol_version exts_bytes previous_cookie with
      | Nego_abort ->
        trace ("Application requested to abort the handshake.");
        Error (AD_handshake_failure, "application aborted the handshake by callback")
      | Nego_retry cextra ->
        let hrr = ({
          hrr_sessionID = offer.ch_sessionID;
          hrr_cipher_suite = m.n_cipher_suite;
          hrr_extensions = [
            Extensions.E_supported_versions (Extensions.ServerPV TLS_1p3);
          ]}) in
        let ha = verifyDataHashAlg_of_ciphersuite hrr.hrr_cipher_suite in
        let digest = HandshakeLog.hash_tag #ha log in
        let cookie = Ticket.create_cookie hrr digest cextra in
        let hrr = { hrr with hrr_extensions =
          (Extensions.E_cookie cookie) :: hrr.hrr_extensions; } in
        ns.state := (S_HRR offer hrr);
        Correct (ServerHelloRetryRequest hrr)
      | Nego_accept sexts ->
        trace ("negotiated "^string_of_pv m.n_protocol_version^" "^string_of_ciphersuite m.n_cipher_suite);
        ns.state := S_ClientHello m cert;
        Correct (ServerMode m cert (Extensions.ext_of_custom sexts))

let share_of_serverKeyShare (ks:CommonDH.serverKeyShare) : share =
  let CommonDH.Share g gy = ks in (| g, gy |)

val server_ServerShare: #region:rgn -> t region Server ->
  option CommonDH.serverKeyShare -> extra_ext ->
  St (result mode)
let server_ServerShare #region ns ks app_exts =
  match HST.op_Bang ns.state with
  | S_ClientHello mode cert ->
    let cexts = mode.n_offer.ch_extensions in
    trace ("processing client extensions " ^ string_of_option_extensions cexts);
    match Extensions.negotiateServerExtensions
      mode.n_protocol_version
      cexts
      mode.n_offer.ch_cipher_suites
      ns.cfg
      mode.n_cipher_suite
      None  // option (TI.cVerifyData*TI.sVerifyData)
      mode.n_pski
      (Option.mapTot CommonDH.ServerKeyShare ks)
      (mode.n_sessionID = mode.n_offer.ch_sessionID)
    with
    | Error z -> Error z
    | Correct sexts ->
      begin
      trace ("including server extensions (SH + EE) " ^ string_of_option_extensions sexts);
      let sexts = match sexts with
        | Some el ->
          trace ("extra extensions from application callback: "^string_of_extensions app_exts);
          Some (el @ app_exts)
        | _ -> sexts
        in
      let mode = Mode
        mode.n_offer
        mode.n_hrr
        mode.n_protocol_version
        mode.n_server_random
        mode.n_sessionID
        mode.n_cipher_suite
        mode.n_pski
        sexts
        (Option.mapTot share_of_serverKeyShare ks)
        mode.n_client_cert_request
        mode.n_server_cert
        mode.n_client_share
      in
      HST.op_Colon_Equals ns.state (S_Mode mode cert);
      Correct mode
      end

//17-03-30 where is it used?
type hs_id = {
  id_cert: Cert.chain;
  id_sigalg: option signatureScheme;
}

//17-03-30 get rid of this wrapper?
type session = {
  session_nego: option mode;
}

// represents the outcome of a successful handshake,
// providing context for the derived epoch
type handshake =
  | Fresh of session // was sessionInfo
  | Resumed of session // was abbrInfo * sessionInfo
// We use SessionInfo as unique session indexes.
// We tried using instead hs, but this creates circularities
// We'll probably need a global log to reason about them.
// We should probably do the same in the session store.
