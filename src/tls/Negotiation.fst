module Negotiation

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open HandshakeMessages

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MR = FStar.Monotonic.RRef

//16-05-31 these opens are implementation-only; overall we should open less
open Extensions
open CoreCrypto

(**
  Debugging flag.
  F* normalizer will erase debug prints at extraction when set to false.
*)
inline_for_extraction let n_debug = false
 
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
(*
  | Offer:
    co_protocol_version: protocolVersion ->
    co_cipher_suites: (k:valid_cipher_suites{List.Tot.length k < 256}) ->
    co_compressions: (cl:list compression{ List.Tot.length cl > 0 /\ List.Tot.length cl < 256 }) ->
    co_namedGroups: list valid_namedGroup ->
    co_sigAlgs: list sigHashAlg ->
    co_safe_resumption: bool ->
    co_safe_renegotiation: bool ->
    co_resume: option sessionID ->
    // Each tag between 32 and 255 bytes, and the total length is < 2^16
    // We need a timestamp too, for obfuscated_ticket_age
    co_psks: list (PSK.pskIdentity * Hashing.anyTag) ->
    co_client_shares: list (g:CommonDH.group & CommonDH.share g) ->
    co_client_random: TLSInfo.random ->
    offer
*)    

type retryInfo (offer:offer) =
  hrr *
  (list (g:CommonDH.group & CommonDH.share g)) *
  (list (PSK.pskIdentity * Hashing.anyTag))

// The final negotiated outcome, including key shares and long-term identities.
// mode is the name used in the resilience paper;
// session_info is the one from TLSInfo
noeq type mode =
  | Mode:
    // Negotiated client offer
    n_offer: offer ->

    // Optional HRR (including cookie and overwritten part of initial offer)
    n_hrr: option (retryInfo n_offer) ->

    // more from SH (both TLS 1.2 and TLS 1.3)
    n_server_random: option TLSInfo.random ->

    // the resumption response
    n_resume: option bool -> // is this a 1.2 resumption with the offered sid?
    n_psk: option PSK.pskid -> // none with 1.2 (we are not doing PSK 1.2)
    n_sessionID: option sessionID -> // optional, proposed 1.2 id for *future* resumptions (not always what SH carries)

    n_protocol_version: protocolVersion ->
    n_kexAlg: TLSConstants.kexAlg ->
    n_aeAlg: TLSConstants.aeAlg ->
    n_sigAlg: TLSConstants.sigAlg ->
    n_cipher_suite: cipherSuite ->
    n_extensions: negotiatedExtensions ->
    n_server_extensions: (se:list extension{List.Tot.length se < 256}) ->
    n_scsv: list scsv_suite ->

    // more from SKE in ...ServerHelloDone (1.2) or SH (1.3)
    n_server_share: option (g:CommonDH.group & CommonDH.share g) ->

    // more from either ...ServerHelloDone (1.2) or ServerFinished (1.3)
    n_client_cert_request: option HandshakeMessages.cr ->
    n_server_cert: option Cert.chain ->

    // more from either CH+SH (1.3) or CKE (1.2)

    // This is the share selected
    n_client_share: option (g:CommonDH.group & CommonDH.share g) ->
    // { both shares are in the same negotiated group }
    mode

noeq type negotiationState (r:role) (cfg:config) (resume:resumeInfo r) =
  // Have C_Offer_13 and C_Offer? Shares aren't available in C_Offer yet
  | C_Init:     n_client_random: TLSInfo.random ->
                negotiationState r cfg resume
                
  | C_Offer:    n_offer: offer ->
                negotiationState r cfg resume

  | C_HRR:      n_offer: offer ->
                n_hrr: retryInfo n_offer ->
                negotiationState r cfg resume

  | C_WaitFinished1:
                n_offer: offer ->
                (* Here be fields of mode -> *)
                negotiationState r cfg resume

  | C_Mode:     n_mode: mode -> // In 1.2, used for resumption and full handshakes
                negotiationState r cfg resume

  | C_WaitFinished2: // Only 1.2
                n_mode: mode ->
                n_client_certificate: option Cert.chain ->
                negotiationState r cfg resume

  | C_Complete: n_mode: mode ->
                n_client_certificate: option Cert.chain ->
                negotiationState r cfg resume

  | S_Init:     n_server_random: TLSInfo.random ->
                negotiationState r cfg resume

  // Waiting for ClientHello2
  | S_HRR:      n_offer: offer ->
                n_hrr: hrr ->
                negotiationState r cfg resume

  // This state is used to wait for both Finished1 and Finished2
  | S_Mode:     n_mode: mode -> // If 1.2, then client_share is None
                negotiationState r cfg resume

  | S_Complete: n_mode: mode ->
                n_client_certificate: option Cert.chain ->
                negotiationState r cfg resume


let ns_rel (#r:role) (#cfg:config) (#resume:resumeInfo r) : MR.reln (negotiationState r cfg resume) =
  fun ns ns' ->
  match ns, ns' with
  | C_Init nonce, C_Init nonce' -> nonce == nonce'
  | C_Offer offer, C_Offer offer' -> offer == offer'
  | C_Init nonce, C_Offer offer -> nonce == offer.ch_client_random
  | _, _ -> True // TODO

noeq type t (region:rgn) (role:TLSConstants.role) =
  | NS:
    cfg: config -> // local configuration
    resume: TLSInfo.resumeInfo role ->
    state: MR.m_rref region (negotiationState role cfg resume) ns_rel ->
    t region role


val computeOffer: r:role -> cfg:config -> resume:TLSInfo.resumeInfo r -> nonce:TLSInfo.random -> 
  ks:option CommonDH.keyShare -> offer
let computeOffer r cfg resume nonce ks =
  let sid = 
    match resume with
    | Some sid, _ -> sid
    | None, _ -> empty_bytes
  in
  let extensions = 
    Extensions.prepareExtensions
      cfg.maxVer
      cfg.ciphersuites
      cfg.safe_renegotiation
      cfg.safe_resumption
      cfg.signatureAlgorithms
      cfg.namedGroups
      None // : option (cVerifyData * sVerifyData)
      ks
  in
  {
    ch_protocol_version = cfg.maxVer; // legacy for 1.3
    ch_client_random = nonce;
    ch_sessionID = sid;
    ch_cipher_suites = cfg.ciphersuites;
    // This file is reconstructed from ch_cipher_suites in HandshakeMessages.clientHelloBytes;
    ch_raw_cipher_suites = None; 
    ch_compressions = cfg.compressions;
    ch_extensions = Some extensions
  }


val create:
  region:rgn -> r:role -> cfg:TLSInfo.config -> resume:TLSInfo.resumeInfo r -> TLSInfo.random ->
  St (t region r)
let create region r cfg resume nonce =
  match r with
  | Client ->
    let state = MR.m_alloc region (C_Init nonce) in
    NS cfg resume state
  | Server ->
    let state = MR.m_alloc region (S_Init nonce) in
    NS cfg resume state

// a bit too restrictive: use a single Hash in any given offer
val hashAlg: #region:rgn -> #role:TLSConstants.role -> t region role -> Hashing.Spec.alg
let hashAlg #region #role ns =
  Hashing.Spec.SHA256

val local_config: #region:rgn -> #role:TLSConstants.role -> t region role -> TLSInfo.config
let local_config #region #role ns =
  NS?.cfg ns

val resume: #region:rgn -> #role:TLSConstants.role -> t region role -> TLSInfo.resumeInfo role
let resume #region #role ns =
  NS?.resume ns

val getMode: #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST mode
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let getMode #region #role nego =
  admit()
  //snd (NS?.state nego)

val version: #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST protocolVersion
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let version #region #role nego =
  admit()


(* CLIENT *)

// Checks that the protocol version in the CHELO message is
// within the range of versions supported by the server configuration
// and outputs the negotiated version if true
val negotiateVersion: cfg:config -> c:protocolVersion -> Tot (result protocolVersion)
let negotiateVersion cfg c =
  if geqPV c cfg.minVer && geqPV cfg.maxVer c then Correct c
  else if geqPV c cfg.maxVer then Correct cfg.maxVer
  else Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation failed")

val client_ServerHello: #region:rgn -> t region Client ->
  HandshakeMessages.sh ->
  St (result mode) // it needs to be computed, whether returned or not
let client_ServerHello #region ns sh =
  admit()
(*
  match negotiateVersion (NS?.cfg ns) pv with
  | Error e -> Error e
  | Correct pv ->

  ns := C_Mode
*)


(*
{
  sh_protocol_version:protocolVersion;
  sh_server_random:TLSInfo.random;
  sh_sessionID:option sessionID;  // JK : made optional because not present in TLS 1.3
  sh_cipher_suite:valid_cipher_suite;
  sh_compression:option compression; // JK : made optional because not present in TLS 1.3
  sh_extensions:option (se:list extension{List.Tot.length se < 256});
}

*)

val client_ServerKeyExchange: #region:rgn -> t region Client ->
  serverCert: HandshakeMessages.crt ->
  HandshakeMessages.ske ->
  ocr: option HandshakeMessages.cr ->
  St (result mode)
let client_ServerKeyExchange #region ns =
  admit()
(*
    let valid_chain = hs.cfg.check_peer_certificate => Cert.validate_chain c.crt_chain true cfg.peer_name cfg.ca_file in
    if not valid_chain then Error (AD_certificate_unknown_fatal, perror __SOURCE_FILE__ __LINE__ "Certificate validation failure")    else
      let ske_tbs = kex_s_to_bytes ske.ske_kex_s in
      let Some cs_sigalg = n.n_sigAlg in
      let sigalgs = n.n_extensions.ne_signature_algorithms in
      match sigHashAlg_of_ske ske.ske_sig with
      | None -> Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse SKE message")
      | Some ((sa,h),sigv) ->
            let algs: list sigHashAlg =
              match sigalgs with
              | Some l -> l
              | None -> [(cs_sigalg, Hash Hashing.Spec.SHA1)] in
            if not (List.Tot.existsb (fun (xs,xh) -> (xs = sa && xh = h)) algs)
            then Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Signature algorithm negotiation failed")
            else
              let a = Signature.Use (fun _ -> true) sa [h] false false in
              let csr = (n.n_client_random @| n.n_server_random) in
              let ems = n.n_extensions.ne_extended_ms in
              let tbs = to_be_signed n.n_protocol_version Server (Some csr) ske_tbs in
              match Signature.get_chain_public_key #a c.crt_chain with
              | None -> Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "failed to get public key from chain") )
              | Some pk ->
                   let valid_signature = Signature.verify #a h pk tbs sigv in
                   // debug_print("tbs = " ^ (Platform.Bytes.print_bytes tbs) ^ "\n");
                   debug_print("Signature validation status = " ^ (if valid then "OK" else "FAIL") ^ "\n");
                   if not valid_signature then Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "failed to check SKE signature")
                   else
                     match ske.ske_kex_s with
                     | KEX_S_RSA _ -> Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "only support ECDHE/DHE SKE") )
                     | KEX_S_DHE (| g, gy |) ->
*)


assume val clientComplete_13: #region:rgn -> #role:TLSConstants.role -> t region role ->
  HandshakeMessages.ee ->
  ocr: option HandshakeMessages.cr ->
  serverCert: HandshakeMessages.crt ->
  cv: HandshakeMessages.cv ->
  digest:  bytes{length digest <= 32} ->
  St (result mode) // it needs to be computed, whether returned or not


(* SERVER *)

//HS
assume val server_ClientHello: #region:rgn -> #role:TLSConstants.role -> t region role ->
  HandshakeMessages.ch ->
  St (result mode)

//17-03-30 still missing a few for servers.



// TODO factor out signature processing, salvaging chunks from Handshake.fst


//17-03-30 where is it used?
type hs_id = {
  id_cert: Cert.chain;
  id_sigalg: option sigHashAlg;
}

//17-03-30 get rid of this wrapper?
type session = {
  session_nego: mode;
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

// to be renamed and extended to support HS keys, then 0RTT keys
val handshakeKeyInfo:
  #region:rgn -> r:TLSConstants.role -> t region r -> St handshake

// For use in negotiating the ciphersuite, takes two lists and
// outputs the first ciphersuite in list2 that also is in list
// one and is a valid ciphersuite, or [None]
val negotiate:l1:list valid_cipher_suite -> list valid_cipher_suite -> Tot (option (c:valid_cipher_suite{CipherSuite? c && List.Tot.mem c l1}))
let negotiate l1 l2 =
  List.Tot.find #valid_cipher_suite (fun s -> CipherSuite? s && List.Tot.mem s l1) l2

// For use in ensuring the result from negotiate is a Correct
// ciphersuite with associated kex, sig and ae algorithms,
// and throws an error if No ciphersuites were supported in both lists
val negotiateCipherSuite: cfg:config -> pv:protocolVersion -> ccs:valid_cipher_suites -> Tot (result (TLSConstants.kexAlg * option TLSConstants.sigAlg * TLSConstants.aeAlg * valid_cipher_suite))
let negotiateCipherSuite cfg pv ccs =
  match negotiate ccs cfg.ciphersuites with
  | Some(CipherSuite kex sa ae) -> Correct(kex,sa,ae,CipherSuite kex sa ae)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Cipher suite negotiation failed")

assume
val negotiateGroupKeyShare: config -> protocolVersion -> kexAlg -> option (list extension) -> Tot (result (option namedGroup * option bytes))
(*
let rec negotiateGroupKeyShare cfg pv kex exts =
  match exts with
  | None when (pv = TLS_1p3) -> Error(AD_decode_error, "no supported group or key share extension found")
  | Some exts when (pv = TLS_1p3) ->
    let rec aux: list extension -> Tot (result (option namedGroup * option bytes)) =
      function
      | E_key_share (CommonDH.ClientKeyShare gl) :: _ ->
        let inConf (gn, gx) =
           (((SEC? gn) && (kex = Kex_ECDHE || kex = Kex_PSK_ECDHE))
            || ((FFDHE? gn) && (kex = Kex_DHE || kex = Kex_PSK_DHE)))
           && List.Tot.mem gn cfg.namedGroups in
        (match List.Tot.filter inConf gl with
        | share :: _ -> Correct (Some share)
        | [] -> Error(AD_decode_error, "no shared group between client and server config"))
      | _ :: t -> aux t
      | [] -> Error(AD_decode_error, "no supported group or key share extension found")
    in aux exts
  | Some exts when (kex = Kex_ECDHE && List.Tot.existsb E_supported_groups? exts) ->
    let Some (E_supported_groups gl) = List.Tot.find E_supported_groups? exts in
    let filter x = SEC? x && List.Tot.mem x cfg.namedGroups in
    (match List.Tot.filter filter gl with
    | gn :: _ -> Correct (Some gn, None)
    | [] -> Error(AD_decode_error, "no shared curve configured"))
  | _ ->
    let filter x =
      (match kex with | Kex_DHE -> FFDHE? x | Kex_ECDHE -> SEC? x | _ -> false) in
    if kex = Kex_DHE || kex = Kex_ECDHE then
      (match List.Tot.filter filter cfg.namedGroups with
      | gn :: _ -> Correct (Some gn, None)
      | [] -> Error(AD_decode_error, "no valid group is configured for the selected cipher suite"))
    else Correct(None, None)
*)


// Determines if the server random value contains a downgrade flag
// AND if there has been a downgrade
// The downgrade flag is a random value set by RFC (6.3.1.1)
val isSentinelRandomValue: protocolVersion -> protocolVersion -> TLSInfo.random -> Tot bool
let isSentinelRandomValue c_pv s_pv s_random =
  geqPV c_pv TLS_1p3 && geqPV TLS_1p2 s_pv && equalBytes (abytes "DOWNGRD\x01") s_random ||
  geqPV c_pv TLS_1p2 && geqPV TLS_1p1 s_pv && equalBytes (abytes "DOWNGRD\x00") s_random


// Confirms that the version negotiated by the server was:
// - within the range specified by client config AND
// - is not an unnecessary downgrade AND
// - is not a newer version than offered by the client

val acceptableVersion: config -> protocolVersion -> protocolVersion -> TLSInfo.random -> Tot bool
let acceptableVersion cfg cpv spv sr =
  match negotiateVersion cfg cpv with
  | Correct c_pv ->
    geqPV c_pv spv && geqPV spv cfg.minVer &&
    not (isSentinelRandomValue c_pv spv sr)
  | Error _ -> false

// Confirms that the ciphersuite negotiated by the server was:
//  - consistent with the client config;
//  - TODO: [s_cs] is supported by the protocol version (e.g. no GCM with
//    TLS<1.2).
// BD: Removed that the ciphersuite is acceptable given CHELO
// given that the clientOffer is prepared with the entire list
// of valid cipher suites in the client config
val acceptableCipherSuite: config -> protocolVersion -> valid_cipher_suite -> Tot bool
let acceptableCipherSuite cfg spv cs =
  List.Tot.existsb (fun x -> x = cs) cfg.ciphersuites &&
  not (isAnonCipherSuite cs) || cfg.allowAnonCipherSuite

// TODO ADL: incorrect as written; CS nego depends on ext nego
//   (e.g. in TLS 1.2 it's incorrect to select an EC cipher suite if
//         EC extensions are missing)
// FIXME ADL
// I have hacked nego to at least not pick a bad CS for the server's cert keytype
// but this REALLY needs to be rewritten properly from scratch by someone who has
// read all TLS RFCs
// FIXME ADL: grossly inefficient; we need to cache the server keytype at startup
// TODO BD: ignoring extensions for the moment
// due to the fact that we require calling the keyschedule
// in between negotiating the named Group and preparing the
// negotiated Extensions
(* TODO: why irreducible? *)
irreducible val computeServerMode: cfg:config -> cpv:protocolVersion -> ccs:valid_cipher_suites -> cexts:option (list extension) -> comps: (list compression) -> ri:option (cVerifyData*sVerifyData) -> Tot (result mode)
let computeServerMode cfg cpv ccs cexts comps ri =
  (match (negotiateVersion cfg cpv) with
    | Error(z) -> Error(z)
    | Correct(npv) ->
  let nosa = fun (CipherSuite _ sa _) -> None? sa in
  let sigfilter = match Cert.lookup_chain cfg.cert_chain_file with
    | Correct(c) when (Some? (Cert.endpoint_keytype c)) ->
      let kt = Cert.endpoint_keytype c in
      (fun (CipherSuite _ sa _) ->
        match sa,kt with
        | Some sa, Some kt ->
          (match sa, kt with
          | RSASIG, KeyRSA _ | RSAPSS, KeyRSA _
          | ECDSA, KeyECDSA _ | DSA, KeyDSA _ -> true
          | _ -> false)
        | _ -> false)
    | _ ->
       let _ =
        if n_debug then
          IO.debug_print_string "WARNING cannot load server cert; restricting to anonymous CS...\n"
        else false in
       nosa in
  let ccs = List.Tot.filter sigfilter ccs in
  match negotiateCipherSuite cfg npv ccs with
    | Error(z) -> Error(z)
    | Correct(kex,sa,ae,cs) ->
  let nego = ne_default in
  let next = (match cexts with
   | Some cexts -> Correct(List.Tot.fold_left (clientToNegotiatedExtension cfg cs ri false) nego cexts)
//   | None -> ne_default)
   | None -> (match npv with
              | SSL_3p0 ->
                let cre =
                  if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV (list_valid_cs_is_list_cs ccs) then
                     {ne_default with ne_secure_renegotiation = RI_Valid}
                  else ne_default
                in Correct (cre)
             | _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Missing extensions in TLS client hello")))
  in
  let ng = negotiateGroupKeyShare cfg npv kex cexts in
  match next, ng with
    | Error(z), _ | _, Error(z) -> Error(z)
    | Correct(next), Correct(gn, gxo) ->
      let comp = match comps with
                 | [] -> None
                 | _ -> Some NullCompression in
      let mode = admit () in
      (*{
        sm_protocol_version = npv;
        sm_kexAlg = kex;
        sm_aeAlg = ae;
        sm_sigAlg = sa;
        sm_cipher_suite = cs;
        sm_dh_group = gn;
        sm_dh_share = gxo;
        sm_comp = comp;
        sm_ext = next;
      } in *)
      Correct (mode))


irreducible val computeClientMode: cfg:config -> cext:option (list extension) -> cpv:protocolVersion -> spv:protocolVersion -> sr:TLSInfo.random -> cs:valid_cipher_suite -> sext:option (list extension) -> comp:option compression -> option ri -> Tot (result mode)
let computeClientMode cfg cext cpv spv sr cs sext comp ri =
  if not (acceptableVersion cfg cpv spv sr) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
  else if not (acceptableCipherSuite cfg spv cs) then
    Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
  else
   let resume = false in
   match negotiateClientExtensions spv cfg cext sext cs ri resume with
    | Error(z) -> Error(z)
    | Correct(next) ->
    match cs with
     | CipherSuite kex sa ae ->
      match spv, kex, next.ne_keyShare with
       | TLS_1p3, Kex_DHE, Some gy
       | TLS_1p3, Kex_ECDHE, Some gy ->
         let mode = admit() in
         (*
         {cm_protocol_version = spv;
          cm_kexAlg = kex;
          cm_aeAlg = ae;
          cm_sigAlg = sa;
          cm_cipher_suite = cs;
          cm_dh_share = Some gy;
          cm_comp = comp;
          cm_ext = next;
         } in *)
         Correct mode
       | _ ->
         let mode = admit() in
         (*
         {cm_protocol_version = spv;
          cm_kexAlg = kex;
          cm_aeAlg = ae;
          cm_sigAlg = sa;
          cm_cipher_suite = cs;
          cm_dh_share = None;
          cm_comp = comp;
          cm_ext = next;
         } in *)
         Correct mode
      | _ -> Error (AD_decode_error, "ServerHello ciphersuite is not a real ciphersuite")
