module Negotiation.Version

open Parsers.ProtocolVersion
open Parsers.ClientHelloExtension
open TLSConstants // for leqPV and the configuration

open FStar.Error
open TLSError

// updated excerpts of Negotiation re: protocol versions

/// ---- PROTOCOL VERSIONS ----
///
/// The protocol version is negotiated in ClientHello and ServerHello,
/// using two overlapping mechanisms.  We currently implement only TLS
/// 1.2 and 1.3, and the negotiated version can be further constrained
/// in the connection initial configuration.

// 19-01-04 TODO? 
// * replace min/max_version in config with the payload of the supported_version extension.
// * refine TLSConstants.protocolVersion with implemented instead of not Unknown. 

let implemented pv =
  pv = TLS_1p2 || pv = TLS_1p3

let (<=) = leqPV

let supported cfg pv =
  implemented pv &&
  cfg.min_version <= pv && pv <= cfg.max_version


// negotiation failures; unnecessary?
// private let illegal       #a msg: result a = fatal #a Illegal_parameter msg
// private let unsupported   #a msg: result a = fatal #a Unsupported_extension msg
// private let fatal_version #a msg: result a = fatal #a Protocol_version msg

/// (1) Client offers supported versions
///
/// Offer only locally-implemented versions, irrespective of the
/// configuration. We may provide more flexible configurations by replacing
/// min/max_version with a list of supported versions.

#set-options "--z3rlimit 100" // 19-01-04 too slow? note the refinement on the length of the inner lists. 
let supported_versions cfg: option clientHelloExtension =
  match cfg.min_version, cfg.max_version with
  | TLS_1p3, TLS_1p3 -> Some (Case_supported_versions [TLS_1p3])
  | TLS_1p2, TLS_1p3 -> Some (Case_supported_versions [TLS_1p3; TLS_1p2])
  | TLS_1p2, TLS_1p2 -> Some (Case_supported_versions [TLS_1p2])
  | _                -> None

let cons_supported cfg pv pvs = if supported cfg pv then pv::pvs else pvs 

let supported_versions2 cfg: option clientHelloExtension =
  let vs = cons_supported cfg TLS_1p2 [] in 
  let vs = cons_supported cfg TLS_1p3 vs in 
  if List.isEmpty vs then None 
  else Some(Case_supported_versions vs)
// easier to refine and extract; worth the trouble? 

(* too large?
let same_supported cfg: Lemma (supported_versions cfg == supported_versions2 cfg) =
  match cfg.min_version, cfg.max_version with
  | SSL_3p0, SSL_3p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | SSL_3p0, TLS_1p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | SSL_3p0, TLS_1p1 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | SSL_3p0, TLS_1p2 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | SSL_3p0, TLS_1p3 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p0, SSL_3p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p0, TLS_1p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p0, TLS_1p1 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p0, TLS_1p2 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p0, TLS_1p3 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p1, SSL_3p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p1, TLS_1p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p1, TLS_1p1 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p1, TLS_1p2 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p1, TLS_1p3 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p2, SSL_3p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p2, TLS_1p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p2, TLS_1p1 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p2, TLS_1p2 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p2, TLS_1p3 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p3, SSL_3p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p3, TLS_1p0 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p3, TLS_1p1 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p3, TLS_1p2 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
  | TLS_1p3, TLS_1p3 -> assert_norm (supported_versions cfg == supported_versions2 cfg)
*)

#reset-options 

/// (2) Server chooses a supported version
///
/// Check that the protocol version in ClientHello is within the
/// range of versions supported by the server configuration and
/// outputs the negotiated version if true

type offer = Parsers.ClientHello.clientHello // temporary

// We ignore the "minimal protocol version" signalled in the packet
// header; this is fine since our server never accepts any proposal
// below the "maximal protocol version".

let correct #a (x:a): result a = Correct x
 
#set-options "--z3rlimit 100"
val choose_version: cfg:config -> offer -> result (pv:protocolVersion{ supported cfg pv })
let choose_version cfg offer =
  let legacy_max_pv = offer.Parsers.ClientHello.version in
  if TLS_1p3 <= legacy_max_pv then
    fatal Protocol_version "protocol version negotiation: bad legacy proposal"
  else
    match List.Tot.find Case_supported_versions? offer.Parsers.ClientHello.extensions with
    | None ->
      // legacy negotiation: we pick at most TLS 1p2
      if legacy_max_pv = TLS_1p2 && supported cfg TLS_1p2 then
        correct TLS_1p2
      else
        fatal Protocol_version "protocol version negotiation: mismatch"

    | Some (Case_supported_versions vs) ->
      // new extension-based negotiation: we pick the first client offer supported by the server
      match List.Helpers.find_aux cfg supported vs with
      | Some v -> correct v
      | None -> fatal Protocol_version "protocol version negotiation: mismatch"
#reset-options

/// (3) Client validates the server's choice

val isSentinelRandomValue:
  Parsers.ProtocolVersion.protocolVersion ->
  Parsers.ProtocolVersion.protocolVersion ->
  TLSInfo.random ->
  bool
let isSentinelRandomValue client_pv server_pv server_random =
  let open FStar.Bytes in
  let down = bytes_of_string "DOWNGRD" in
  assume(length down = 7 /\ length (abyte 1z) = 1 /\ length (abyte 0z) = 1); //18-12-16 TODO how?
  (server_pv <= TLS_1p2 && TLS_1p3 <= client_pv && server_random = down @| abyte 1z) ||
  (server_pv <= TLS_1p1 && TLS_1p2 <= client_pv && server_random = down @| abyte 0z)

val accept_version:
  cfg: config ->
  pv: protocolVersion ->
  ses: Parsers.ServerHello_extensions.serverHello_extensions ->
  sr: TLSInfo.random ->
  result (pv: Parsers.ProtocolVersion.protocolVersion{ supported cfg pv })

// 18-12-23 separate protocol-version negotiation, usable as spec & implementation.
let accept_version cfg pv ses sr =
  if pv = TLS_1p3 then
    fatal Illegal_parameter "cannot negotiate TLS 1.3 explicitly"
  else
    let open Parsers.ServerHelloExtension in
    let chosen: Parsers.ProtocolVersion.protocolVersion (*may be unknown*) =
      match List.Tot.find Case_supported_versions? ses with
      | None -> pv // old style
      | Some (Case_supported_versions pv) -> pv in
    if TLS_1p3 <= chosen && pv <> TLS_1p2 then
      fatal Illegal_parameter "extension-based version negotiation requires TLS 1.2 apparent version"
    else
    if isSentinelRandomValue cfg.max_version chosen sr then 
      fatal Illegal_parameter "protocol-version downgrade attempt"
    else 
    if not (supported cfg chosen) then 
      fatal Illegal_parameter "client did not offer this protocol version"
    else
      correct chosen


(* BEYOND VERSIONS *) 

/// ----
///
/// server's handling of ClientHello, a rather long stateful function.
/// calling (pure) computeServerMode, then the application callback. 
///
 
let find_client_extension (filter:clientHelloExtension -> bool) o
  : option (e:clientHelloExtension{filter e}) =
  List.Tot.find filter o.Parsers.ClientHello.extensions 

let find_client_key_shares (o:offer): Parsers.KeyShareClientHello.keyShareClientHello =
  match find_client_extension Case_key_share? o with
  | Some (Case_key_share x) -> x
  | _ -> assume(Parsers.KeyShareClientHello.keyShareClientHello_list_bytesize [] = 0); []
//TODO 19-01-04 where to get it from? 

let group_of_hrr hrr : option CommonDH.group = None
//19-01-03 TODO where are QD's HRR extensions? 
(*
  match List.Tot.find (Extensions.E_key_share?) hrr.hrr_extensions with
  | Some (Extensions.E_key_share (CommonDH.HRRKeyShare ng)) ->
    CommonDH.group_of_namedGroup ng
  | _ -> None
*)

private
let sameExtensionTag e0 e1 = tag_of_clientHelloExtension e0 = tag_of_clientHelloExtension e1 

private
let retry_extension_ok (o1, hrr) (e:clientHelloExtension) = 
  match e with
// 19-01-04 TODO   
// | Case_key_share shares2 -> (
//     match shares2, group_of_hrr hrr with
//     | [CommonDH.Share g _], Some g' -> g = g'
//     | _, None ->
//         let shares1 = find_client_key_shares o1 in
//         //TODO 19-01-03 easier on the underlying wire representation
//         Parsers.KeyShareClientHello.keyShareClientHello_serializer32 shares1 =
//         Parsers.KeyShareClientHello.keyShareClientHello_serializer32 shares2
//         // CommonDH.clientKeyShareBytes shares1 = CommonDH.clientKeyShareBytes shares2
//     | _ -> false)
  | Case_early_data _ -> false // Forbidden
  | Case_cookie c -> true // FIXME we will send cookie
      // If we add cookie support we need to treat this case separately
      // | Extensions.E_cookie c -> c = S_HRR?.cookie ns.state
  | e ->
        (match List.Helpers.find_aux e sameExtensionTag o1 with
        | None -> (IO.debug_print_string "Extra extension\n") && false
        // This allows the client to send less extensions,
        // but the ones that are sent must be exactly the same
        | Some e' ->
          //FIXME: Extensions.E_pre_shared_key "may be updated" 4.1.2
          true) // FIXME
          //(extensionBytes e) = (extensionBytes e'))

// check the second offer is compatible with the first (see RFC)
let retry_offer_ok o1 hrr o2 = 
  let open Parsers.ClientHello in 
  o1.version = o2.version &&
  o1.random = o2.random &&
  o1.session_id = o2.session_id &&
// TODO 19-01-04 
//  o1.session_id = hrr.hrr_sessionID &&
//  List.Tot.mem hrr.hrr_cipher_suite o2.ch_cipher_suites &&
  o1.compression_method = o2.compression_method &&
  List.Helpers.forall_aux (o1.extensions, hrr) retry_extension_ok o2.extensions

open Mem 

(*
val server_ClientHello: // #region:rgn -> t region Server ->
  offer -> // log:HandshakeLog.t ->
  St (result serverMode)
#set-options "--admit_smt_queries true"
let server_ClientHello #region ns offer log =
  trace ("offered client extensions "^string_of_option_extensions offer.ch_extensions);
  trace ("offered cipher suites "^(string_of_ciphersuitenames offer.ch_cipher_suites));
  trace (match (offered_versions TLS_1p0 offer) with
        | Error z -> "Error: "^string_of_error z
        | Correct v -> List.Tot.fold_left accum_string_of_pv "offered versions" v);
  match !ns.state with
  | S_HRR o1 hrr ->
    trace ("Processing second offer based on existing HRR state (stateful HRR).");
    if retry_offer_ok o1 offer
    then
      let sm = computeServerMode ns.cfg offer ns.nonce in
      match sm with
      | Error z ->
        trace ("negotiation failed: "^string_of_error z);
        Error z
      | Correct (ServerHelloRetryRequest hrr _) ->
        fatal Illegal_parameter "client sent the same hello in response to hello retry"
      | Correct (ServerMode m cert _) ->
        trace ("negotiated after HRR "^string_of_pv m.n_protocol_version^" "^string_of_ciphersuite m.n_cipher_suite);
        let nego_cb = ns.cfg.nego_callback in
        let exts_bytes = Extensions.app_extensions_bytes offer.ch_extensions in
        trace ("Negotiation callback to handle extra extensions.");
        match nego_cb.negotiate nego_cb.nego_context m.n_protocol_version exts_bytes (Some empty_bytes) with
        | Nego_accept sexts ->
          let el = Extensions.ext_of_custom sexts in
          ns.state := S_ClientHello m cert;
          Correct (ServerMode m cert el)
        | _ ->
          trace ("Application requested to abort the handshake after internal HRR.");
          fatal Handshake_failure "application aborted the handshake by callback"
    else
      fatal Illegal_parameter "Inconsistant parameters between first and second client hello"

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
    | Correct (ServerHelloRetryRequest hrr cs) ->
      // Internal HRR caused by group negotiation
      // We do not invoke the server nego callback in this case
      // record the initial offer and return the HRR to HS
      let ha = verifyDataHashAlg_of_ciphersuite cs in
      let digest = HandshakeLog.hash_tag #ha log in
      let cookie = Ticket.create_cookie hrr digest empty_bytes in
      let hrr = { hrr with hrr_extensions =
        (Extensions.E_cookie cookie) :: hrr.hrr_extensions; } in
      ns.state := S_HRR offer hrr;
      sm
    | Correct (ServerMode m cert _) ->
      let nego_cb = ns.cfg.nego_callback in
      let exts_bytes = Extensions.app_extensions_bytes offer.ch_extensions in
      trace ("Negotiation callback to handle extra extensions and query for stateless retry.");
      trace ("Application data in cookie: "^(match previous_cookie with | Some c -> hex_of_bytes c | _ -> "none"));
      match nego_cb.negotiate nego_cb.nego_context m.n_protocol_version exts_bytes previous_cookie with
      | Nego_abort ->
        trace ("Application requested to abort the handshake.");
        fatal Handshake_failure "application aborted the handshake by callback"
      | Nego_retry cextra ->
        let hrr = ({
          hrr_sessionID = offer.ch_sessionID;
          hrr_cipher_suite = name_of_cipherSuite m.n_cipher_suite;
          hrr_extensions = [
            Extensions.E_supported_versions (Extensions.ServerPV TLS_1p3);
          ]}) in
        let ha = verifyDataHashAlg_of_ciphersuite m.n_cipher_suite in
        let digest = HandshakeLog.hash_tag #ha log in
        let cookie = Ticket.create_cookie hrr digest cextra in
        let hrr = { hrr with hrr_extensions =
          (Extensions.E_cookie cookie) :: hrr.hrr_extensions; } in
        ns.state := (S_HRR offer hrr);
        Correct (ServerHelloRetryRequest hrr m.n_cipher_suite)
      | Nego_accept sexts ->
        trace ("negotiated "^string_of_pv m.n_protocol_version^" "^string_of_ciphersuite m.n_cipher_suite);
        ns.state := S_ClientHello m cert;
        Correct (ServerMode m cert (Extensions.ext_of_custom sexts))
*)
