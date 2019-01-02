module Negotiation.Version

open Parsers.ClientHelloExtension
open Parsers.ProtocolVersion
open TLSConstants

// updated excerpts of Negotiation re: protocol versions


// cutting down on cases to consider after negotiation
let implemented pv =
  pv = TLS_1p2 || pv = TLS_1p3

let (<=) = leqPV

let supported cfg pv =
  implemented pv &&
  cfg.min_version <= pv && pv <= cfg.max_version


open FStar.Error
open TLSError

private let illegal #a msg: result a = fatal #a Illegal_parameter msg
private let unsupported #a msg: result a = fatal #a Unsupported_extension msg


/// (1) Client offers supported versions
///
/// Offer only locally-implemented versions, irrespective of the
/// configuration. We may provide more flexible configurations by replacing
/// min/max_version with a list of supported versions.

#set-options "--z3rlimit 100" // 70'' to TC ?!.
let supported_versions cfg: option clientHelloExtension =
  match cfg.min_version, cfg.max_version with
  | TLS_1p3, TLS_1p3 -> Some (Case_supported_versions [TLS_1p3])
  | TLS_1p2, TLS_1p3 -> Some (Case_supported_versions [TLS_1p3; TLS_1p2])
  | TLS_1p2, TLS_1p2 -> Some (Case_supported_versions [TLS_1p2])
  | _                -> None
#reset-options ""


/// (2) Server chooses a version
///
/// Check that the protocol version in ClientHello is within the
/// range of versions supported by the server configuration and
/// outputs the negotiated version if true

(*
// no need to filter unknowns, since they can't be locally configured
// we might also check no proposal is below min_pv
private let rec filter_unknown_versions: list protocolVersion' -> list protocolVersion = function
  | Unknown_protocolVersion _::vs -> filter_unknown_versions vs
  | v::vs -> v::filter_unknown_versions vs
  | [] -> []
*)

type offer = Parsers.ClientHello.clientHello // temporary

// We ignore the "minimal protocol version" signalled in the packet
// header; this is fine since our server never accepts any proposal
// below the "maximal protocol version".

let correct #a (x:a): result a = Correct x

#set-options "--z3rlimit 100"
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
      | None -> fatal TLSError.Protocol_version "protocol version negotiation: mismatch"
#reset-options
// 150'' to TC?!


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

let acceptable cfg (pv: Parsers.ProtocolVersion.protocolVersion) sr =
  // we statically know that the offered versions are compatible with our config
  // (we may prove e.g. acceptableVersion pv ==> pv in offered_versions
  supported cfg pv &&
  not (isSentinelRandomValue cfg.max_version pv sr)

val accepted_version:
  cfg: config ->
  pv: protocolVersion ->
  ses: Parsers.ServerHello_extensions.serverHello_extensions ->
  sr: TLSInfo.random ->
//18-12-29 wont tc?!
//result (pv: Parsers.ProtocolVersion.protocolVersion{ acceptable cfg pv sr })
  result Parsers.ProtocolVersion.protocolVersion

// 18-12-23 separate protocol-version negotiation, usable as spec & implementation.
let accepted_version cfg pv ses sr =
  if pv = TLS_1p3 then
    illegal "cannot negotiate TLS 1.3 explicitly"
  else
    let open Parsers.ServerHelloExtension in
    let chosen: Parsers.ProtocolVersion.protocolVersion (*may be unknown*) =
      match List.Tot.find Case_supported_versions? ses with
      | None -> pv // old style
      | Some (Case_supported_versions pv) -> pv in
    if TLS_1p3 <= chosen && pv <> TLS_1p2 then
      illegal "extension-based version negotiation requires TLS 1.2 apparent version"
    else
    if acceptable cfg chosen sr then
      correct pv
    else
      illegal "client did not offer this protocol version"

// Note TLSConstants.protocolVersion is a (not so useful) not-unknown refinement of Parsers.ProtocolVersion.protocolVersion.
// #(pv: Parsers.ProtocolVersion.protocolVersion{ acceptable cfg pv sr })

/// ----
///
/// server's handling of ClientHello, a rather long stateful function.
/// trying to write down its pure specification.
///
/// effects: 
/// 
///
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
    trace ("Processing second offer based on existing HRR state (staeful HRR).");
    let o2 = offer in
    let extension_ok =
      if Some? o2.ch_extensions && Some? o1.ch_extensions then
        List.Helpers.forall_aux (o1, hrr) aux_extension_ok (Some?.v o2.ch_extensions)
      else
        false
    in
    if
      o1.ch_protocol_version = o2.ch_protocol_version &&
      o1.ch_client_random = o2.ch_client_random &&
      o1.ch_sessionID = o2.ch_sessionID &&
      o1.ch_sessionID = hrr.hrr_sessionID &&
      List.Tot.mem hrr.hrr_cipher_suite o2.ch_cipher_suites &&
      o1.ch_compressions = o2.ch_compressions &&
      extension_ok
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
