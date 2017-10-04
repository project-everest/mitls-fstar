module QUIC

/// QUIC-specific interface on top of our main TLS API
/// * establishes session & exported keys: no application-data traffic!
/// * simplified configuration, with reasonable defaults
/// * TCP-like send/recv callbacks operate on caller-provided buffers
///   recv may yield (not enough input)
///   send is guaranteed to succeed (large enough output buffer expected)
///
/// See https://tools.ietf.org/html/draft-ietf-quic-tls-04
///
/// Relying on FFI for accessing configs, callbacks, etc.
/// Testing both in OCaml (TCP-based, TestQUIC ~ TestFFI) and in C.

open Platform.Bytes
open Platform.Error
open TLSConstants
open TLSInfo
open Range
open DataStream
open TLS
open FFICallbacks

open FStar.HyperStack.All

#set-options "--lax"

(* A flag for runtime debugging of ffi data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("QIC| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_QUIC then print else (fun _ -> ())


// an integer carrying the fatal alert descriptor
// we could also write txt into the application error log
type error = UInt16.t
private let errno description txt: ST error
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> h0 == h1)
=
  trace ("returning error"^
    (match description with
    | Some ad -> " "^TLSError.string_of_ad ad
    | None    -> "")^": "^txt);
  let b2 = Alert.alertBytes (match description with | Some a -> a | None -> TLSError.AD_internal_error) in
  Parse.uint16_of_bytes b2

/// TLS processing loop: we keep receiving and sending as long as we
/// can read.  Does not handle TLS termination (unused by QUIC?)
///
(* Alternatively, we could maintain a result record with room for all results, e.g.
type result = {
  local_error: error;
  peer_error: error;
  secret0: bool; // the 0RTT key is available
  secret1: bool; // the 1RTT key is available
  refused0: bool ; // the server refused 0RTT
  complete: bool; // the handshake is complete
  ticket: bool; // a server ticket has been sent/received
}
*)

type resultcode =
  | TLS_would_block // More input bytes are required to proceed
  | TLS_error_local // A fatal error occurred locally
  | TLS_error_alert // The peer reported a fata error
  // The client offered a connection with early data.  Secret0 is
  // available, but note the client hasn't heard from the server yet.
  | TLS_client_early_data

  // The client completed the connection: the server is authenticated
  // and both parties agree on the connection, including their QUIC
  // parameters and whether early data is received or discarded.
  //
  // Secret1 and the server parameters & certificates are available.
  | TLS_client_complete
  | TLS_client_complete_with_early_data

  // The server accepted the connection, with or without early data.
  // Secret0 (if early traffic is accepted), Secret1, and the client
  // parameters are now available.
  | TLS_server_accept
  | TLS_server_accept_with_early_data

  // The server now knows that the client agrees on the connection, and
  // may have sent a resumption ticket (for future early data)
  | TLS_server_complete

type result = {
  code: resultcode;
  error: error; // we could keep more details
}

val recv: Connection.connection -> St result
let rec recv c =
  let i = currentId c Reader in
  match read c i with
  | Update false     -> recv c // do not report intermediate, internal key changes
  | ReadWouldBlock   -> {code=TLS_would_block; error=0us;}
  | Update true -> (
       let keys = Handshake.xkeys_of c.Connection.hs in
       match Connection.c_role c, Seq.length keys with
       | Client, 1   -> {code=TLS_client_early_data; error=0us;}
       | Server, 1   -> {code=TLS_server_accept; error=0us;}
       | Server, 2   -> {code=TLS_server_accept_with_early_data; error=0us;}
       | _           -> {code=TLS_error_local; error=errno None "unexpected exporter keys"})
  | Complete -> (
       let keys = Handshake.xkeys_of c.Connection.hs in
       match Connection.c_role c with
       | Client -> if Negotiation.zeroRTT (Handshake.get_mode c.Connection.hs)
                  then {code=TLS_client_complete_with_early_data; error=0us;}
                  else {code=TLS_client_complete; error=0us;}
       | Server      -> {code=TLS_server_complete; error=0us;})
         (* we could read once more to flush any ticket.
                      let i = currentId c Reader in
                      match read c i with
                      | ReadWouldBlock -> {code=TLS_server_complete; error=0us;}
                      | _ -> {code=TLS_error_local; error=errno None "bad ticket delivery";} *)
  | ReadError a txt  -> {code=TLS_error_local; error=errno a txt;}
  | Read Close       -> {code=TLS_error_alert; error=errno (Some TLSError.AD_close_notify) "received close";}
  | Read (Alert a)   -> {code=TLS_error_alert; error=errno (Some a) "received alert";}
  | _                -> {code=TLS_error_local; error=errno None "unexpected TLS read result";}

let quic_check config =
  if config.min_version <> TLS_1p3 then trace "WARNING: not TLS 1.3";
  if not config.non_blocking_read then trace "WARNING: reads are blocking";
  if None? config.quic_parameters then trace "WARNING: missing parameters";
  if None? config.alpn            then trace "WARNING: missing ALPN"

/// New client and server connections (without any  I/O yet)
/// [send] and [recv] are callbacks to operate on QUIC stream0 buffers
/// [config] is a client configuration for QUIC (see above)
/// [psks] is a list of proposed pre-shared-key identifiers and tickets
let connect send recv config psks: ML Connection.connection =
  // we assume the configuration specifies the target SNI;
  // otherwise we must check the authenticated certificate chain.
  let tcp = Transport.callbacks send recv in
  let here = new_region HyperHeap.root in
  quic_check config;
  TLS.resume here tcp config None psks

/// [send] and [recv] are callbacks to operate on QUIC stream0 buffers
/// [config] is a server configuration for QUIC (see above)
/// tickets are managed internally
let accept send recv config : ML Connection.connection =
  let tcp = Transport.callbacks send recv in
  let here = new_region HyperHeap.root in
  quic_check config;
  TLS.accept_connected here tcp config

// Ticket also includes the serialized session,
// if it is not in the PSK database it will be installed
// (allowing resumption across miTLS client processes)
val ffiConnect: config:config -> ticket: option (bytes * bytes) -> callbacks:FFI.callbacks -> ML Connection.connection
let ffiConnect config ticket cb =
  let send = FFI.sendTcpPacket cb in
  let recv = FFI.recvTcpPacket cb in
  connect send recv config (FFI.install_ticket config ticket)

val ffiAcceptConnected: config:config -> callbacks:FFI.callbacks -> ML Connection.connection
let ffiAcceptConnected config cb =
  accept (FFI.sendTcpPacket cb) (FFI.recvTcpPacket cb) config


/// new QUIC-specific properties
///
let get_parameters c (r:role): ML (option TLSConstants.quicParameters) =
  let mode = Handshake.get_mode c.Connection.hs in
  if r = Client
  then Negotiation.find_quic_parameters mode.Negotiation.n_offer
  else Negotiation.find_server_quic_parameters mode

// extracting some QUIC parameters to C (a bit ad hoc)
val ffi_parameters: option TLSConstants.quicParameters -> ML (UInt32.t * UInt32.t * UInt32.t * UInt16.t * bytes)
let ffi_parameters qpo =
  match qpo with
  | None -> failwith "no parameters available"
  | Some (QuicParametersClient _ _ qp)
  | Some (QuicParametersServer _ qp) ->  (
      ( match (List.Tot.find Quic_initial_max_stream_data? qp) with
        | Some (Quic_initial_max_stream_data v) -> v
        | None -> failwith "no Quic_initial_max_stream_data"),
      ( match (List.Tot.find Quic_initial_max_data? qp) with
        | Some (Quic_initial_max_data v) -> v
        | None -> failwith "no Quic_initial_max_data"),
      ( match (List.Tot.find Quic_initial_max_stream_id? qp) with
        | Some (Quic_initial_max_stream_id v) -> v
        | None -> failwith "no Quic_initial_max_stream_id"),
      ( match (List.Tot.find Quic_idle_timeout? qp) with
        | Some (Quic_idle_timeout v) -> v
        | None -> failwith "no Quic_idle_timeout"),
      ( let nondefault = function
        | Quic_initial_max_stream_data _
        | Quic_initial_max_data _
        | Quic_initial_max_stream_id _
        | Quic_idle_timeout _ -> false
        | _ -> true in
      Extensions.quicParametersBytes_aux (List.Tot.filter nondefault qp)))

let get_peer_parameters c =
  let r = TLSConstants.dualRole (Connection.c_role c) in
  ffi_parameters (get_parameters c r)

let ffiConfig
  max_stream_data
  max_data
  max_stream_id
  idle_timeout
  (others: bytes)
  (versions: list UInt32.t)
  (host: string)  =
  let ver = List.Tot.map (fun (n:UInt32.t) ->
    match UInt32.v n with
    | 1 -> QuicVersion1
    | _ -> QuicCustomVersion n) versions in
  if length others > 0 then trace ("Other QUIC transport parameters: "^(hex_of_bytes others));
  let others =
    match Extensions.parseQuicParameters_aux others
    with
    | Error z -> trace "WARNING: ill-formed custom parameters "; []
    | Correct qpl -> qpl
    in
  { defaultConfig with
    min_version = TLS_1p3;
    max_version = TLS_1p3;
    peer_name = Some host;
    check_peer_certificate = false;
    non_blocking_read = true;
    quic_parameters = Some (ver, [
      Quic_initial_max_stream_data max_stream_data;
      Quic_initial_max_data max_data;
      Quic_initial_max_stream_id max_stream_id;
      Quic_idle_timeout idle_timeout] @ others)
  }
