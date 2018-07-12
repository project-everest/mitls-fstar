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

open FStar.Bytes
open FStar.Error
open FStar.HyperStack.All

open TLSConstants
open TLSInfo
open DataStream
open TLS
open FFICallbacks

module HS = FStar.HyperStack
module FFI = FFI
module Range = Range
open Range

#set-options "--admit_smt_queries true"

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
unfold let trace = if DebugFlags.debug_QUIC then print else (fun _ -> ())


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

  // The server has sent a hello retry request.
  // This message must be sent in a special QUIC packet
  | TLS_server_stateless_retry

type result = {
  code: resultcode;
  error: error; // we could keep more details
}

module Handshake = Old.Handshake

val recv: Connection.connection -> St result
let rec recv c =
  let i = currentId c Reader in
  match read c i with
  | Update false     -> recv c // do not report intermediate, internal key changes
  | ReadWouldBlock   ->
      if Handshake.is_server_hrr c.Connection.hs
      then {code=TLS_server_stateless_retry; error=0us;}
      else {code=TLS_would_block; error=0us;}
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
  if None? config.alpn            then trace "WARNING: missing ALPN"

/// New client and server connections (without any  I/O yet)
/// [send] and [recv] are callbacks to operate on QUIC stream0 buffers
/// [config] is a client configuration for QUIC (see above)
/// [psks] is a list of proposed pre-shared-key identifiers and tickets
let connect ctx send recv config : ML Connection.connection =
  // we assume the configuration specifies the target SNI;
  // otherwise we must check the authenticated certificate chain.
  let tcp = Transport.callbacks ctx send recv in
  let here = new_region HS.root in
  quic_check config;
  TLS.connect here tcp config

/// [send] and [recv] are callbacks to operate on QUIC stream0 buffers
/// [config] is a server configuration for QUIC (see above)
/// tickets are managed internally
let accept ctx send recv config : ML Connection.connection =
  let tcp = Transport.callbacks ctx send recv in
  let here = new_region HS.root in
  quic_check config;
  TLS.accept_connected here tcp config

// Ticket also includes the serialized session,
// if it is not in the PSK database it will be installed
// (allowing resumption across miTLS client processes)
val ffiConnect:
  Transport.pvoid -> Transport.pfn_send -> Transport.pfn_recv ->
  config:config -> ML Connection.connection
let ffiConnect ctx snd rcv config = connect ctx snd rcv config

val ffiAcceptConnected:
  Transport.pvoid -> Transport.pfn_send -> Transport.pfn_recv ->
  config:config -> ML Connection.connection
let ffiAcceptConnected ctx snd rcv config = accept ctx snd rcv config

let ffiConfig (host:bytes) =
  let h = if length host = 0 then None else Some host in
  { defaultConfig with
    min_version = TLS_1p3;
    max_version = TLS_1p3;
    peer_name = h;
    non_blocking_read = true
  }

type chSummary = {
  ch_sni: bytes;
  ch_alpn: bytes;
  ch_extensions: bytes;
  ch_cookie: option bytes;
}

let peekClientHello (ch:bytes) (has_record:bool) : ML (option chSummary) =
  if length ch < 40 then (trace "peekClientHello: too short"; None) else
  let ch =
    if has_record then
      let hdr, ch = split ch 5ul in
      match Record.parseHeader hdr with
      | Error (_, msg) -> trace ("peekClientHello: bad record header"); None
      | Correct(ct, pv, len) ->
        if ct <> Content.Handshake || len <> length ch then
          (trace "peekClientHello: bad CT or length"; None)
        else Some ch
    else Some ch
    in
  match ch with
  | None -> None
  | Some ch ->
    match HandshakeMessages.parseMessage ch with
    | Error _
    | Correct None -> trace ("peekClientHello: bad handshake header"); None
    | Correct (Some (| _, hst, ch, _ |)) ->
      if hst <> HandshakeMessages.HT_client_hello then
         (trace "peekClientHello: not a client hello"; None)
      else
        match HandshakeMessages.parseClientHello ch with
        | Error (_, msg) -> trace ("peekClientHello: bad client hello: "^msg); None
        | Correct (ch, _) ->
          let sni = Negotiation.get_sni ch in
          let alpn = Extensions.alpnBytes (Negotiation.get_alpn ch) in
          let ext = HandshakeMessages.optionExtensionsBytes ch.HandshakeMessages.ch_extensions in
          let cookie =
            match Negotiation.find_cookie ch with
            | None -> None
            | Some c ->
              match Ticket.check_cookie c with
              | None -> None
              | Some (hrr, digest, extra) -> Some extra
            in
          Some ({ch_sni = sni; ch_alpn = alpn; ch_extensions = ext; ch_cookie = cookie; })

// QUIC interface to TLS handshake

module H = Old.Handshake
module HSL = HandshakeLog

let create_hs (is_server:bool) config : ML H.hs =
  let r = new_region HS.root in
  let role = if is_server then Server else Client in
  H.create r config role

type hs_in = {
  input: bytes;
  max_output: UInt32.t;
}

type hs_out = {
  consumed: UInt32.t;
  output: bytes;
  to_be_written: UInt32.t;
  is_complete: bool;
}

type hs_result =
  | HS_SUCCESS of hs_out
  | HS_ERROR of UInt16.t

private let currentId (hs:H.hs) (rw:rw) : St TLSInfo.id =
  let j = H.i hs rw in
  if j<0 then PlaintextID (H.nonce hs)
  else
    let e = Old.Epochs.get_current_epoch (H.epochs_of hs) rw in
    Old.Epochs.epoch_id e

let get_epochs (hs:H.hs) : ML (int * int) =
  H.i hs Reader, H.i hs Writer

private let handle_signals (hs:H.hs) (sig:option HSL.next_keys_use) : ML unit =
  match sig with
  | None -> ()
  | Some use ->
    Old.Epochs.incr_writer (H.epochs_of hs)
//    if use.HSL.out_skip_0RTT then
//      Old.Epochs.incr_writer (H.epochs_of hs)

let process_hs (hs:H.hs) (ctx:hs_in) : ML hs_result =
  let tbw = H.to_be_written hs in
  if tbw > 0 then
   begin
    if ctx.max_output = 0ul then
      HS_SUCCESS ({
        consumed = 0ul;
        output = empty_bytes;
	to_be_written = UInt32.uint_to_t tbw;
	is_complete = false;
      })
    else
      let i = currentId hs Writer in
      match H.next_fragment_bounded hs i (UInt32.v ctx.max_output) with
      | Error (z) -> HS_ERROR 1us
      | Correct (HSL.Outgoing (Some frag) sig _) ->
        handle_signals hs sig;
        HS_SUCCESS ({
	  consumed = 0ul;
	  output = dsnd frag;
	  to_be_written = UInt32.uint_to_t (H.to_be_written hs);
	  is_complete = false;
	})
   end
  else
    let i = currentId hs Reader in
    let len = length ctx.input in
    let rg : Range.frange i = (len, len) in
    let f : Range.rbytes rg = ctx.input in
    match H.recv_fragment hs rg f with
    | H.InQuery _ _ -> HS_ERROR 2us
    | H.InError z -> HS_ERROR 3us
    | H.InAck nk complete ->
      let consumed = UInt32.uint_to_t len in
      let i = currentId hs Writer in
      match H.next_fragment_bounded hs i (UInt32.v ctx.max_output) with
      | Error z -> HS_ERROR 4us
      | Correct (HSL.Outgoing frag sig _ ) ->
        handle_signals hs sig;
	HS_SUCCESS ({
          consumed = consumed;
          output = (match frag with Some f -> dsnd f | None -> empty_bytes);
          to_be_written = UInt32.uint_to_t (H.to_be_written hs);
          is_complete = complete;
        })

type raw_key = {
  alg: aeadAlg;
  aead_key: bytes;
  aead_iv: bytes;
  pn_key: bytes;
}

let get_key (hs:Old.Handshake.hs) (ectr:nat) (rw:bool) : ML (option raw_key) =
  let epochs = Monotonic.Seq.i_read (Old.Epochs.get_epochs (Handshake.epochs_of hs)) in
  if Seq.length epochs <= ectr then None
  else
    let AEAD alg _ = aeAlg_of_id (currentId hs (if rw then Reader else Writer)) in
    let e = Seq.index epochs ectr in
    let (key, iv), pn =
      let (rpn, wpn) = Old.Epochs.pn_epoch e in
      if rw then
        let StAE.Stream _ st = Old.Epochs.reader_epoch e in
        let st = StreamAE.State?.aead st in
        AEADProvider.leak st, Some?.v rpn
      else
        let StAE.Stream _ st = Old.Epochs.writer_epoch e in
        let st = StreamAE.State?.aead st in
        AEADProvider.leak st, Some?.v wpn
    in
    Some ({
      alg = alg;
      aead_key = key;
      aead_iv = iv;
      pn_key = pn;
    })
    
