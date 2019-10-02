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

module Send = TLS.Handshake.Send 
module Receive = TLS.Handshake.Receive
module Machine = TLS.Handshake.Machine 

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
  let open TLSError in 
  trace ("returning error"^
    (match description with
    | Some ad -> " "^string_of_alert ad
    | None    -> "")^": "^txt);
  let a = match description with | Some a -> a | None -> fatalAlert Internal_error in
  Parse.uint16_of_bytes (Alert.alertBytes a)

module Handshake = TLS.Handshake

let quic_check config =
  if config.min_version <> TLS_1p3 then trace "WARNING: not TLS 1.3";
  if not config.non_blocking_read then trace "WARNING: reads are blocking";
  if None? config.alpn            then trace "WARNING: missing ALPN";
  if not config.is_quic           then trace "WARNING: missing QUIC config, using TLS key labels"

let ffiConfig (host:bytes) =
  let h = if length host = 0 then None else Some host in
  { defaultConfig with
    min_version = TLS_1p3;
    max_version = TLS_1p3;
    is_quic = true;
    peer_name = h;
    non_blocking_read = true;
    send_ticket = None;
  }

type chSummary = {
  ch_sni: bytes;
  ch_alpn: bytes;
  ch_extensions: bytes;
  ch_cookie: option bytes;
  ch_ticket_data: option bytes;
}

let rec find_ticket_content (l:Extensions.offeredPsks_identities)
  : St (option bytes) =
  match l with
  | [] -> None
  | id::t ->
    match Ticket.check_ticket false id.Extensions.identity with
    | Some (Ticket.Ticket13 _ _ _ _ _ _ _ app_data) -> Some app_data
    | _ -> find_ticket_content t

module HSM = HandshakeMessages
module CH = Parsers.ClientHello
module CK = TLS.Cookie

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
    match HSM.handshake_parser32 ch with
    | None -> trace ("peekClientHello: bad handshake header"); None
    | Some (HSM.M_client_hello ch, _) ->
      let sni = Negotiation.get_sni ch in
        let alpn = Extensions.protocolNameList_serializer32 (Negotiation.get_alpn ch) in
        let ext = Extensions.clientHelloExtensions_serializer32 ch.CH.extensions in
	let ticket_data =
	  match Negotiation.find_clientPske ch with
	  | None -> None
	  | Some psk -> find_ticket_content psk.Extensions.identities in
        let cookie =
           match Negotiation.find_cookie ch with
           | None -> None
           | Some c ->
             match CK.decrypt c with
             | Error z -> None
             | Correct (_, extra, _) -> Some extra
          in
        Some ({ch_sni = sni; ch_alpn = alpn; ch_extensions = ext; ch_cookie = cookie; ch_ticket_data = ticket_data })
    | _ -> trace ("peekClientHello: not a client hello!"); None

module H = TLS.Handshake
module HM = TLS.Handshake.Machine

let create_hs (is_server:bool) config : ML Machine.state =
  quic_check config;
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
  is_writable: bool;
  is_early_rejected: bool;
  is_post_handshake: bool;
}

type hs_result =
  | HS_SUCCESS of hs_out
  | HS_ERROR of UInt16.t

private let currentId (hs:Machine.state) (rw:rw) : St TLSInfo.id =
  let n = Machine.nonce hs in
  let j = H.i hs rw in
  if j<0 then PlaintextID n
  else
    let e = Old.Epochs.get_current_epoch (Machine.epochs hs n) rw in
    Old.Epochs.epoch_id e

let get_epochs (hs:Machine.state) : ML (int * int) =
  H.i hs Reader, H.i hs Writer

private let handle_signals (hs:Machine.state) (sig:option Send.next_keys_use) : ML bool =
  match sig with
  | None -> false
  | Some use ->
    let n = Machine.nonce hs in
    let epochs = Machine.epochs hs n in
    Old.Epochs.incr_writer epochs;
    if use.Send.out_skip_0RTT then
     begin
      trace "Skip 0-RTT (incr writer)";
      Old.Epochs.incr_writer epochs
     end;
    use.Send.out_appdata

private inline_for_extraction let api_error (ad, err) =
  trace ("Returning HS error: "^err);
  HS_ERROR (Parse.uint16_of_bytes (Alert.alertBytes ad))

let process_hs (hs:Machine.state) (ctx:hs_in) : ML hs_result =
  let tbw = H.to_be_written hs in
  if tbw > 0 then
   begin
    if ctx.max_output = 0ul then
      HS_SUCCESS ({
        consumed = 0ul;
        output = empty_bytes;
        to_be_written = UInt32.uint_to_t tbw;
        is_complete = false;
        is_writable = false;
	is_early_rejected = false;
	is_post_handshake = false;
      })
    else
      let i = currentId hs Writer in
      match H.next_fragment_bounded hs i (UInt32.v ctx.max_output) with
      | Error z -> api_error z
      | Correct (Send.Outgoing (Some frag) sig complete) ->
        let is_writable = handle_signals hs sig in
        HS_SUCCESS ({
	  consumed = 0ul;
	  output = dsnd frag;
	  to_be_written = UInt32.uint_to_t (H.to_be_written hs);
	  is_complete = complete;
	  is_writable = is_writable;
	  is_early_rejected = false;
	  is_post_handshake = false;
	})
   end
  else
    let i = currentId hs Reader in
    let len = length ctx.input in
    let rg : Range.frange i = (len, len) in
    let f : Range.rbytes rg = ctx.input in
    match H.recv_fragment hs rg f with
    | Receive.InQuery _ _ -> trace "Unexpected handshake query"; HS_ERROR 252us
    | Receive.InError z -> api_error z
    | Receive.InAck nk complete ->
      let consumed = UInt32.uint_to_t len in
      let j = H.i hs Writer in

      //19-09-14 TODO recheck semantics 
      let post_hs =
        match hs with
	| HM.Client _ _ r -> HM.C13_complete? !r
	| HM.Server _ _ r -> HM.S13_complete? !r
	| _ -> false in
      let reject_0rtt = 
        if HM.Client? hs && j = 2 then // FIXME: early reject vs. late reject
	  TLS.Handshake.Client.early_rejected hs 
	else false in
      let i = currentId hs Writer in
      let max_o = UInt32.v ctx.max_output in
      match H.next_fragment_bounded hs i max_o with
      | Error z -> api_error z
      | Correct (Send.Outgoing frag sig complete' ) ->
        let is_writable = handle_signals hs sig in
        HS_SUCCESS ({
          consumed = consumed;
          output = (match frag with Some f -> dsnd f | None -> empty_bytes);
          to_be_written = UInt32.uint_to_t (H.to_be_written hs);
          is_complete = complete || complete';
	  is_writable = is_writable;
	  is_early_rejected = reject_0rtt;
	  is_post_handshake = post_hs;
        })

type raw_key = {
  alg: aeadAlg;
  aead_key: bytes;
  aead_iv: bytes;
  pn_key: bytes;
}

let get_key (hs:HM.state) (ectr:nat) (rw:bool) : ML (option raw_key) =
  let n = HM.nonce hs in
  let epochs = Monotonic.Seq.i_read
    (Old.Epochs.get_epochs (HM.epochs hs n)) in
  if Seq.length epochs <= ectr then None
  else
    let e = Seq.index epochs ectr in
    let AEAD alg _ = aeAlg_of_id (Old.Epochs.epoch_id e) in
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
    
let send_ticket (hs:HM.state) (b:bytes) : ML bool =
  TLS.Handshake.send_ticket hs b
