module TLS.Handshake

open FStar.String
open FStar.Heap
open FStar.HyperStack
open FStar.Seq
open FStar.Error
open FStar.Bytes

open TLSError
open TLSInfo
open TLS.Callbacks
open TLSConstants
open Range
open Old.Epochs

module U32 = FStar.UInt32
module MS = FStar.Monotonic.Seq
module HS = FStar.HyperStack
module Nego = Negotiation
module HST = FStar.HyperStack.ST
module Epochs = Old.Epochs
module KeySchedule = Old.KeySchedule
module HMAC_UFCMA = Old.HMAC.UFCMA
module HSM = HandshakeMessages
module HSL = HandshakeLog
module CH = Parsers.ClientHello
module SH = Parsers.RealServerHello
module HRR = Parsers.HelloRetryRequest
module FSH = Parsers.ServerHello

// For readabililty, we try to open/abbreviate fewer modules

(* A flag for runtime debugging of Handshake data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("HS | "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_HS then print else (fun _ -> ())

// TODO : implement resumption
//val getCachedSession: cfg:config -> ch:ch -> ST (option session)
//  (requires (fun h -> True))
//  (ensures (fun h0 i h1 -> True))
//let getCachedSession cfg cg = None


// *** internal stuff: state machine, reader/writer counters, etc.


private
let finishedId = HMAC_UFCMA.finishedId

#set-options "--admit_smt_queries true"
type machineState =
  | C_init
  | C_wait_ServerHello
  | C13_wait_Finished1
  | C13_sent_EOED:
    digest ->
    option HSM.certificateRequest13 ->
    i:finishedId & cfk:KeySchedule.fink i -> machineState // TLS 1.3#20 aggravation
  | C_wait_NST of bool           // server must send NewSessionticket
  | C_wait_CCS of bool * digest  // TLS classic, resume & digest to be MACed by server
  | C_wait_R_Finished1 of digest // TLS resume, digest to be MACed by server
  | C_wait_ServerHelloDone     // TLS classic
  | C_wait_Finished2 of digest // TLS classic, digest to be MACed by server
  | C_Complete //19-06-07 to be split between 1.2 and 1.3

  | S_Idle //19-06-07 may disappear
  | S13_sent_ServerHello         // TLS 1.3, intermediate state to encryption
  | S13_wait_EOED                // TLS 1.3, sometimes waiting for EOED
  | S13_wait_Finished2 of digest // TLS 1.3, digest to be MACed by client
  | S_wait_CCS1                  // TLS classic
  | S_wait_Finished1 of digest // TLS classic, digest to the MACed by client
  | S_wait_CCS2 of digest      // TLS resume (CCS)
  | S_wait_CF2 of digest       // TLS resume (CF)
  | S_Complete

//17-03-24 consider using instead "if role = Client then clientState else serverServer"
//17-03-24 but that may break extraction to Kremlin and complicate typechecking
//17-03-24 we could also use two refinements.

// Removed error states, consider adding again to ensure the machine is stuck?

noeq type hs' = | HS:
  #region: rgn {is_hs_rgn region} ->
  r: role ->
  nego: Nego.t region r ->
  log: HandshakeLog.t {HandshakeLog.region_of log = region} ->
  ks: KeySchedule.ks (*region*) ->
  epochs: epochs region (Nego.nonce nego) ->
  state: ref machineState {HS.frameOf state = region} -> // state machine; should be opaque and depend on r.
  hs'

let hs = hs' //17-04-08 around .fsti limitation

let nonce (s:hs) = Nego.nonce s.nego
let region_of (s:hs) = s.region
let role_of (s:hs) = s.r
let random_of (s:hs) = nonce s
let config_of (s:hs) = Nego.local_config s.nego
let version_of (s:hs) = Nego.version s.nego
let get_mode (s:hs) = Nego.getMode s.nego
let is_server_hrr (s:hs) = Nego.is_server_hrr s.nego
let is_0rtt_offered (s:hs) =
  let mode = get_mode s in Nego.zeroRTToffer mode.Nego.n_offer
let is_post_handshake (s:hs) =
  match !s.state with | C_Complete | S_Complete -> true | _ -> false
let epochs_of (s:hs) = s.epochs

(* WIP on the handshake invariant
let inv (s:hs) (h:HS.mem) =
  // let context = Negotiation.context h hs.nego in
  let transcript = HandshakeLog.transcript h hs.log in
  match HS.sel h s.state with
  | C_wait_ServerHello ->
      hs.role = Client /\
      transcript = [clientHello hs.nonce offer] /\
      "nego in Wait_ServerHello" /\
      "ks in wait_ServerHello"
  | _ -> True
*)

// the states of the HS sub-module will be subject to a joint invariant
// for example the Nego state is a function of ours.


let stateType (s:hs) = seq (epoch s.region (nonce s)) * machineState
let stateT (s:hs) (h:HS.mem) : GTot (stateType s) = (logT s h, sel h s.state)

let forall_epochs (s:hs) h (p:(epoch s.region (nonce s) -> Type)) =
  (let es = logT s h in
   forall (i:nat{i < Seq.length es}).{:pattern (Seq.index es i)} p (Seq.index es i))
//epochs in h1 extends epochs in h0 by one

(*
#set-options "--admit_smt_queries true"
let fresh_epoch h0 s h1 =
  let es0 = logT s h0 in
  let es1 = logT s h1 in
  Seq.length es1 > 0 &&
  es0 = Seq.slice es1 0 (Seq.length es1 - 1)

(* vs modifies clauses? *)
(* let unmodified_epochs s h0 h1 =  *)
(*   forall_epochs s h0 (fun e ->  *)
(*     let rs = regions e in  *)
(*     (forall (r:rid{Set.mem r rs}).{:pattern (Set.mem r rs)} Map.sel h0 r = Map.sel h1 r)) *)
*)

let latest h (s:hs{Seq.length (logT s h) > 0}) = // accessing the latest epoch
  let es = logT s h in
  Seq.index es (Seq.length es - 1)

// separation policy: the handshake mutates its private state,
// only depends on it, and only extends the log with fresh epochs.

// placeholder, to be implemented as a stateful property.
let completed #rgn #nonce e = True

// consider adding an optional (resume: option sid) on the client side
// for now this bit is not explicitly authenticated.

// Well-formed logs are all prefixes of (Epoch; Complete)*; Error
// This crucially assumes that TLS keeps track of OutCCS and InCCSAck
// so that it knows which reader & writer to use (not always the latest ones):
// - within InCCSAck..OutCCS, we still use the older writer
// - within OutCCS..InCCSAck, we still use the older reader
// - otherwise we use the latest readers and writers

// abstract invariant; depending only on the HS state (not the epochs state)
// no need for an epoch states invariant here: the HS never modifies them

assume val hs_invT : s:hs -> epochs:seq (epoch s.region (nonce s)) -> machineState -> Type0

let hs_inv (s:hs) (h: HS.mem) = True
(* 17-04-08 TODO deal with inferred logic qualifiers
  hs_invT s (logT s h) (sel h (HS?.state s))  //An abstract invariant of HS-internal state
  /\ Epochs.containsT s.epochs h                //Nothing deep about these next two, since they can always
  /\ HS.contains s.state.ref ( h)                 //be recovered by 'recall'; carrying them in the invariant saves the trouble

//A framing lemma with a very trivial proof, because of the way stateT abstracts the state-dependent parts
*)

#set-options "--admit_smt_queries true"
let frame_iT_trivial  (s:hs) (rw:rw) (h0:HS.mem) (h1:HS.mem)
  : Lemma (stateT s h0 = stateT s h1  ==>  iT s rw h0 = iT s rw h1)
  = ()

//Here's a framing on stateT connecting it to the region discipline
let frame_stateT  (s:hs) (rw:rw) (h0:HS.mem) (h1:HS.mem) (mods:Set.set rid)
  : Lemma
    (requires
      HS.modifies mods ( h0) ( h1) /\
      HS.live_region h0 s.region /\
      not (Set.mem s.region mods))
    (ensures stateT s h0 = stateT s h1)
  = ()

//This is probably the framing lemma that a client of this module will want to use
let frame_iT  (s:hs) (rw:rw) (h0:HS.mem) (h1:HS.mem) (mods:Set.set rid)
  : Lemma
    (requires
      HS.modifies mods ( h0) ( h1) /\
      HS.live_region h0 s.region /\
      not (Set.mem s.region mods))
    (ensures stateT s h0 = stateT s h1 /\ iT s rw h0 = iT s rw h1)
=
  frame_stateT s rw h0 h1 mods;
  frame_iT_trivial s rw h0 h1



// factored out; indexing to be reviewed
val register: hs -> KeySchedule.recordInstance -> St unit
let register hs keys =
    let ep = //? we don't have a full index yet for the epoch; reuse the one for keys??
      let h = Nego.Fresh ({ Nego.session_nego = None }) in
      Epochs.recordInstanceToEpoch #hs.region #(nonce hs) h keys in // just coercion
      // New Handshake does
      // let KeySchedule.StAEInstance #id r w = keys in
      // Epochs.recordInstanceToEpoch #hs.region #(nonce hs) h (Handshake.Secret.StAEInstance #id r w) in
    Epochs.add_epoch hs.epochs ep // actually extending the epochs log

val export: hs -> KeySchedule.exportKey -> St unit
let export hs xk =
  trace "exporting a key";
  Monotonic.Seq.i_write_at_end hs.epochs.exporter xk

let xkeys_of hs = Monotonic.Seq.i_read hs.epochs.exporter

val map_ST2: 'c -> ('c -> 'a -> KeySchedule.ST0 'b) -> list 'a -> KeySchedule.ST0 (list 'b)
let rec map_ST2 env f x = match x with
  | [] -> []
  | a::tl -> f env a :: map_ST2 env f tl

let rec iutf8 (m:bytes) : St (s:string{String.length s < pow2 30 /\ utf8_encode s = m}) =
    match iutf8_opt m with
    | None -> trace ("Not a utf8 encoding of a string"); iutf8 m
    | Some s -> s

(* -------------------- Control Interface ---------------------- *)

let create (parent:rid) cfg role =
  let r = new_region parent in
  let log = HandshakeLog.create r None (* cfg.max_version (Nego.hashAlg nego) *) in
  //let nonce = Nonce.mkHelloRandom r r0 in //NS: should this really be Client?
  let ks, nonce = KeySchedule.create #r role cfg.is_quic in
  let nego = Nego.create r role cfg nonce in
  let epochs = Epochs.create r nonce in
  let state = ralloc r (if role = Client then C_init else S_Idle) in
  let x: hs = HS role nego log ks epochs state in //17-04-17 why needed?
  x

let rehandshake s c = FStar.Error.unexpected "rehandshake: not yet implemented"

let rekey s c = FStar.Error.unexpected "rekey: not yet implemented"

let send_ticket hs app_data =
  if is_post_handshake hs then
    let _ = server_Ticket hs app_data in true
  else false

let request s c = FStar.Error.unexpected "request: not yet implemented"

let invalidateSession hs = ()
// ADL: disabling this for top-level API testing purposes
// FStar.Error.unexpected "invalidateSession: not yet implemented"


(* ------------------ Outgoing -----------------------*)

let next_fragment_bounded (hs:hs) i (max:nat) =
    trace "next_fragment";
    let outgoing = HSL.write_at_most hs.log i max in
    match outgoing, !hs.state with
    // when the output buffer is empty, we send extra messages in two cases
    // we prepare the initial ClientHello; or
    // after sending ServerHello in plaintext, we continue with encrypted traffic
    // otherwise, we just returns buffered messages and signals
    | HSL.Outgoing None None false, C_init ->
      (match client_ClientHello hs i with
      | Error z -> Error z
      | Correct () -> Correct(HSL.write_at_most hs.log i max))
    | HSL.Outgoing None None false, S13_sent_ServerHello ->
      (match server_ServerFinished_13 hs i with
      | Error z -> Error z
      | Correct () -> Correct(HSL.write_at_most hs.log i max))
    | HSL.Outgoing None None false, C13_sent_EOED d ocr cfk ->
      client_ClientFinished_13 hs d ocr cfk;
      Correct(HSL.write_at_most hs.log i max)
    | _ -> Correct outgoing // nothing to do

let next_fragment (hs:hs) i =
  next_fragment_bounded hs i max_TLSPlaintext_fragment_length

let to_be_written (hs:hs) =
  HSL.to_be_written hs.log

(* ----------------------- Incoming ----------------------- *)

let rec recv_fragment (hs:hs) #i rg f =
  let open HandshakeLog in
  let open HandshakeMessages in
  let recv_again r =
    match r with
    // only case where the next incoming flight may already have been buffered.
    | InAck false false -> recv_fragment hs #i (0,0) empty_bytes
    | r -> r  in
  trace "recv_fragment";
  let h0 = HST.get() in
  let flight = receive hs.log f in
  match flight with
  | Error z -> InError z
  | Correct None -> InAck false false // nothing happened
  | Correct (Some (ms,ts)) ->
    match !hs.state, ms, ts with

    (* CLIENT *)

    | C_init, _, _ -> InError (fatalAlert Unexpected_message, "Client hasn't sent hello yet")
    | C_wait_ServerHello, [Msg (M_server_hello sh)], [] ->
      if HSM.is_hrr sh then
        client_HelloRetryRequest hs (HSM.get_hrr sh)
      else
        recv_again (client_ServerHello hs (HSM.get_sh sh))

    // 1.2 full: wrap these two into a single received flight with optional [cr]
    | C_wait_ServerHelloDone, [Msg12 (M12_certificate c); Msg12 (M12_server_key_exchange ske); Msg12 (M12_server_hello_done ())], [_] ->
      client_ServerHelloDone hs c ske None

    | C_wait_ServerHelloDone, [Msg12 (M12_certificate c); Msg12 (M12_server_key_exchange ske); Msg12 (M12_certificate_request cr); Msg12 (M12_server_hello_done ())], [_] ->
      client_ServerHelloDone hs c ske (Some cr)

    | C_wait_Finished2 digestClientFinished, [Msg12 (M12_finished f)], [digestServerFinished] ->
      client_ServerFinished hs f digestClientFinished

    | C_wait_NST resume, [Msg12 (M12_new_session_ticket st)], [digestNewSessionTicket] ->
      client_NewSessionTicket_12 hs resume digestNewSessionTicket st

    // 1.3; wrap these three into single flight with optional cr and optional (c;cv).
    | C13_wait_Finished1, [Msg13 (M13_encrypted_extensions ee); Msg13 (M13_certificate c); Msg13 (M13_certificate_verify cv); Msg13 (M13_finished f)],
      [_; digestCert; digestCertVerify; digestServerFinished] ->
      client_ServerFinished_13 hs ee None (Some c) (Some cv) f
                               (Some digestCert) digestCertVerify digestServerFinished

    | C13_wait_Finished1, [Msg13 (M13_encrypted_extensions ee); Msg13 (M13_certificate_request cr); Msg13 (M13_certificate c); Msg13 (M13_certificate_verify cv); Msg13 (M13_finished f)],
      [_; digestCert; digestCertVerify; digestServerFinished] ->
      client_ServerFinished_13 hs ee (Some cr) (Some c) (Some cv) f
                               (Some digestCert) digestCertVerify digestServerFinished

    | C13_wait_Finished1, [Msg13 (M13_encrypted_extensions ee); Msg13 (M13_finished f)],
                        [digestEE; digestServerFinished] ->
      client_ServerFinished_13 hs ee None None None f None digestEE digestServerFinished

    | C_Complete, [Msg13 (M13_new_session_ticket st13)], [_] ->
      client_NewSessionTicket_13 hs st13

    // 1.2 resumption
    | C_wait_R_Finished1 digestNewSessionTicket, [Msg12 (M12_finished f)], [digestServerFinished] ->
      client_R_ServerFinished hs f digestNewSessionTicket digestServerFinished

    (* SERVER *)
    | S_Idle, [Msg (M_client_hello ch)], []  -> server_ClientHello hs ch

    // 1.2 full
    | S_wait_Finished1 digest, [Msg12 (M12_finished f)], [digestClientFinish] ->
      server_ClientFinished hs f digest digestClientFinish

    // 1.2 resumption
    | S_wait_CF2 digest, [Msg12 (M12_finished f)], [digestClientFinished] -> // classic resumption
      server_ClientFinished2 hs f digest digestClientFinished

    // 1.3, similarly group cases with optional ((c,cv)?
    | S13_wait_EOED, [Msg13 (M13_end_of_early_data ())], [digestEOED] ->
      server_EOED hs digestEOED

    | S13_wait_Finished2 digestServerFinished,
      [Msg13 (M13_finished f)], [digestClientFinished] ->
      server_ClientFinished_13 hs f digestServerFinished digestClientFinished None

    | S13_wait_Finished2 digestServerFinished,
      [Msg13 (M13_certificate c); Msg13 (M13_certificate_verify cv); Msg13 (M13_finished f)], [digestSigned; digestCertVerify; digestClientFinished] ->
      server_ClientFinished_13 hs f digestCertVerify digestClientFinished (Some (c, cv, digestSigned))

    // are we missing the case with a Certificate but no CertificateVerify?
    | _,  _, _ ->
//      trace "DISCARD FLIGHT"; InAck false false
      InError(fatalAlert Unexpected_message, "unexpected flight")

// TODO check CCS once committed to TLS 1.3 yields an alert
let recv_ccs (hs:hs) =
  let open HandshakeLog in
  let open HandshakeMessages in
  trace "recv_ccs";
  // Draft 22 CCS during HRR
  // Because of stateless HRR, this may also happen as the very first message before CH (!!!)
  let is_hrr = Nego.is_hrr hs.nego in
  let is_idle = S_Idle? !hs.state in
  if is_hrr || is_idle then
    begin
    trace "IGNORING CCS (workaround for implementations that send CCS after HRR)";
    InAck false false
    end
  else
    // CCS triggers completion of the incoming flight of messages.
    let mode = Nego.getMode hs.nego in
    match receive_CCS #(Nego.hashAlg mode) hs.log with
    | Error z -> InError z
    | Correct (ms, digests, digestCCS) ->
      match !hs.state, ms, digests with
      // client full handshake
      | C_wait_CCS (resume, digest), [], [] ->
        Epochs.incr_reader hs.epochs;
        hs.state := (if resume then C_wait_R_Finished1 digest else C_wait_Finished2 digest);
        InAck true false

      | S_wait_CCS2 digestServerFinished, [], [] -> (
        Epochs.incr_reader hs.epochs;
        hs.state := S_wait_CF2 digestServerFinished;
        InAck true false)

      | S_wait_CCS1, [Msg12 (M12_client_key_exchange cke)], [digest_to_finish] ->
        // assert (Some? pv && pv <> Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE))
        // getting two copies of the same digest?
        server_ClientCCS1 hs cke digestCCS

      | _, _, _ ->
        trace "WARNING: bad CCS";
        InError(fatalAlert Unexpected_message, "CCS received at wrong time")


let authorize s ch = FStar.Error.unexpected "authorize: not yet implemented"
