module TLS.Handshake.State

open TLSConstants
open TLSInfo
open TLSError
open Mem
open FStar.HyperStack.ST

module Epochs = Old.Epochs
module H = Hashing.Spec
module HMAC = Old.HMAC.UFCMA
module HS = FStar.HyperStack
module HSL = HandshakeLog
module HSM = HandshakeMessages
module KS = Old.KeySchedule
module MS = FStar.Monotonic.Seq
module Nego = Negotiation
module S = FStar.Seq

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

#set-options "--admit_smt_queries true"
type machineState =
  | C_init
  | C_wait_ServerHello
  | C13_sent_CH2: // Replaces the C_HRR state in Nego
    ch1: Nego.offer ->
    hrr: HSM.hrr -> //Nego.retryInfo ch1 ->
    machineState
  | C13_wait_Finished1
  | C13_sent_EOED: H.anyTag ->
    option HSM.certificateRequest13 ->
    i:HMAC.finishedId & cfk:KS.fink i ->
    machineState // TLS 1.3#20 aggravation
  | C_wait_NST of bool           // server must send NewSessionticket
  | C_wait_CCS of bool * H.anyTag  // TLS classic, resume & digest to be MACed by server
  | C_wait_R_Finished1 of H.anyTag // TLS resume, digest to be MACed by server
  | C_wait_ServerHelloDone     // TLS classic
  | C_wait_Finished2 of H.anyTag // TLS classic, digest to be MACed by server
  | C_Complete //19-06-07 to be split between 1.2 and 1.3

  | S_Idle //19-06-07 may disappear
  | S13_wait_CH2:                // TLS 1.3, sent a retry request
    ch1: Nego.offer ->
    hrr: HSM.hrr ->
    machineState
  | S13_sent_ServerHello         // TLS 1.3, intermediate state to encryption
  | S13_wait_EOED                // TLS 1.3, sometimes waiting for EOED
  | S13_wait_Finished2 of H.anyTag // TLS 1.3, digest to be MACed by client
  | S_wait_CCS1                  // TLS classic
  | S_wait_Finished1 of H.anyTag // TLS classic, digest to the MACed by client
  | S_wait_CCS2 of H.anyTag      // TLS resume (CCS)
  | S_wait_CF2 of H.anyTag       // TLS resume (CF)
  | S_Complete

//17-03-24 consider using instead "if role = Client then clientState else serverServer"
//17-03-24 but that may break extraction to Karamel and complicate typechecking
//17-03-24 we could also use two refinements.

// Removed error states, consider adding again to ensure the machine is stuck?

noeq type hs =
| HS:
  #region: rgn {is_hs_rgn region} ->
  r: role ->
  nego: Nego.t region r ->
  log: HSL.t {HSL.region_of log = region} ->
  ks: KS.ks (*region*) ->
  epochs: Epochs.epochs region (Nego.nonce nego) ->
  state: ref machineState {HS.frameOf state = region} -> // state machine; should be opaque and depend on r.
  hs

let nonce (s:hs) = Nego.nonce s.nego
let region_of (s:hs) = s.region
let role_of (s:hs) = s.r
let random_of (s:hs) = nonce s
let config_of (s:hs) = Nego.local_config s.nego
let version_of (s:hs) = Nego.version s.nego
let get_mode (s:hs) = Nego.getMode s.nego
let is_0rtt_offered (s:hs) =
  let mode = get_mode s in Nego.zeroRTToffer mode.Nego.n_offer
let is_post_handshake (s:hs) =
  match !s.state with | C_Complete | S_Complete -> true | _ -> false
let epochs_of (s:hs) = s.epochs

let epochs_t_of (s:hs) = Seq.seq (Epochs.epoch (region_of s) (random_of s))
let logT (s:hs) (h:HS.mem) = Epochs.epochsT (epochs_of s) h
let stateType (s:hs) = S.seq (Epochs.epoch s.region (nonce s)) * machineState
let stateT (s:hs) (h:HS.mem) : GTot (stateType s) = (logT s h, sel h s.state)

let forall_epochs (s:hs) h (p:(Epochs.epoch s.region (nonce s) -> Type)) =
  (let es = logT s h in
   forall (i:nat{i < Seq.length es}).{:pattern (Seq.index es i)} p (Seq.index es i))

let latest h (s:hs{Seq.length (logT s h) > 0}) = // accessing the latest epoch
  let es = logT s h in
  Seq.index es (Seq.length es - 1)

assume val hs_invT:
  s:hs ->
  epochs: S.seq (Epochs.epoch s.region (nonce s)) ->
  machineState ->
  Type0

let hs_inv (s:hs) (h: HS.mem) = True
(* 17-04-08 TODO deal with inferred logic qualifiers
  hs_invT s (logT s h) (sel h (HS?.state s))  //An abstract invariant of HS-internal state
  /\ Epochs.containsT s.epochs h                //Nothing deep about these next two, since they can always
  /\ HS.contains s.state.ref ( h)                 //be recovered by 'recall'; carrying them in the invariant saves the trouble

//A framing lemma with a very trivial proof, because of the way stateT abstracts the state-dependent parts
*)

let non_empty h s = Seq.length (logT s h) > 0
let logIndex (#t:Type) (log: Seq.seq t) = n:int { -1 <= n /\ n < Seq.length log }
let es_of (s:hs) = Epochs.((epochs_of s).es)

// returns the current counters, with a precise refinement
let iT (s:hs) rw (h:HS.mem): GTot (Epochs.epoch_ctr_inv (region_of s) (es_of s)) =
  match rw with
  | Reader -> Epochs.readerT (epochs_of s) h
  | Writer -> Epochs.writerT (epochs_of s) h

// this function increases (how to specify it once for all?)
let i (s:hs) (rw:rw) : ST int
  (requires (fun h -> True))
  (ensures (fun h0 i h1 ->
    h0 == h1 /\
    i = iT s rw h1 /\
    Epochs.get_ctr_post (epochs_of s) rw h0 i h1))
  =
  assume false;
  match rw with
  | Reader -> Epochs.get_reader (epochs_of s)
  | Writer -> Epochs.get_writer (epochs_of s)

// returns the current epoch for reading or writing
let eT s rw (h:HS.mem {iT s rw h >= 0}) =
  let es = logT s h in
  let j = iT s rw h in
  assume(j < Seq.length es); //17-04-08 added verification hint; assumed for now.
  Seq.index es j
  
let readerT s h = eT s Reader h
let writerT s h = eT s Writer h

// factored out; indexing to be reviewed
val register: hs -> KS.recordInstance -> St unit
let register hs keys =
    let ep = //? we don't have a full index yet for the epoch; reuse the one for keys??
      let h = Nego.Fresh ({ Nego.session_nego = None }) in
      Epochs.recordInstanceToEpoch #hs.region #(nonce hs) h keys in // just coercion
      // New Handshake does
      // let KeySchedule.StAEInstance #id r w = keys in
      // Epochs.recordInstanceToEpoch #hs.region #(nonce hs) h (Handshake.Secret.StAEInstance #id r w) in
    Epochs.add_epoch hs.epochs ep // actually extending the epochs log

val export: hs -> KS.exportKey -> St unit
let export hs xk =
  trace "exporting a key";
  MS.i_write_at_end hs.epochs.Epochs.exporter xk

// returns the current exporter keys
val xkeys_of: s:hs -> ST (Seq.seq KS.exportKey)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> h0 == h1 /\ Seq.length r <= 2)
let xkeys_of hs = MS.i_read hs.epochs.Epochs.exporter

type incoming =
  | InAck: // the fragment is accepted, and...
      next_keys : bool -> // the reader index increases;
      complete  : bool -> // the handshake is complete!
      incoming
  | InQuery: Cert.chain -> bool -> incoming // could be part of InAck if no explicit user auth
  | InError: TLSError.error -> incoming // how underspecified should it be?

let in_next_keys (r:incoming) = InAck? r && InAck?.next_keys r
let in_complete (r:incoming)  = InAck? r && InAck?.complete r
