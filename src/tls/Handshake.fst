(*--build-config
options:--fstar_home ../../../FStar --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection --use_hints --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../hacl-star/secure_api/LowCProvider/fst --include ../../../kremlin/kremlib --include ../../../hacl-star/specs --include ../../../hacl-star/code/lib/kremlin --include ../../../hacl-star/code/bignum --include ../../../hacl-star/code/experimental/aesgcm --include ../../../hacl-star/code/poly1305 --include ../../../hacl-star/code/salsa-family --include ../../../hacl-star/secure_api/test --include ../../../hacl-star/secure_api/utils --include ../../../hacl-star/secure_api/vale --include ../../../hacl-star/secure_api/uf1cma --include ../../../hacl-star/secure_api/prf --include ../../../hacl-star/secure_api/aead --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ../../src/tls/ideal-flags;
--*)
module Handshake

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.Set
open Platform.Error
open Platform.Bytes
open TLSError
open TLSInfo
open TLSConstants
open Range
open HandshakeMessages // for the message syntax
open HandshakeLog // for Outgoing
open Epochs

module HH = FStar.HyperHeap
module MR = FStar.Monotonic.RRef
module MS = FStar.Monotonic.Seq
module Nego = Negotiation
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
unfold let trace = if Flags.debug_HS then print else (fun _ -> ())


// TODO : implement resumption
//val getCachedSession: cfg:config -> ch:ch -> ST (option session)
//  (requires (fun h -> True))
//  (ensures (fun h0 i h1 -> True))
//let getCachedSession cfg cg = None


// *** internal stuff: state machine, reader/writer counters, etc.

// some states keep digests (irrespective of their hash algorithm)
type digest = l:bytes{length l <= 32}

type machineState =
  | C_Idle
  | C_Wait_ServerHello
  | C_Wait_Finished1           // TLS 1.3
  | C_Sent_EOED: digest -> option HandshakeMessages.cr13 -> (i:finishedId & cfk:KeySchedule.fink i) -> machineState // TLS 1.3#20 aggravation
//| C_Wait_CCS1 of digest      // TLS resume, digest to be MACed by server
//| C_Wait_Finished1 of digest // TLS resume, digest to be MACed by server
  | C_Wait_ServerHelloDone     // TLS classic
  | C_Wait_CCS2 of digest      // TLS classic, digest to be MACed by server
  | C_Wait_Finished2 of digest // TLS classic, digest to be MACed by server
  | C_Complete

  | S_Idle
  | S_Sent_ServerHello         // TLS 1.3, intermediate state to encryption
  | S_Wait_Finished2 of bool * digest // TLS 1.3, EOED flag x digest to be MACed by client
  | S_Wait_CCS1                   // TLS classic
  | S_Wait_Finished1 of digest // TLS classic, digest to the MACed by client
//| S_Wait_CCS2 of digest      // TLS resume, digest to be MACed by client
//| S_Wait_Finished2 of digest // TLS resume, digest to be MACed by client
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
  state: ref machineState {state.HyperStack.id = region} -> // state machine; should be opaque and depend on r.
  hs'

let hs = hs' //17-04-08 interface limitation

let nonce (s:hs) = Nego.nonce s.nego
let region_of (s:hs) = s.region
let role_of (s:hs) = s.r
let random_of (s:hs) = nonce s
let config_of (s:hs) = Nego.local_config s.nego
let version_of (s:hs) = Nego.version s.nego
let resumeInfo_of (s:hs) = Nego.resume s.nego
let get_mode (s:hs) = Nego.getMode s.nego
let epochs_of (s:hs) = s.epochs

(* WIP on the handshake invariant
let inv (s:hs) (h:HyperStack.mem) =
  // let context = Negotiation.context h hs.nego in
  let transcript = HandshakeLog.transcript h hs.log in
  match HyperStack.sel h s.state with
  | C_Wait_ServerHello ->
      hs.role = Client /\
      transcript = [clientHello hs.nonce offer] /\
      "nego in Wait_ServerHello" /\
      "ks in wait_ServerHello"
  | _ -> True
*)

// the states of the HS sub-module will be subject to a joint invariant
// for example the Nego state is a function of ours.


let stateType (s:hs) = seq (epoch s.region (nonce s)) * machineState
let stateT (s:hs) (h:HyperStack.mem) : GTot (stateType s) = (logT s h, sel h s.state)

let forall_epochs (s:hs) h (p:(epoch s.region (nonce s) -> Type)) =
  (let es = logT s h in
   forall (i:nat{i < Seq.length es}).{:pattern (Seq.index es i)} p (Seq.index es i))
//epochs in h1 extends epochs in h0 by one

(*
#set-options "--lax"
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

let hs_inv (s:hs) (h: HyperStack.mem) = True
(* 17-04-08 TODO deal with inferred logic qualifiers
  hs_invT s (logT s h) (sel h (HS?.state s))  //An abstract invariant of HS-internal state
  /\ Epochs.containsT s.epochs h                //Nothing deep about these next two, since they can always
  /\ HyperHeap.contains_ref s.state.ref (HyperStack.HS?.h h)                 //be recovered by 'recall'; carrying them in the invariant saves the trouble

//A framing lemma with a very trivial proof, because of the way stateT abstracts the state-dependent parts
*)

#set-options "--lax"
let frame_iT_trivial  (s:hs) (rw:rw) (h0:HyperStack.mem) (h1:HyperStack.mem)
  : Lemma (stateT s h0 = stateT s h1  ==>  iT s rw h0 = iT s rw h1)
  = ()

//Here's a framing on stateT connecting it to the region discipline
let frame_stateT  (s:hs) (rw:rw) (h0:HyperStack.mem) (h1:HyperStack.mem) (mods:Set.set rid)
  : Lemma
    (requires
      HH.modifies_just mods (HyperStack.HS?.h h0) (HyperStack.HS?.h h1) /\
      Map.contains (HyperStack.HS?.h h0) s.region /\
      not (Set.mem s.region mods))
    (ensures stateT s h0 = stateT s h1)
  = ()

//This is probably the framing lemma that a client of this module will want to use
let frame_iT  (s:hs) (rw:rw) (h0:HyperStack.mem) (h1:HyperStack.mem) (mods:Set.set rid)
  : Lemma
    (requires
      HH.modifies_just mods (HyperStack.HS?.h h0) (HyperStack.HS?.h h1) /\
      Map.contains (HyperStack.HS?.h h0) s.region /\
      not (Set.mem s.region mods))
    (ensures stateT s h0 = stateT s h1 /\ iT s rw h0 = iT s rw h1)
=
  frame_stateT s rw h0 h1 mods;
  frame_iT_trivial s rw h0 h1



// factored out; indexing to be reviewed
val register: hs -> KeySchedule.recordInstance -> St unit
let register hs keys =
    let ep = //? we don't have a full index yet for the epoch; reuse the one for keys??
      let h = Nego.Fresh ({ Nego.session_nego = Nego.getMode hs.nego }) in
      Epochs.recordInstanceToEpoch #hs.region #(nonce hs) h keys in // just coercion
    Epochs.add_epoch hs.epochs ep // actually extending the epochs log

(* ------- Pure functions between offer/mode and their message encodings -------- *)

(*
let clientHello offer = // pure; shared by Client and Server
  let sid =
    match offer.co_resume with
    | None -> empty_bytes
    | Some x -> x
    in
  (* In Extensions: prepare client extensions, including key shares *)
  //17-03-30 where are the keyshares? How to convert them?
  let ext = Extensions.prepareExtensions
    offer.co_protocol_version
    offer.co_cipher_suites
    false false //17-03-30 ??
    offer.co_sigAlgs
    offer.co_namedGroups // list of named groups?
    None //17-03-30 ?? optional (cvd,svd)
    offer.co_client_shares // apparently at most one for now
    in
  {
    ch_protocol_version = offer.co_protocol_version;
    ch_client_random = offer.co_client_random;
    ch_sessionID = sid;
    ch_cipher_suites = offer.co_cipher_suites;
    ch_raw_cipher_suites = None;
    ch_compressions = offer.co_compressions;
    ch_extensions = Some ext }
*)

(* -------------------- Handshake Client ------------------------ *)

val client_ClientHello: s:hs -> i:id -> ST (result (HandshakeLog.outgoing i))
  (requires fun h0 ->
    let n = MR.m_sel h0 Nego.(s.nego.state) in
    let t = transcript h0 s.log in
    let k = HyperStack.sel h0 s.ks.KeySchedule.state in
    match n with
    | Nego.C_Init nonce -> k = KeySchedule.(C (C_Init nonce)) /\ t = []
    | _ -> False )
  (ensures fun h0 r h1 ->
    let n = MR.m_sel h0 Nego.(s.nego.state) in
    let t = transcript h0 s.log in
    let k = HyperStack.sel h1 s.ks.KeySchedule.state in
    ( Correct? r ==>
      ( match n with
        | Nego.C_Offer offer -> (
          ( if offer.ch_protocol_version = TLS_1p3
            then
             k = KeySchedule.(C(C_13_wait_SH
              (nonce s)
              [] (*TODO: es for 0RTT*)
              (C_13_wait_SH?.gs (C?.s k)) // TODO
                 // ADL: need an existential for the keyshares (offer only has contains shares)
                 // + check that that the group and CommonDH.pubshare g gx match
              //(Nego.gs_of offer)
             ))
            else k = KeySchedule.(C(C_12_Full_CH offer.ch_client_random)) /\
          t = [ClientHello offer] ))
        | _ -> False )))

let compute_binder hs (binderKey:(i:binderId & bk:KeySchedule.binderKey i))
  : ST (HMAC.UFCMA.tag (HMAC.UFCMA.HMAC_Binder (let (|i,_|) = binderKey in i)))
    (requires fun h0 -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1)  // we'll need a complete spec to determine the transcript
  =
  let (| bid, bk |) = binderKey in
  let digest_CH0 = HandshakeLog.hash_tag #(binderId_hash bid) hs.log in
  HMAC.UFCMA.mac bk digest_CH0


let client_ClientHello hs i =
  (* Negotiation computes the list of groups from the configuration;
     KeySchedule computes and serializes the shares from these groups (calling into CommonDH)
     Messages should do the serialization (calling into CommonDH), but dependencies are tricky *)
  let sid, pskids = resumeInfo_of hs in
  // TODO: 1.2 resumption in both branches
  let shares, binderKeys, pskinfo =
    match (config_of hs).maxVer  with
      | TLS_1p3 -> (* compute shares for groups in offer *)
        trace "offering ClientHello 1.3";
        let (sid, pskids) = resumeInfo_of hs in
        let bk, pski, shares = KeySchedule.ks_client_13_init hs.ks pskids (config_of hs).namedGroups in
        Some shares, bk, pski
      | _ ->
        trace "offering ClientHello 1.2";
        let si = KeySchedule.ks_client_12_init hs.ks in
        None, [], []
    in
  //
  // Compute & send the ClientHello offer
  // for now we assume there is no filtering or reordering on the PSKs.
  // TODO filter PKSs within Nego, not extensions!
  let offer = Nego.client_ClientHello hs.nego shares pskinfo in (* compute offer from configuration *)
  HandshakeLog.send hs.log (ClientHello offer);
  //
  // Computing & sending the binders
  let nego_psk =
    (match Nego.find_clientPske offer with
    | Some pskl ->
      // for later: we only compute binders for PSK identities negotiated in ClientHello
      //      let filter bk =
      //        let (| Binder esId _, bk |) = bk in
      //        let ApplicationPSK pskid _ = esId in
      //        List.Tot.existsb (fun (x,_) -> equalBytes x pskid) pskl in
      //      let nego_binders = List.Tot.filter filter binderKeys in
      if List.Tot.length pskl <> length binderKeys then trace "WARNING: PSK filtering";
      let binders = KeySchedule.map_ST (compute_binder hs) binderKeys in
      HandshakeLog.send hs.log (Binders binders);
      pskl
    | _ -> []) in

  // 0-RTT data
  (match Nego.find_early_data offer, nego_psk with
  | Some _, (pskid, _) :: _ ->
    let Some (_, info0) = List.Tot.find (fun (x,_) -> equalBytes x pskid) pskinfo in
    let digest_CH = HandshakeLog.hash_tag #(PSK.pskInfo_hash info0) hs.log in
    let edk = KeySchedule.ks_client_13_ch hs.ks digest_CH in
    register hs edk
    // TODO enable client 0RTT
  | Some _, [] -> trace "statically excluded"
  | _ -> ());

  hs.state := C_Wait_ServerHello; // we may still need to keep parts of ch
  Correct(HandshakeLog.next_fragment hs.log i)


// requires !hs.state = Wait_ServerHello
// ensures TLS 1.3 ==> installed handshake keys
let client_ServerHello (s:hs) (sh:sh) (* digest:Hashing.anyTag *) : St incoming =
  trace "client_ServerHello";
  match Nego.client_ServerHello s.nego sh with
  | Error z -> InError z
  | Correct mode ->
    let pv = mode.Nego.n_protocol_version in
    let ha = Nego.hashAlg mode in
    let ka = Nego.kexAlg mode in
    HandshakeLog.setParams s.log pv ha (Some ka) None (*?*);
    match pv, ka with
    | TLS_1p3, Kex_DHE //, Some gy
    | TLS_1p3, Kex_ECDHE //, Some gy
    ->
      begin
        trace "Running TLS 1.3";
        let digest = HandshakeLog.hash_tag #ha s.log in
        let hs_keys = KeySchedule.ks_client_13_sh s.ks
          mode.Nego.n_server_random
          mode.Nego.n_cipher_suite
          digest
          (Some?.v mode.Nego.n_server_share)
          mode.Nego.n_pski in
        ( match Nego.zeroRTToffer mode.n_offer, Nego.zeroRTT mode with
          | true, true -> trace "0RTT accepted"
          | true, false -> trace "0RTT refused"
          | _ -> ());
        //TODO check we cover 0rtt-accepted and 0rtt-refused cases
        // we expect 0RTTing clients to check the mode after handshake completion.
        //
        register s hs_keys; // register new epoch
        s.state := C_Wait_Finished1;
        Epochs.incr_reader s.epochs; // Client 1.3 HSK switch to handshake key for decrypting EE etc...
        InAck true false // Client 1.3 HSK
      end
    | TLS_1p3, _ -> InError(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Unsupported group negotiated")
    | _, _ ->
      begin
        trace "Running classic TLS";
        s.state := C_Wait_ServerHelloDone;
        InAck false false
      end

(* receive Certificate...ServerHelloDone, with optional cert request. Not for TLS 1.3 *)
val client_ServerHelloDone:
  hs ->
  HandshakeMessages.crt ->
  HandshakeMessages.ske ->
  option HandshakeMessages.cr ->
  ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_ServerHelloDone hs c ske ocr =
    trace "processing ...ServerHelloDone";
    match Nego.client_ServerKeyExchange hs.nego c ske ocr with
    | Error z -> InError z
    | Correct mode -> (
      ( match ocr with
        | None -> ()
        | Some cr ->
            trace "processing certificate request (TODO)";
            let cc = {crt_chain = []} in
            HandshakeLog.send hs.log (Certificate cc));

      let gy = Some?.v (mode.Nego.n_server_share) in // already set in KS
      let gx =
        KeySchedule.ks_client_12_full_dh hs.ks
        mode.Nego.n_server_random
        mode.Nego.n_protocol_version
        mode.Nego.n_cipher_suite
        (Nego.emsFlag mode) // a flag controlling the use of ems
        gy in
      let (|g, _|) = gy in
      let msg = ClientKeyExchange ({cke_kex_c = kex_c_of_dh_key #g gx}) in
      let ha = verifyDataHashAlg_of_ciphersuite (mode.Nego.n_cipher_suite) in
      let digestClientKeyExchange = HandshakeLog.send_tag #ha hs.log msg  in
      let cfin_key, app_keys = KeySchedule.ks_client_12_set_session_hash hs.ks digestClientKeyExchange in
      register hs app_keys;
      // we send CCS then Finished;  we will use the new keys only after CCS

      trace ("digest is "^print_bytes digestClientKeyExchange);
      //let cvd = TLSPRF.verifyData (mode.Nego.n_protocol_version,mode.Nego.n_cipher_suite) cfin_key Client digestClientKeyExchange in
      let cvd = TLSPRF.finished12 ha cfin_key Client digestClientKeyExchange in
      let digestClientFinished = HandshakeLog.send_CCS_tag #ha hs.log (Finished ({fin_vd = cvd})) false in
      hs.state := C_Wait_CCS2 digestClientFinished;
      InAck false false)

#set-options "--lax"
private val client_ClientFinished_13: hs -> digest -> option HandshakeMessages.cr13 -> (i:finishedId & cfk:KeySchedule.fink i) -> St unit
let client_ClientFinished_13 hs digestServerFinished ocr cfin_key =
  let mode = Nego.getMode hs.nego in
  let ha = verifyDataHashAlg_of_ciphersuite (mode.Nego.n_cipher_suite) in
  let digest =
    match ocr with
    | Some cr -> HandshakeLog.send_tag #ha hs.log (Certificate13 ({crt_request_context = empty_bytes; crt_chain13 = []}))
    | None -> digestServerFinished in
  let (| finId, cfin_key |) = cfin_key in
  let cvd = HMAC.UFCMA.mac cfin_key digest in
  Epochs.incr_writer hs.epochs; // to HSK
  HandshakeLog.send hs.log (Finished ({fin_vd = cvd}));
  Epochs.incr_reader hs.epochs; // to ATK
  HandshakeLog.send_signals hs.log (Some true) true; //was: Epochs.incr_writer hs.epochs
  hs.state := C_Complete // full_mode (cvd,svd); do we still need to keep those?

(* receive EncryptedExtension...ServerFinished for TLS 1.3, roughly mirroring client_ServerHelloDone *)
val client_ServerFinished_13:
  s: hs ->
  ee: HandshakeMessages.ee ->
  ocr: option HandshakeMessages.cr13 ->
  c: HandshakeMessages.crt13 ->
  cv: HandshakeMessages.cv ->
  svd: bytes ->
  digestCert: Hashing.anyTag ->
  digestCertVerify: Hashing.anyTag ->
  digestServerFinished: Hashing.anyTag ->
  St incoming
let client_ServerFinished_13 hs ee ocr c cv (svd:bytes) digestCert digestCertVerify digestServerFinished =
    match Nego.clientComplete_13 hs.nego ee ocr c.crt_chain13 cv digestCert with
    | Error z -> InError z
    | Correct mode ->
        // ADL: 4th returned value is the exporter master secret.
        // should be passed to application somehow --- store in Nego? We need agreement.
        let (sfin_key, cfin_key, app_keys, exporter_master_secret) = KeySchedule.ks_client_13_sf hs.ks digestServerFinished in
        let (| finId, sfin_key |) = sfin_key in
        if not (HMAC.UFCMA.verify sfin_key digestCertVerify svd)
        then InError (AD_decode_error, "Finished MAC did not verify: expected digest "^print_bytes digestCertVerify )
        else (
          register hs app_keys; // ATKs are ready to use in both directions
          if Nego.zeroRTT mode then (
            HandshakeLog.send hs.log EndOfEarlyData;
            HandshakeLog.send_signals hs.log false false;
            hs.state := C_Sent_EOED digestServerFinished ocr cfin_key;
            trace "queued AEAD; are we sending it??";
            InAck false false )
          else (
            client_ClientFinished_13 hs digestServerFinished ocr cfin_key;
            InAck true false // Client 1.3 ATK; next the client will read again to send Finished, writer++, and the Complete signal
          )) // moving to C_Complete

let client_ServerFinished hs f digestClientFinished =
    let sfin_key = KeySchedule.ks_12_finished_key hs.ks in
    let mode = Nego.getMode hs.nego in
    let ha = verifyDataHashAlg_of_ciphersuite mode.Nego.n_cipher_suite in
    let expected_svd = TLSPRF.finished12 ha sfin_key Server digestClientFinished in
    //let expected_svd = TLSPRF.verifyData (mode.Nego.n_protocol_version,mode.Nego.n_cipher_suite) sfin_key Server digestClientFinished in
    if equalBytes f.fin_vd expected_svd
    then (
      hs.state := C_Complete; // ADL: TODO need a proper renego state Idle (Some (vd,svd)))};
      InAck false true // Client 1.2 ATK
      )
    else
      InError (AD_decode_error, "Finished MAC did not verify: expected digest "^print_bytes digestClientFinished)


(* -------------------- Handshake Server ------------------------ *)

(* called by server_ClientHello after sending TLS 1.2 ServerHello *)
// static precondition: n.n_protocol_version <> TLS_1p3 && Some? n.n_sigAlg && (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)
// should instead use Nego for most of this processing
val server_ServerHelloDone: hs -> St incoming // why do I need an explicit val?
let server_ServerHelloDone hs =
  trace "Sending ...ServerHelloDone";
  let mode = Nego.getMode hs.nego in
  let Some chain = mode.Nego.n_server_cert in // Server cert chosen in Nego.server_ClientHello
  match Nego.chosenGroup mode with
  | None ->
    InError (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "no shared supported group")
  | Some g  ->
    // ad hoc signing of the nonces and server key share
    let kex_s = KEX_S_DHE (Some?.v mode.Nego.n_server_share) in
    let tbs =
      let cr = mode.Nego.n_offer.ch_client_random in
      let sv = kex_s_to_bytes kex_s in
      let csr = cr @| mode.Nego.n_server_random in
      Nego.to_be_signed mode.Nego.n_protocol_version Server (Some csr) sv
    in
    match Nego.sign hs.nego tbs with
    | None ->
      InError (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "no compatible signature algorithm")
    | Some signature ->
      begin
      let ske = {ske_kex_s = kex_s; ske_sig = signature} in
      HandshakeLog.send hs.log (Certificate ({crt_chain = Cert.chain_down chain}));
      HandshakeLog.send hs.log (ServerKeyExchange ske);
      HandshakeLog.send hs.log ServerHelloDone;
      hs.state := S_Wait_CCS1;
      InAck false false // Server 1.2 ATK
      end

// the ServerHello message is a simple function of the mode.
let serverHello (m:Nego.mode) =
  let open Nego in
  let pv = m.n_protocol_version in
  ServerHello ({
    sh_protocol_version = pv;
    sh_server_random = m.n_server_random;
    sh_sessionID = m.n_sessionID;
    sh_cipher_suite = m.n_cipher_suite;
    sh_compression = if pv = TLS_1p3 then None else Some NullCompression;
    sh_extensions = m.n_server_extensions })

(* receive ClientHello, choose a protocol version and mode *)
val server_ClientHello: hs -> HandshakeMessages.ch -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let server_ClientHello hs offer =
    trace "Processing ClientHello";
    let sid = Some (CoreCrypto.random 32) (* used only if we negotiate TLS < 1.3 *) in
    // Nego proceeds in two steps, first server share
    match Nego.server_ClientHello hs.nego offer sid with
    | Error z -> InError z
    | Correct mode ->
      begin
      let server_share =
        match mode.Nego.n_protocol_version, mode.Nego.n_client_share, Nego.kexAlg mode with
        | TLS_1p3, Some (| g, gx |), _ ->
          Some
            (CommonDH.ServerKeyShare
              (KeySchedule.ks_server_13_1rtt_init
                hs.ks offer.ch_client_random mode.Nego.n_cipher_suite g gx))
        | TLS_1p3, _, _  -> None
        | _, _, Kex_DHE
        | _, _, Kex_ECDHE ->
          begin
          match Nego.chosenGroup mode with
          | None ->  None // Should be unreachable
          | Some g ->
            let cr = mode.Nego.n_offer.ch_client_random in
            let gy = KeySchedule.ks_server_12_init_dh hs.ks cr
              mode.Nego.n_protocol_version
              mode.Nego.n_cipher_suite
              (Nego.emsFlag mode)
              g
            in Some (CommonDH.ServerKeyShare (CommonDH.Share g gy))
          end
      in
      match Nego.server_ServerShare hs.nego server_share with
      | Error z -> InError z
      | Correct mode ->
        let pv = mode.Nego.n_protocol_version in
        let ha = Nego.hashAlg mode in
        let ka = Nego.kexAlg mode in
        HandshakeLog.setParams hs.log pv ha (Some ka) None;
        let ha = verifyDataHashAlg_of_ciphersuite (mode.Nego.n_cipher_suite) in
        let digestServerHello = HandshakeLog.send_tag #ha hs.log (serverHello mode) in
        if mode.Nego.n_protocol_version = TLS_1p3
        then
          begin
            // TODO handle 0RTT accepted and 0RTT refused
            // - get 0RTT key from KS.
            // - do the signalling
            HandshakeLog.send_signals hs.log (Some false) false; // signal key change after writing ServerHello
            trace "derive handshake keys";
            let hs_keys = KeySchedule.ks_server_13_sh hs.ks digestServerHello (* digestServerHello *)  in
            register hs hs_keys;
            // We will start using the HTKs later (after sending SH, and after receiving 0RTT traffic)
            hs.state := S_Sent_ServerHello;
            InAck false false
          end
        else
          server_ServerHelloDone hs // sending our whole flight hopefully in a single packet.
        end


(* receive ClientKeyExchange; CCS *)
let server_ClientCCS1 hs cke (* clientCert *) digestCCS1 =
    // FIXME support optional client c and cv
    // let ems = n.n_extensions.ne_extended_ms in // ask Nego?
    trace "process Client CCS";
    match cke.cke_kex_c with
      | KEX_C_RSA _ | KEX_C_DH -> InError(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Expected DHE/ECDHE CKE")
      | KEX_C_DHE gyb
      | KEX_C_ECDHE gyb ->
        begin
          let mode = Nego.getMode hs.nego in  //TODO read back from mode.
          // ADL: the type of gyb will change from bytes to g & share g; for now we parse here.
          let Some (|g,  _|) = mode.Nego.n_server_share in
          match CommonDH.parse g gyb with
          | None -> InError(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Cannot parse client share in CKE")
          | Some gy ->
            let app_keys = KeySchedule.ks_server_12_cke_dh hs.ks (| g, gy |) digestCCS1 in
            register hs app_keys;
            Epochs.incr_reader hs.epochs;
            // use the new reader; will use the new writer only after sending CCS
            hs.state := S_Wait_Finished1 digestCCS1; // keep digest to verify the Client Finished
            InAck true false  // Server 1.2 ATK
        end

(* receive ClientFinish *)
val server_ClientFinished:
  hs -> bytes -> Hashing.anyTag -> Hashing.anyTag -> St incoming
let server_ClientFinished hs cvd digestCCS digestClientFinished =
    trace "Process Client Finished";
    let fink = KeySchedule.ks_12_finished_key hs.ks in
    let mode = Nego.getMode hs.nego in
    let alpha = (mode.Nego.n_protocol_version, mode.Nego.n_cipher_suite) in
    let ha = verifyDataHashAlg_of_ciphersuite (mode.Nego.n_cipher_suite) in
    let expected_cvd = TLSPRF.finished12 ha fink Client digestCCS in
    //let expected_cvd = TLSPRF.verifyData alpha fink Client digestCCS in
    if equalBytes cvd expected_cvd
    then
      //let svd = TLSPRF.verifyData alpha fink Server digestClientFinished in
      let svd = TLSPRF.finished12 ha fink Server digestClientFinished in
      let unused_digest = HandshakeLog.send_CCS_tag #ha hs.log (Finished ({fin_vd = svd})) true in
      hs.state := S_Complete;
      InAck false false // Server 1.2 ATK; will switch write key and signal completion after sending
    else
      InError (AD_decode_error, "Finished MAC did not verify: expected digest "^print_bytes digestClientFinished)

(* send EncryptedExtensions; Certificate13; CertificateVerify; Finish (1.3) *)
val server_ServerFinished_13: hs -> i:id -> ST (result (outgoing i))
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let server_ServerFinished_13 hs i =
    // static pre: n.n_protocol_version = TLS_1p3 && Some? n.n_sigAlg && (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)
    // most of this should go to Nego
    trace "prepare Server Finished";
    let mode = Nego.getMode hs.nego in
    let Some chain = mode.Nego.n_server_cert in
    let pv = mode.Nego.n_protocol_version in
    let cs = mode.Nego.n_cipher_suite in
    let sh_alg = sessionHashAlg pv cs in
    let halg = verifyDataHashAlg_of_ciphersuite cs in // Same as sh_alg but different type FIXME

    HandshakeLog.send hs.log (EncryptedExtensions []);
    let digestSig = HandshakeLog.send_tag #halg hs.log (Certificate13 ({crt_request_context = empty_bytes; crt_chain13 = chain})) in

    // signing of the formatted session digest
    let tbs : bytes =
      let Hash sh_alg = sh_alg in
      let hL = Hashing.Spec.tagLen sh_alg in
      let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
      let rc = Hashing.compute sh_alg zeroes in
      let lb = digestSig @| rc in
      Nego.to_be_signed pv Server None lb
    in
    match Nego.sign hs.nego tbs with
    | None ->
      Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "no compatible signature algorithm")
    | Some signature ->
      begin
      let digestFinished = HandshakeLog.send_tag #halg hs.log (CertificateVerify ({cv_sig = signature})) in
      let (| sfinId, sfin_key |) = KeySchedule.ks_server_13_server_finished hs.ks in
      let svd = HMAC.UFCMA.mac sfin_key digestFinished in
      let digestServerFinished = HandshakeLog.send_tag #halg hs.log (Finished ({fin_vd = svd})) in
      // we need to call KeyScheduke twice, to pass this digest
      // ADL this call also returns exporter master secret, which should be passed to application
      let app_keys, _ = KeySchedule.ks_server_13_sf hs.ks digestServerFinished in
      register hs app_keys;
      HandshakeLog.send_signals hs.log (Some true) false;
      Epochs.incr_reader hs.epochs; // TODO when to increment the reader?
      hs.state := S_Wait_Finished2 (Nego.zeroRTT mode, digestServerFinished);
      Correct(HandshakeLog.next_fragment hs.log i)
      end

(* receive ClientFinish 1.3 *)
val server_ClientFinished_13: hs ->
  cvd:bytes ->
  Hashing.anyTag -> // Digest either up to ServerFinished or up to CertificateVerify with client certg
  Hashing.anyTag -> // Digest up to ClientFinished
  option (HandshakeMessages.crt13 * HandshakeMessages.cv * Hashing.anyTag) -> St incoming
let server_ClientFinished_13 hs f digestBeforeClientFinished digestClientFinished clientAuth =
   trace "Process Client Finished";
   match clientAuth with
   | Some  (c,cv,digest) ->
      InError(AD_internal_error,
        perror __SOURCE_FILE__ __LINE__ "Client CertificateVerify validation not implemented")
   | None ->
       let (| i, cfin_key |) = KeySchedule.ks_server_13_client_finished hs.ks in
       // TODO MACVerify digestClientFinished
       if HMAC.UFCMA.verify cfin_key digestBeforeClientFinished f
       then (
          // ADL: missing call for resumption master secret etc
          //let _ = KeySchedule.ks_server_13_cf ks digestClientFinished in
          hs.state := S_Complete;
          Epochs.incr_reader hs.epochs; // finally start reading with AKTs
          InAck true true  // Server 1.3 ATK
          )
       else InError (AD_decode_error, "Finished MAC did not verify: expected digest "^print_bytes digestClientFinished)

(* TODO: resumption *)
assume val server_send_server_finished_res: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

(* Handshake API: PUBLIC Functions, taken from FSTI *)

// returns the protocol version negotiated so far
// (used for formatting outgoing packets, but not trusted)
(*
val version: s:hs -> Tot protocolVersion
  (requires (hs_inv s))
  (ensures (fun h0 pv h1 -> h0 = h1))
  *)

(* ----------------------- Control Interface -------------------------*)

let create (parent:rid) cfg role resume =
  let r = new_region parent in
  let log = HandshakeLog.create r None (* cfg.maxVer (Nego.hashAlg nego) *) in
  //let nonce = Nonce.mkHelloRandom r r0 in //NS: should this really be Client?
  let ks, nonce = KeySchedule.create #r role in
  let nego = Nego.create r role cfg resume nonce in
  let epochs = Epochs.create r nonce in
  let state = ralloc r (if role = Client then C_Idle else S_Idle) in
  let x: hs = HS role nego log ks epochs state in //17-04-17 why needed?
  x

let rehandshake s c = Platform.Error.unexpected "rehandshake: not yet implemented"

let rekey s c = Platform.Error.unexpected "rekey: not yet implemented"

let request s c = Platform.Error.unexpected "request: not yet implemented"

let invalidateSession hs = ()
// ADL: disabling this for top-level API testing purposes
// Platform.Error.unexpected "invalidateSession: not yet implemented"


(* ------------------ Outgoing -----------------------*)

let next_fragment (hs:hs) i =
    trace "next_fragment";
    let outgoing = HandshakeLog.next_fragment hs.log i in
    match outgoing, !hs.state with
    // when the output buffer is empty, we send extra messages in two cases
    // we prepare the initial ClientHello; or
    // after sending ServerHello in plaintext, we continue with encrypted traffic
    // otherwise, we just returns buffered messages and signals
    | Outgoing None None false, C_Idle -> client_ClientHello hs i
    | Outgoing None None false, S_Sent_ServerHello -> server_ServerFinished_13 hs i
    | Outgoing None None false, C_Sent_EOED d ocr cfk -> client_ClientFinished_13 hs d ocr cfk; Correct(HandshakeLog.next_fragment hs.log i)

    //| Outgoing msg  true _ _, _ -> (Epochs.incr_writer hs.epochs; Correct outgoing) // delayed
    | _ -> Correct outgoing // nothing to do

(* ----------------------- Incoming ----------------------- *)

let rec recv_fragment (hs:hs) #i rg f =
    let  recv_again r =
      match r with
      | InAck false false -> recv_fragment hs #i (0,0) empty_bytes // only case where the next incoming flight may already have been buffered.
      | r -> r  in
    trace "recv_fragment";
    let h0 = ST.get() in
    let flight = HandshakeLog.receive hs.log f in
    match flight with
    | Error z -> InError z
    | Correct None -> InAck false false // nothing happened
    | Correct (Some (ms,ts)) ->
      match !hs.state, ms, ts with
      | C_Idle, _, _ -> InError (AD_unexpected_message, "Client hasn't sent hello yet")
      | C_Wait_ServerHello, [ServerHello sh], [] ->
        recv_again (client_ServerHello hs sh)

    //| C_Wait_ServerHello, Some ([ServerHello sh], [digest]) -> client_ServerHello hs sh digest
      | C_Wait_ServerHelloDone, [Certificate c; ServerKeyExchange ske; ServerHelloDone], [] ->
        client_ServerHelloDone hs c ske None

      | C_Wait_ServerHelloDone, [Certificate c; ServerKeyExchange ske; CertificateRequest cr; ServerHelloDone], [] ->
        client_ServerHelloDone hs c ske (Some cr)

      | C_Wait_Finished1, [EncryptedExtensions ee; Certificate13 c; CertificateVerify cv; Finished f], [digestCert; digestCertVerify; digestServerFinished] ->
        client_ServerFinished_13 hs ee None c cv f.fin_vd digestCert digestCertVerify digestServerFinished

      | C_Wait_Finished1, [EncryptedExtensions ee; CertificateRequest13 cr; Certificate13 c; CertificateVerify cv; Finished f], [digestCert; digestCertVerify; digestServerFinished] ->
        client_ServerFinished_13 hs ee (Some cr) c cv f.fin_vd digestCert digestCertVerify digestServerFinished

      // we'll have other variants for resumption, shc as ([EncryptedExtensions ee; Finished f], [...])

      | C_Wait_Finished2 digestClientFinished, [Finished f], [digestServerFinished] ->
        client_ServerFinished hs f digestClientFinished

      | S_Idle, [ClientHello ch], []  ->
        server_ClientHello hs ch
      | S_Wait_Finished1 digest, [Finished f], [digestClientFinish] ->
        server_ClientFinished hs f.fin_vd digest digestClientFinish
      | S_Wait_Finished1 digest, [Finished f], tags ->
        (trace (List.Tot.fold_left (fun a t -> a^" "^print_bytes t) "BAD TAGS: "tags);
        server_ClientFinished hs f.fin_vd digest digest )

      | S_Wait_Finished2 (false, digestServerFinished),
        [Finished f], [digestClientFinished] ->
        server_ClientFinished_13 hs f.fin_vd digestServerFinished digestClientFinished None

      | S_Wait_Finished2 (false, digestServerFinished),
        [Certificate13 c; CertificateVerify cv; Finished f], [digestSigned; digestCertVerify; digestClientFinished] ->
        server_ClientFinished_13 hs f.fin_vd digestCertVerify digestClientFinished (Some (c, cv, digestSigned))

      | S_Wait_Finished2 (true, digestServerFinished),
        [EndOfEarlyData; Finished f], [digestClientFinished] ->
        server_ClientFinished_13 hs f.fin_vd digestServerFinished digestClientFinished None

      | S_Wait_Finished2 (true, digestServerFinished),
        [EndOfEarlyData; Certificate13 c; CertificateVerify cv; Finished f], [digestSigned; digestCertVerify; digestClientFinished] ->
        server_ClientFinished_13 hs f.fin_vd digestCertVerify digestClientFinished (Some (c, cv, digestSigned))

      // are we missing the case with a Certificate but no CertificateVerify?
      | _,  _, _ ->
        trace "DISCARD FLIGHT"; InAck false false
        //InError(AD_unexpected_message, "unexpected flight")



// TODO check CCS once committed to TLS 1.3 yields an alert
let recv_ccs (hs:hs) =
    trace "recv_ccs";
    // assert pv <> TLS 1.3
    // CCS triggers completion of the incoming flight of messages.
    let mode = Nego.getMode hs.nego in
    match HandshakeLog.receive_CCS #(Nego.hashAlg mode) hs.log with
    | Error z -> InError z
    | Correct (ms, digests, digestCCS) ->
        match !hs.state, ms, digests with
        | C_Wait_CCS2 digest, [], [] -> (
            trace "Processing CCS";
            hs.state := C_Wait_Finished2 digest;
            Epochs.incr_reader hs.epochs;
            InAck true false // Client 1.2 ATK
            )

        | C_Wait_CCS2 digest, [NewSessionTicket st], [] -> (
            trace "Processing SessionTicket; CCS. WARNING: no support for tickets";
            // now expect encrypted finish on this digest; shall we tell Nego?
            hs.state := C_Wait_Finished2 digest;
            Epochs.incr_reader hs.epochs;
            InAck true false // Client 1.2 ATK
            )

        | S_Wait_CCS1, [ClientKeyExchange cke], [digest_to_finish] ->
            // assert (Some? pv && pv <> Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE))
            // getting two copies of the same digest?
            server_ClientCCS1 hs cke digestCCS
(*
        // FIXME support optional client c and cv
        | S_HelloDone n, [Certificate c; ClientKeyExchange cke], [digestClientKeyExchange]
          when (c.crt_chain = [] && Some? pv && pv <> Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
            server_ClientCCS hs cke digestClientKeyExchange (Some (c, None))

        | S_HelloDone n, [Certificate c; ClientKeyExchange cke; CertificateVerify cv], [digestClientKeyExchange; digestCertificateVerify]]
          when (Some? pv && pv <> Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
            server_ClientCCS hs cke digestClientKeyExchange (Some (c, Some (cv, digestCertificateVerify)))
*)
        | _, _, _ ->
            trace "WARNING: bad CCS";
            InError(AD_unexpected_message, "CCS received at wrong time")


let authorize s ch = Platform.Error.unexpected "authorize: not yet implemented"
