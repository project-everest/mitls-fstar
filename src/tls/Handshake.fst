(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
module Handshake

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
//FIXME! Don't open so much ... gets confusing. Use module abbrevs instead
//AR: Yes ! Totally agree.
//CF: TODO.
open FStar.Seq
 // for e.g. found
open FStar.Set

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open Range
open HandshakeMessages
//open Negotiation
open StAE

//16-05-31 these opens are implementation-only; overall we should open less
open Extensions
//open CoreCrypto
open Epochs
//open HandshakeLog


module HH = FStar.HyperHeap
module MR = FStar.Monotonic.RRef
module MS = FStar.Monotonic.Seq
module KS = KeySchedule
module Nego = Negotiation

let hashSize = Hashing.Spec.tagLen

//<expose for TestClient> CF: temporarily broken; such tests should be coded against HS submodules.
// TODO restore unit tests as in TestClient

(* A flag for runtime debugging of Handshake data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
inline_for_extraction let hs_debug = false



(* Returns [c] if [c] is within the range of acceptable versions for [cfg],
 * [Error] otherwise. *)

// TODO : implement resumption
val getCachedSession: cfg:config -> ch:ch -> ST (option session)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let getCachedSession cfg cg = None


(* Handshake API: TYPES, taken from FSTI *)

//17-03-24 consider using instead "if role = Client then clientState else serverServer"
//17-03-24 but that may break extraction to Kremlin and complicate typechecking
//17-03-24 we could also use two refinements. 
type machineState =
  | C_Idle:                  option ri -> clientState
  | C_HelloSent:       option ri -> ch -> clientState

  // only after accepting TLS 1.3
  | C_HelloReceived:              nego -> clientState
  | C_PostHS:                             clientState

  // only after accepting TLS classic
  | C_OutCCS:                     nego -> clientState
  | C_FinishedSent:nego -> cVerifyData -> clientState
  | C_CCSReceived: nego -> cVerifyData -> clientState
  | C_FinishedReceived:     nego -> ri -> clientState

  | C_Error:                     error -> clientState

  | S_Idle:                  option ri -> serverState

  // only after choosing TLS 1.3
  | S_HelloSent :                 nego -> serverState 
  | S_ZeroRTTReceived :           nego -> serverState
  | S_PostHS:                             serverState

  // only after choosing TLS classic
  | S_HelloDone :                 nego -> serverState 
  | S_CCSReceived :               nego -> cVerifyData -> serverState
  | S_FinishedReceived :          nego -> serverState
  | S_OutCCS:                     nego -> serverState
  | S_FinishedSent :              nego -> serverState
  | S_ResumeFinishedSent :        nego -> serverState

  | S_Error:                     error -> serverState

// TODO: review their parameters; should probably all disappear except for some digests 


// MOVE to HandshakeMessage
//16-06-01 we don't need to precisely track this part of the state
//16-06-01 later, pre-allocate large-enough buffers for the connection.
//16-06-01 also revisit type of encrypted messages
type hs_msg_bufs = {
     hs_incoming_parsed : list (hs_msg * bytes); // messages parsed earlier
     hs_incoming: bytes;                         // incomplete message received earlier
     hs_outgoing: bytes;                         // messages to be sent in current epoch
     hs_outgoing_epochchange: option rw;         // Whether to increment the reader or writer epoch after sending the messages in the current epoch
     hs_outgoing_ccs: bool;                      // Whether a CCS signal is buffered for the local writer
}
let hs_msg_bufs_init() = {
     hs_incoming_parsed = [];
     hs_incoming = empty_bytes;
     hs_outgoing = empty_bytes;
     hs_outgoing_epochchange = None;
     hs_outgoing_ccs = false;
}



//</expose for TestClient>
// internal stuff: state machine, reader/writer counters, etc.
// (will take other HS fields as parameters)

type resume_info (r:role) = 
  o:option sessionID{r=Server ==> o=None} *
  l:list PSK.psk_identifier {r=Server ==> l = []} // assuming we do the PSK lookups locally  

type hs = | HS: 
  #region: rgn { is_hs_rgn region } ->
  r: role ->
  nonce: TLSInfo.random ->  // unique for all honest instances; locally enforced
  nego: Negotiation.t region r ->
  log: Handshake.Log.t region (Negotiation.hashAlg nego) (* embedding msg buffers *) -> 
  ks: KeySchedule.ks region r -> 
  epochs: epochs region nonce ->
  state: rref region machineState -> // state machine; should be opaque and depend on r.
  hs

// the states of the HS sub=module will be subject to a joint invariant

// now both part of immutable nego state:
// resume: resume_info r (* client dyn. config, both for 1.2 and 1.3 *) ->
// cfg: config -> 


(* the handshake internally maintains epoch
   indexes for the current reader and writer *)

let logT (s:hs) (h:HyperStack.mem) = Epochs.epochsT s.log h

let stateType (s:hs) = seq (epoch s.region s.nonce) * handshake_state (HS?.r s)

let stateT (s:hs) (h:HyperStack.mem) : GTot (stateType s) = (logT s h, sel h s.state)

let non_empty h s = Seq.length (logT s h) > 0

let logIndex (#t:Type) (log: seq t) = n:int { -1 <= n /\ n < Seq.length log }

let forall_epochs (hs:hs) h (p:(epoch hs.region hs.nonce -> Type)) =
  (let es = logT hs h in
   forall (i:nat{i < Seq.length es}).{:pattern (Seq.index es i)} p (Seq.index es i))
//epochs in h1 extends epochs in h0 by one
let fresh_epoch h0 s h1 =
  let es0 = logT s h0 in
  let es1 = logT s h1 in
  Seq.length es1 > 0 &&
  es0 = Seq.slice es1 0 (Seq.length es1 - 1)

let latest h (s:hs{Seq.length (logT s h) > 0}) = // accessing the latest epoch
 let es = logT s h in
 Seq.index es (Seq.length es - 1)



(* vs modifies clauses? *)
(* let unmodified_epochs s h0 h1 =  *)
(*   forall_epochs s h0 (fun e ->  *)
(*     let rs = regions e in  *)
(*     (forall (r:rid{Set.mem r rs}).{:pattern (Set.mem r rs)} Map.sel h0 r = Map.sel h1 r)) *)

// separation policy: the handshake mutates its private state,
// only depends on it, and only extends the log with fresh epochs.


// placeholder, to be implemented as a stateful property.
assume val completed: #region:rgn -> #nonce:TLSInfo.random -> epoch region nonce -> Type0

// consider adding an optional (resume: option sid) on the client side
// for now this bit is not explicitly authenticated.

// Well-formed logs are all prefixes of (Epoch; Complete)*; Error
// This crucially assumes that TLS keeps track of OutCCS and InCCSAck
// so that it knows which reader & writer to use (not always the latest ones):
// - within InCCSAck..OutCCS, we still use the older writer
// - within OutCCS..InCCSAck, we still use the older reader
// - otherwise we use the latest readers and writers

// technicality: module dependencies?
// we used to pre-declare all identifiers in TLSInfo
// we used owe could also record (fatal) errors as log terminators

// abstract invariant; depending only on the HS state (not the epochs state)
// no need for an epoch states invariant here: the HS never modifies them

assume val hs_invT : s:hs -> epochs:seq (epoch s.region s.nonce) -> handshake_state (HS?.r s) -> Type0

let hs_inv (s:hs) (h: HyperStack.mem) =
  hs_invT s (logT s h) (sel h (HS?.state s))  //An abstract invariant of HS-internal state
  /\ Epochs.containsT s.log h                //Nothing deep about these next two, since they can always
  /\ HyperHeap.contains_ref s.state.ref (HyperStack.HS?.h h)                 //be recovered by 'recall'; carrying them in the invariant saves the trouble

let iT (s:hs) rw (h:HyperStack.mem) =
    match rw with
    | Reader -> Epochs.readerT s.log h
    | Writer -> Epochs.writerT s.log h

//A framing lemma with a very trivial proof, because of the way stateT abstracts the state-dependent parts
let frame_iT_trivial  (s:hs) (rw:rw) (h0:HyperStack.mem) (h1:HyperStack.mem)
  : Lemma (stateT s h0 = stateT s h1
           ==> iT s rw h0 = iT s rw h1)
  = ()

//Here's a framing on stateT connecting it to the region discipline
let frame_stateT  (s:hs) (rw:rw) (h0:HyperStack.mem) (h1:HyperStack.mem) (mods:Set.set rid)
  : Lemma (requires HH.modifies_just mods (HyperStack.HS?.h h0) (HyperStack.HS?.h h1)
            /\ Map.contains (HyperStack.HS?.h h0) s.region
            /\ not (Set.mem s.region mods))
          (ensures stateT s h0 = stateT s h1)
  = ()

//This is probably the framing lemma that a client of this module will want to use
let frame_iT  (s:hs) (rw:rw) (h0:HyperStack.mem) (h1:HyperStack.mem) (mods:Set.set rid)
  : Lemma (requires HH.modifies_just mods (HyperStack.HS?.h h0) (HyperStack.HS?.h h1)
            /\ Map.contains (HyperStack.HS?.h h0) s.region
            /\ not (Set.mem s.region mods))
          (ensures stateT s h0 = stateT s h1
           /\ iT s rw h0 = iT s rw h1)
  = frame_stateT s rw h0 h1 mods;
    frame_iT_trivial s rw h0 h1

// returns the epoch for reading or writing
let eT s rw (h:HyperStack.mem { iT s rw h >= 0 }) = Seq.index (logT s h) (iT s rw h)

let readerT s h = eT s Reader h
let writerT s h = eT s Writer h

// this function increases (how to specify it once for all?)
val i: s:hs -> rw:rw -> ST int
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> h0 == h1
              /\ i = iT s rw h1
              /\ Epochs.get_ctr_post (HS?.log s) rw h0 i h1))
let i (HS #r0 _ _ _ _ epochs _) rw =
  match rw with
  | Reader -> Epochs.get_reader epochs
  | Writer -> Epochs.get_writer epochs




// payload of a handshake fragment, to be made opaque eventually
type message (i:id) = ( rg: frange i & rbytes rg )
let out_msg i rg b : message i= (|rg, b|)

// What the HS asks the record layer to do, in that order.
type outgoing (i:id) (* initial index *) =
  | Outgoing:
      send_first: option (message i) -> // HS fragment to be sent;  (with current id)
      send_ccs  : bool               -> // CCS fragment to be sent; (with current id)
      next_keys : bool               -> // the writer index increases;
      complete  : bool               -> // the handshake is complete!
      outgoing i
  | OutError: error -> outgoing i       // usage? in case something goes wrong when preparing messages.

let out_next_keys (#i:id) (r:outgoing i) = Outgoing? r && Outgoing?.next_keys r
let out_complete (#i:id) (r:outgoing i)  = Outgoing? r && Outgoing?.complete r

type incoming =
  // the fragment is accepted, and...
  | InAck:
      next_keys : bool -> // the reader index increases;
      complete  : bool -> // the handshake is complete!
      incoming

  | InQuery: Cert.chain -> bool -> incoming // could be part of InAck if no explicit user auth
  | InError: error -> incoming // how underspecified should it be?

let in_next_keys (r:incoming) = InAck? r && InAck?.next_keys r
let in_complete (r:incoming)  = InAck? r && InAck?.complete r


let optHashAlg_prime_is_optHashAlg: result hashAlg' -> Tot (result hashAlg) =
  function
  | Error z -> Error z
  | Correct h -> Correct h

let sigHashAlg_is_tuple_sig_hash: sigHashAlg -> Tot (sigAlg * hashAlg) =
  function | a,b -> a,b

let rec list_sigHashAlg_is_list_tuple_sig_hash: list sigHashAlg -> Tot (list (sigAlg * hashAlg)) =
  function
  | [] -> []
  | hd::tl -> (sigHashAlg_is_tuple_sig_hash hd) :: (list_sigHashAlg_is_list_tuple_sig_hash tl)

val to_be_signed: pv:protocolVersion -> role -> csr:option bytes{None? csr <==> pv = TLS_1p3} -> bytes -> Tot bytes
let to_be_signed pv role csr tbs =
  match pv, csr with
  | TLS_1p3, None ->
    let pad = abytes (String.make 64 (Char.char_of_int 32)) in
    let ctx =
      match role with
      | Server -> "TLS 1.3, server CertificateVerify"
      | Client -> "TLS 1.3, client CertificateVerify"
    in
    pad @| (abytes ctx) @| (abyte 0z) @| tbs
  | _, Some csr -> csr @| tbs

val sigHashAlg_of_ske: bytes -> Tot (option (sigHashAlg * bytes))
let sigHashAlg_of_ske signature =
  if length signature > 4 then
   let h, sa, sigv = split2 signature 1 1 in
   match vlsplit 2 sigv with
   | Correct (sigv, eof) ->
     begin
     match length eof, parseSigAlg sa, optHashAlg_prime_is_optHashAlg (parseHashAlg h) with
     | 0, Correct sa, Correct (Hash h) -> Some ((sa,Hash h), sigv)
     | _, _, _ -> None
     end
   | Error _ -> None
  else None


(* Handshake API: INTERNAL Callbacks, hidden from API *)

(* Sketch 
val Nego.prepareClientOffer: config -> clientOffer
let Nego.prepareClientOffer cfg =
  let groups = List.Tot.choose CommonDH.group_of_namedGroup cfg.namedGroups in
  let cipher_suites = ... in
  let sigAlgs = ... in
  let protocol_version = ... in
  let ext = prepareExtensions protocol_version cipher_suites sigAlgs groups kp in
*)  




(* Handshake.Client *)

(* send ClientHello *)
val client_send_client_hello: hs -> ST unit 
  (requires (fun h -> 
    True (* add the precondition that Nego and KS are in proper state *) ))
  (ensures (fun h0 i h1 -> True))
  (* TODO: what should we say here? something like:
    - The Keys Schedule state machine is in the initial state
    - The Handshake log has exactly one more message: the ClientHello computed from the input configurtion
    - The result is this ClientHello and its serialization
  *)
let client_send_client_hello hs =
  (* merged in prepare_client_hello *)
  (* Negotiation computes the list of groups from the configuration;
     KeySchedule computes and serializes the shares from these groups (calling into CommonDH)
     Messages should do the serialization (calling into CommonDH), but dependencies are tricky
  *)
  let offer = Nego.clientOffer hs.nego hs.cfg hs.resume in   (* compute offer from configuration *)
  let shares = (* compute shares for groups in offer *)
    match offer.co_protocol_version with
    | TLS_1p3 -> Some (KeySchedule.ks_client_13_1rtt_init hs.ks offer.co_namedGroups)
    | _       -> let si = KeySchedule.ks_client_12_init ks in None
    in
  (* Some? sido in case of resumption *)
  let sid =
    match fst hs.resume with
    | None -> empty_bytes
    | Some x -> x
  in
  (* In Extensions: prepare client extensions, including key shares *)
  let ext = prepareExtensions offer hs.resume ri shares in
  let ch = // a bit too concrete? ClientHello hs.nonce offer hs.resume ri shares
  {
    ch_protocol_version = offer.co_protocol_version;
    ch_client_random = hs.nonce;
    ch_sessionID = sid;
    ch_cipher_suites = offer.co_cipher_suites;
    ch_raw_cipher_suites = None;
    ch_compressions = offer.co_compressions;
    ch_extensions = Some ext
  } in
  Handshake.Log.send hs.log (ClientHello ch);  // TODO in two steps, appending the binders
  hs.state := C_HelloSent ri ch

(* receive ServerHello *)
let client_ServerHello hs sh =
    IO.hs_debug_print_string "Processing client hello...\n";
    let r = Nego.clientModel hs.nego  (*... don't repeat the offer? *) 
      //ch.ch_extensions ch.ch_protocol_version 
      sh.sh_protocol_version 
      sh.sh_server_random 
      sh.sh_cipher_suite 
      sh.sh_extensions 
      sh.sh_compression ri in
    match r with
    | Error z -> Error z
    | Correct (n,keys) -> (

    //17-03-24 what's the main "mode" type? o_nego or mode? 
   (* no need for this one yet? 
   let o_nego =
    {n_client_random = ch.ch_client_random;
     n_server_random = sh.sh_server_random;
     n_sessionID = sh.sh_sessionID;
     n_protocol_version = mode.cm_protocol_version;
     n_kexAlg = mode.cm_kexAlg;
     n_aeAlg = mode.cm_aeAlg;
     n_sigAlg = mode.cm_sigAlg;
     n_cipher_suite = mode.cm_cipher_suite;
     n_dh_group = mode.cm_dh_group;
     n_compression = sh.sh_compression;
     n_scsv = [];
     n_extensions = mode.cm_ext;
     n_resume = false } in 
     
    (match o_nego.n_protocol_version, o_nego.n_kexAlg, mode.cm_dh_group, mode.cm_dh_share with
     | TLS_1p3, Kex_DHE, Some gn, Some gyb
     | TLS_1p3, Kex_ECDHE, Some gn, Some gyb ->
       (match CommonDH.group_of_namedGroup gn with
       | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Unsupported group negotiated")
       | Some g ->
         (match CommonDH.parse g gyb  // This should have been parsed earlier! 
         with
         | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse server share")
         | Some gy ->
           let keys = KeySchedule.ks_client_13_sh ks o_nego.n_cipher_suite g gy false in
           Correct (o_nego, Some keys)))
     | _ -> Correct (o_nego,None))
*)
    // split between 1.2 and 1.3 
      ( match keys with 
      | Some keys -> ( // If a handshake encryption key is returned install the epoch and increment the reader
          let ep = 
            //? we don't have a full index yet for the epoch; reuse the one for keys??
            let h = Negotiation.Fresh ({session_nego = n}) in
            Epochs.recordInstanceToEpoch #r0 #nonce h keys in 
          Epochs.add_epoch hs.epochs ep;
          Epochs.incr_reader hs.epochs  )
      | None -> ());
      hs_state := C_HelloReceived n;
      InAck (Some? keys) false )

(* receive Certificate...ServerHelloDone *)
// with or without a certificate request; not for TLS 1.3
val client_ServerHelloDone: 
  hs -> _ -> _ -> _ -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let client_ServerHelloDone hs c ske ocr = 
    match Nego.clientComplete hs.nego c ske ocr with 
    | Error z -> Error z 
    | Correct (fullmode, g, gy) -> (

    (* here are the checks we were doing before; now hopefully in Nego:
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
                   // IO.hs_debug_print_string("tbs = " ^ (Platform.Bytes.print_bytes tbs) ^ "\n");
                   IO.hs_debug_print_string("Signature validation status = " ^ (if valid then "OK" else "FAIL") ^ "\n");
                   if not valid_signature then Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "failed to check SKE signature")
                   else 
                     match ske.ske_kex_s with
                     | KEX_S_RSA _ -> Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "only support ECDHE/DHE SKE") )
                     | KEX_S_DHE (| g, gy |) -> 
                     *)

                       ( match ocr with 
                         | None -> ()
                         | Some cr -> 
                             let cc = {crt_chain = []} in // TODO
                             Handshake.Log.send hs.log (Certificate cc));
                       let gx = KeySchedule.ks_client_12_full_dh ks n.n_server_random n.n_protocol_version n.n_cipher_suite n.n_extensions.ne_extended_ms g gy in
                       let msg = ClientKeyExchange ({cke_kex_c = kex_c_of_dh_key #g gx}) in
                       let digestClientKeyExchange = Handshake.Log.send_tag hs.log msg  in

                       (* fuse these two calls? *)
                       if ems then KeySchedule.ks_client__12_set_session_hash hs.ks digestClientKeyExchange; 
                       let app_keys = KeySchedule.ks_12_get_keys hs.ks  in
                       let ep = 
                         let h = Negotiation.Fresh ({session_nego = n}) in
                         Epochs.recordInstanceToEpoch h keys in
                       Epochs.add_epoch hs.epochs ep;
                       hs.state := C_OutCCS n;                       
                       InAck false false )

(*
val client_send_client_finished: hs -> ST unit
  (requires (fun h -> True (* C_OutCCS *) ))
  (ensures (fun h0 i h1 -> True))
let client_send_client_finished hs =
    let tag = KeySchedule.ks_client_12_client_finished hs.ks in
    HandshakeLog.send (Finished {fin_vd = tag});
    hs.state := C_FinishedSent n tag
*)

(* receive Server CCS *)
// inlined in recv_ccs (two cases)

(* receive EncryptedExtension...ServerFinished 1.3 *)
// keep this function check against client ServerHelloDone
let client_ServerFinished_13 hs ee ocr c cv svd digestCert digestCertVerify digestServerFinished =
    match Nego.clientComplete_13 hs.nego ee ocr c cv digestCert with 
    | Error z -> Error z 
    | Correct full_mode -> 

    (* here are the checks we were doing before; now hopefully in Nego:
    let valid_chain = cfg.check_peer_certificate => Cert.validate_chain c.crt_chain true cfg.peer_name cfg.ca_file in
    if not valid_chain then Error (AD_decode_error, "Certificate was not valid")
    else
    begin
       let Some cs_sigalg = n.n_sigAlg in
       let Some algs = n.n_extensions.ne_signature_algorithms in
       IO.hs_debug_print_string("cv_sig = " ^ (Platform.Bytes.print_bytes cv.cv_sig) ^ "\n");
       match sigHashAlg_of_ske cv.cv_sig with
       | Some ((sa,ha), sigv) ->
         if not (List.Tot.existsb (fun (xs,xh) -> (xs = sa && xh = ha)) (list_sigHashAlg_is_list_tuple_sig_hash algs))
         then Error (AD_handshake_failure, "Signature algorithm negotiation failed")
         else (
           begin
           let Hash sh_alg = sessionHashAlg n.n_protocol_version n.n_cipher_suite in
           let hL = hashSize sh_alg in
           let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
           let rc = Hashing.compute sh_alg zeroes in
           let lb = (HandshakeLog.getHash log sh_alg) @| rc in
           let a = Signature.Use (fun _ -> true) sa [ha] false false in
           let tbs = to_be_signed n.n_protocol_version Server None lb in
           match Signature.get_chain_public_key #a c.crt_chain with
           | None -> Error (AD_decode_error, "Certificate was not valid")
           | Some pk ->
             let valid_signature = Signature.verify ha pk tbs sigv in
             IO.hs_debug_print_string("Signature validation status = " ^ (if valid then "OK" else "FAIL") ^ "\n");
             if not valid then Error (AD_decode_error, "Certificate signature did not verify")
             else *)

               let (cfin_key, sfin_key, app_keys) = KeySchedule.ks_client_13_server_finished ks in
               // was also calling:  let keys = KeySchedule.ks_client_13_sf ks in
               // was also calling:  let cvd = KeySchedule.ks_client_13_client_finished ks in
               // was also calling: let ems = KeySchedule.ks_client_13_cf ks in // ? 
               if  not MAC.verify sfin_key digestCertVerify svd then Error (AD_decode_error, "Finished MAC did not verify")
               else (
                 let digest = 
                   match ocr with 
                   | Some cr -> Handshake.Log.send_tag (Certificate ({crt_chain = []}))
                   | None -> digestServerFinished in 
                 let cvd = MAC.mac cfin_key digest in 
                 Handshake.Log.send (Finished ({fin_vd = cvd});
                 let ep = 
                   let h = Negotiation.Fresh ({session_nego = full_mode}) in // review index?
                   Epochs.recordInstanceToEpoch #r0 #id h app_keys in
                 Epochs.add_epoch hs.epochs ep;
                 Epochs.incr_reader hs.epochs;
                 Epochs.incr_writer hs.epochs; // TODO update writer key properly
                 hs.state := C_FinishedReceived full_mode (cvd,svd); // do we still need to keep those?
                 InAck true false ))



// Handshake.Server 

(* receive ClientHello; send ServerHello (still for all pv) *) 
val server_ClientHello: hs -> HandshakeMessages.ch -> ST incoming
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let server_ClientHello hs ch =
    match Nego.computeServerMode hs.nego ch with
    | Error z -> Error z
    | Correct mode -> (
      let srand = KS.ks_server_random hs.ks in
      let ksl = // move to Nego?
        (match mode.sm_protocol_version, mode.sm_dh_group, mode.sm_dh_share with
         | TLS_1p3, Some gn, Some gxb ->
         (match CommonDH.group_of_namedGroup gn with
          | None -> None
          | Some g ->
           (match CommonDH.parse g gxb with
           | None -> None
           | Some gx ->
             Some (KeySchedule.ks_server_13_1rtt_init ks ch.ch_client_random mode.sm_cipher_suite g gx)))
       | _ -> None) in
      (* Extensions:negotiateServerExtensions *) 
      match negotiateServerExtensions mode.sm_protocol_version ch.ch_extensions ch.ch_cipher_suites cfg mode.sm_cipher_suite ri ksl false with
      | Error z -> Error z
      | Correct sext -> (
        let sid = CoreCrypto.random 32 in
        let sh =
          { sh_protocol_version = mode.sm_protocol_version;
             sh_sessionID = Some sid;
             sh_server_random = srand;
             sh_cipher_suite = mode.sm_cipher_suite;
             sh_compression = mode.sm_comp;
             sh_extensions = sext} in
        Handshake.Log.send (ServerHello sh); 
             
        let nego = // should be directly returned by Nego? Who allocates sid?
          { n_client_random = ch.ch_client_random;
             n_server_random = srand;
             n_sessionID = Some sid;
             n_protocol_version = mode.sm_protocol_version;
             n_kexAlg = mode.sm_kexAlg;
             n_sigAlg = mode.sm_sigAlg;
             n_aeAlg  = mode.sm_aeAlg;
             n_cipher_suite = mode.sm_cipher_suite;
             n_compression = mode.sm_comp;
             n_dh_group = mode.sm_dh_group;
             n_scsv = [];
             n_extensions = mode.sm_ext;
             (* [getCachedSession] returned [None], so no session resumption *)
             n_resume = false} in

        if mode.sm_protocol_version = TLS_1p3 then
        ( let keys = KeySchedule.ks_server_13_sh ks in
          let ep = 
            let h = Negotiation.Fresh ({session_nego = n}) in
            Epochs.recordInstanceToEpoch #r0 #id h ri in
         // Do not increment writer yet as the SH is sent in plaintext
          Epochs.add_epoch lgref ep); 
          hs.state := S_HelloSent n;
          InAck false false))

// We can directly continue to ServerHelloDone when pv < 1.3. 


(* send Certificate; CertificateVerify; ServerHelloDone *) 
//val server_ServerHelloDone: hs -> ST unit
//  (requires (fun h -> True))
//  (ensures (fun h0 i h1 -> True))
let server_ServerHelloDone hs n =
    if not (n.n_protocol_version <> TLS_1p3 && Some? n.n_sigAlg && (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE))
    then Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "should not call this function in TLS 1.3")
    else 
    match Cert.lookup_chain cfg.cert_chain_file with
    | Error z -> Error z
    | Correct chain ->
      let c = {crt_chain = chain} in
      let cr = n.n_client_random in
      let ems = n.n_extensions.ne_extended_ms in
      let pv = n.n_protocol_version in
      let cs = n.n_cipher_suite in
      let Some gn = n.n_dh_group in // FIXME error flow
      let Some g = CommonDH.group_of_namedGroup gn in // FIXME static enforcement
      let gy = KeySchedule.ks_server_12_init_dh ks cr pv cs ems g in
      let kex_s = KEX_S_DHE gy in
      let sv = kex_s_to_bytes kex_s in
      let csr = n.n_client_random @| n.n_server_random in

      // Signature agility (following the broken rules of 7.4.1.4.1. in RFC5246)
      let Some sa = n.n_sigAlg in
      let sigalgs = n.n_extensions.ne_signature_algorithms in
      let algs =
          match sigalgs with
          | Some l -> l
          | None -> [(sa,Hash Hashing.Spec.SHA1)]  in
      let algs = List.Tot.filter (fun (s,_) -> s = sa) algs in
      let sa, ha =
          match algs with
          | sha::_ -> sha
          | [] -> (sa, Hash Hashing.Spec.SHA1)
        in
      let hab, sab = hashAlgBytes ha, sigAlgBytes sa in
      let a = Signature.Use (fun _ -> true) sa [ha] false false in
      let tbs = to_be_signed n.n_protocol_version Server (Some csr) sv in
      begin
        match Signature.lookup_key #a cfg.private_key_file with
        | None -> Error (AD_internal_error, perror __SOURCE_FILE__ __LINE__ "could not load siginig key")
        | Some csk ->
            let sigv = Signature.sign ha csk tbs in
          if not (length sigv >= 2 && length sigv < 65536)
          then Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "signature length out of range")
          else

      // move most code above to Nego?   
              begin
                lemma_repr_bytes_values (length sigv);
                let signature = (hab @| sab @| (vlbytes 2 sigv)) in
                let ske = {ske_kex_s = kex_s; ske_sig = signature} in
                Handshake.Log.send hs.log (Certificate c);
                Handshake.Log.send hs.log (ServerKeyExchange ske);
                Handshake.Log.send hs.log ServerHelloDone;
                s.state := S_HelloDone n
              end
      end

(* receive ClientKeyExchange; CCS *)
let server_ClientCCS hs cke digest (* clientCert *)  =
    // FIXME support optional client c and cv 
    // let ems = n.n_extensions.ne_extended_ms in // ask Nego? 
    match cke.cke_kex_c with
      | KEX_C_RSA _ | KEX_C_DH -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Expected DHE/ECDHE CKE")
      | KEX_C_DHE gyb
      | KEX_C_ECDHE gyb -> (
          let Some gn = n.n_dh_group in // FIXME error flow
          let Some g = CommonDH.group_of_namedGroup gn in // FIXME static enforcement
          let gy = CommonDH.parse g gyb in 
          KeySchedule.ks_server_12_cke_dh ks g gy; 

          let app_keys = KeySchedule.ks_12_get_keys (!hsref).hs_ks in
          let h = Negotiation.Fresh ({session_nego = n}) in
          let ep = Epochs.recordInstanceToEpoch h keys in
          Epochs.add_epoch lgref ep;
          Epochs.incr_reader lgref;
          hs.state := S_CCSReceived n digest; // keep digest to verify the Client Finished
          InAck true false )

(* receive ClientFinish *) 
let server_ClientFinished hs digestCCS digestClientFinished =

    // to be adjusted
    let cvd = KeySchedule.ks_server_12_client_finished ks in
    if not (equalBytes cvd f.fin_vd) then Error (AD_decode_error, "Finished MAC did not verify")
    else
        let svd = KeySchedule.ks_server_12_server_finished ks in
        let fin = Finished ({fin_vd = svd}) in
        let finb = log @@ fin in

        (hsref := {!hsref with
                  hs_buffers = {(!hsref).hs_buffers with
                   hs_outgoing_ccs = true; 
                   // Because of the current constraints of the Record/HS interface the sendCCS flag is only available on writing
                   // therefore, I am forced to "buffer" the fact a CCS will need to be sent before the ServerFinished
                   hs_outgoing = finb};
               hs_state = S(S_OutCCS n)};
        InAck false false)

(* send ServerFinish (inlined) *) 

(* send EncryptedExtensions; Certificate; CertificateVerify; Finish (1.3) *)
val server_send_server_finished_13: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let server_send_server_finished_13 hs n = 
  if not (n.n_protocol_version = TLS_1p3 && Some? n.n_sigAlg && (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE))
  then Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "should not call this function in TLS < 1.3")
  else
    match Cert.lookup_chain cfg.cert_chain_file with
    | Error z -> Error z
    | Correct chain ->

      Handshake.Log.send hs.log (EncryptedExtensions ({ee_extensions = []}));
      let digestSig = Handshake.Log.send_tag hs.log (Certificate ({crt_chain = chain})) in 

      let pv = n.n_protocol_version in
      let cs = n.n_cipher_suite in
      let sh_alg = sessionHashAlg pv cs in

      //TODO factor out code for signing
      // Signature agility (following the broken rules of 7.4.1.4.1. in RFC5246)
      // If no signature nego took place we use the SA and KDF hash from the CS
      let Some sa = n.n_sigAlg in
      let algs =
        match n.n_extensions.ne_signature_algorithms with
        | Some l -> l
        | None -> [sa, sh_alg]
      in
      let algs = List.Tot.filter (fun (s,_) -> s = sa) algs in
      let sa, ha =
        match algs with
        | ha::_ -> ha
        | [] -> (sa, sh_alg) in
      let hab, sab = hashAlgBytes ha, sigAlgBytes sa in
      let a = Signature.Use (fun _ -> true) sa [ha] false false in
      begin
        match Signature.lookup_key #a cfg.private_key_file with
        | None -> Error (AD_internal_error, perror __SOURCE_FILE__ __LINE__ "could not load signing key")
        | Some csk -> (
            let Hash sh_alg = sh_alg in
            let hL = hashSize sh_alg in
            let zeroes = Platform.Bytes.abytes (String.make hL (Char.char_of_int 0)) in
            let rc = Hashing.compute  sh_alg zeroes in
            let lb = digestSig @| rc in
            let tbs = to_be_signed pv Server None lb in
            let sigv = Signature.sign ha csk tbs in
            let signature = hab @| sab @| vlbytes 2 sigv in

            let digestFinished = Handshake.Log.send_tag hs.log (CertificateVerify ({cv_sig = signature})) in
            let svd = KeySchedule.ks_server_13_server_finished hs.ks digestFinished in
            Handshake.Log.send (Finished ({fin_vd = svd}));

            let keys = KeySchedule.ks_server_13_sf ks in
            let ep = 
               let h = Negotiation.Fresh ({session_nego = n}) in
               Epochs.recordInstanceToEpoch #r0 #id h keys in
            Epochs.add_epoch lgref ep;
            Epochs.incr_writer lgref; // Switch to ATK after the SF
            Epochs.incr_reader lgref; // TODO when to increment the reader?

            ///??? hs_outgoing_epochchange = Some Writer; };
            hs.state := S_FinishedSent n )
      end 

(* receive ClientFinish 1.3 *)
let server_ClientFinished_13 hs n f digestClientFinished clientAuth=
   match clientAuth with
   | Some (c,cv,digest) -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Client CertificateVerify validation not implemented")
   | None -> 
       let cvd = KeySchedule.ks_server_13_client_finished hs.ks digestClientFinished in
       if not (equalBytes cvd f.fin_vd) then Error (AD_decode_error, "Finished MAC did not verify")
       else (
          Epochs.incr_writer hs.epochs lgref;
          hs.state := S_FinishedReceived n;
          InAck true false )

(* TODO: resumption *)
assume val server_send_server_finished_res: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))



(* Handshake API: PUBLIC Functions, taken from FSTI *)

// returns the protocol version negotiated so far
// (used for formatting outgoing packets, but not trusted)
val version: s:hs -> ST protocolVersion
  (requires (hs_inv s))
  (ensures (fun h0 pv h1 -> h0 = h1))
let version (HS r res cfg id l st) =
    match (!st).hs_nego with
    | Some n -> n.n_protocol_version
    | None -> cfg.minVer

// JP: the outside has been checked against the fsti which had another
// definition (at the bottom of this file)
val iT_old:  s:hs -> rw:rw -> ST int
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let iT_old (HS r res cfg id l st) rw =
  match rw with
  | Reader -> (!st).hs_reader
  | Writer -> (!st).hs_writer



(* Control Interface *)

// Create instance for a fresh connection, with optional resumption for clients
val create: r0:rid -> r: role -> cfg:config -> resume: resume_id r ->
  ST hs
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion r0 (HS?.region s) h0 h1 /\
    hs_inv s h1 /\
    HS?.r s = r /\
    HS?.resume s = resume /\
    HS?.cfg s = cfg /\
    logT s h1 = Seq.createEmpty ))
let create r0 r cfg res =
    let id = Nonce.mkHelloRandom r r0 in //NS: should this really be Client?
    let lgref = Epochs.epochs_init r0 id in
    let hs = handshake_state_init cfg r r0 in
    let hsref = ralloc r0 hs in
    HS #r0 r res cfg id lgref hsref

// MERGE: 
val handshake_state_init: (cfg:TLSInfo.config) -> (r:role) -> (reg:rid) -> ST (handshake_state r)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let handshake_state_init cfg (r:role) (reg:rid) =
   let nego = Nego.create cfg in // where is the resumption info? 
   let log = HandshakeLog.create #reg in
   let ks, nonce = KeySchedule.create #reg r log in
   let epochs = Epochs.create reg nonce in 
   let state = ralloc (if r = Client then C_Idle else S_Idle) in
   ST r nonce epochs nego log ks state


let mods s h0 h1 =
  HyperStack.modifies_one s.region h0 h1

let modifies_internal h0 s h1 =
    hs_inv s h1 /\
    mods s h0 h1 /\
    modifies_rref s.region !{as_ref s.state} (HyperStack.HS?.h h0) (HyperStack.HS?.h h1)

// Idle client starts a full handshake on the current connection
val rehandshake: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ HS?.r s = Client))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))
let rehandshake s c = Platform.Error.unexpected "rehandshake: not yet implemented"

// Idle client starts an abbreviated handshake resuming the current session
val rekey: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ HS?.r s = Client))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))
let rekey s c = Platform.Error.unexpected "rekey: not yet implemented"

// (Idle) Server requests an handshake
val request: s:hs -> config -> ST bool
  (requires (fun h -> hs_inv s h /\ HS?.r s = Server))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1))
let request s c = Platform.Error.unexpected "request: not yet implemented"

val invalidateSession: s:hs -> ST unit
  (requires (hs_inv s))
  (ensures (fun h0 _ h1 -> modifies_internal h0 s h1)) // underspecified
let invalidateSession hs = ()
// ADL: disabling this for top-level API testing purposes
// Platform.Error.unexpected "invalidateSession: not yet implemented"


(* Outgoing (main) *)

//val next_fragment: see .fsti
let next_fragment_ensures (#i:id) (s:hs) h0 (result:outgoing i) h1 =
    let es = logT s h0 in
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    hs_inv s h1 /\
    mods s h0 h1 /\
    r1 == r0 /\
//  w1 == (match result with | Outgoing _ _ true _ -> w0 + 1 | _ -> w0 ) /\
    w1 == (if out_next_keys result then  w0 + 1 else w0 ) /\
    Seq.length (logT s h1) >= Seq.length (logT s h0) /\
    (b2t (out_complete result) ==> r1 = w1 /\ indexable (logT s h1) w1 /\ completed (eT s Writer h1))

val next_fragment: i:id -> s:hs -> ST (outgoing i)
  (requires (fun h0 ->
    let es = logT s h0 in
    let j = iT s Writer h0 in
    hs_inv s h0 /\
    (if j = -1 then PlaintextID? i else let e = Seq.index es j in i = epoch_id e)
  ))
  (ensures (next_fragment_ensures s))
let rec next_fragment i hs =
    let (HS #r0 r res cfg id lgref hsref) = hs in
    let pv,kex,res =
      (match (!hsref).hs_nego with
       | None -> None, None, None
       | Some n -> Some n.n_protocol_version, Some n.n_kexAlg, Some n.n_resume) in
    let b = (!hsref).hs_buffers.hs_outgoing in

    // GOING to Handshake.Log
    //16-06-01 TODO: handle fragmentation; return fragment + flags set in some cases
    let l = length b in
    if (!hsref).hs_buffers.hs_outgoing_ccs then (
       hsref := {!hsref with
         hs_buffers = {(!hsref).hs_buffers with
           hs_outgoing_ccs = false }};
       Epochs.incr_writer lgref;
       Outgoing None true true false
    ) else if (l > 0) then (
       let keychange =
          match (!hsref).hs_buffers.hs_outgoing_epochchange with
          | None -> false
          | Some Reader -> Epochs.incr_reader lgref; true // possibly used by server in 0-RT
          | Some Writer -> Epochs.incr_writer lgref; true in
       IO.hs_debug_print_string (" * WRITE "^print_bytes b^"\n");
       hsref := {!hsref with
         hs_buffers = {(!hsref).hs_buffers with
           hs_outgoing = empty_bytes;
           hs_outgoing_epochchange = None }};
       Outgoing (Some (out_msg i (l,l) b)) false keychange false)
    else
    
      (match !hsref.state with
       | C_Error e -> OutError e
       | S_Error e -> OutError e
       | C_Idle ri -> (
          client_send_client_hello hs; 
          next_fragment i hs )
       | C_OutCCS n -> (
          //was: client_send_client_finished hs;
          let tag = KeySchedule.ks_client_12_client_finished hs.ks in
          Handshake.Log.send hs.log (Finished ({fin_vd = tag}));
          hs.state := C_FinishedSent n tag
          Epochs.incr_writer lgref;
          Outgoing None true true false )
       | C_FinishedReceived n (cvd,svd) ->
          hsref := {!hsref with hs_state = C (C_PostHS)};
          Epochs.incr_writer lgref; // Switch to ATK writer
          Outgoing None false true true
       | S_HelloSent n when (Some? pv && pv <> Some TLS_1p3 && res = Some false) ->
          server_ServerHelloDone hs n;
          next_fragment i hs
       | S_HelloSent n when (Some? pv && pv <> Some TLS_1p3 && res = Some true) ->
          server_send_server_finished_res hs;
          next_fragment i hs
       | S_HelloSent n when (Some? pv && pv = Some TLS_1p3) ->
          server_send_server_finished_13 hs n;
          next_fragment i hs
       | S_FinishedReceived n ->
          Epochs.incr_reader lgref; // Switch to ATK reader
          hs.state := S_PostHS;
          Outgoing None false true true
       | S_OutCCS n ->
          hs.state := S_FinishedSent n  // who actually sends the ServerFinished? buffered?
          Outgoing None false false true
       | _ -> Outgoing None false false false)

(* Incoming (main) *)

// GOING Handshake.Log
val parseHandshakeMessages : option protocolVersion -> option kexAlg -> buf:bytes -> Tot  (result (rem:bytes * list (hs_msg * bytes)))
let rec parseHandshakeMessages pv kex buf =
    match parseMessage buf with
    | Error z -> Error z
    | Correct None -> Correct (buf,[])
    | Correct (Some (|rem,hstype,pl,to_log|)) ->
      (match parseHandshakeMessage pv kex hstype pl with
       | Error z -> Error z
       | Correct hsm ->
             (match parseHandshakeMessages pv kex rem with
                | Error z -> Error z
                | Correct (r,hsl) -> Correct(r,(hsm,to_log)::hsl)))


let recv_ensures (s:hs) (h0:HyperStack.mem) (result:incoming) (h1:HyperStack.mem) =
    let w0 = iT s Writer h0 in
    let w1 = iT s Writer h1 in
    let r0 = iT s Reader h0 in
    let r1 = iT s Reader h1 in
    hs_inv s h1 /\
    mods s h0 h1 /\
    w1 == w0 /\
    r1 == (if in_next_keys result then r0 + 1 else r0) /\
    (b2t (in_complete result) ==> r1 >= 0 /\ r1 = w1 /\ iT s Reader h1 >= 0 /\ completed (eT s Reader h1))

// move to Handshake.Log?
let print_hsl hsl : Tot bool =
    let sl = List.Tot.map (fun (x,_) -> HandshakeMessages.string_of_handshakeMessage x) hsl in
    let s = List.Tot.fold_left (fun x y -> x^", "^y) "" sl in
    IO.debug_print_string("Recv_fragment buffer: " ^ s ^ "\n")


val recv_fragment: s:hs -> #i:id -> message i -> ST incoming
  (requires (hs_inv s))
  (ensures (recv_ensures s))
let recv_fragment hs #i f =
    let pv, kex, res = // still needed? function on hs.nego? 
      match !hsref.hs_nego with
      | None -> None, None, None
      | Some n -> Some n.n_protocol_version, Some n.n_kexAlg, Some n.n_resume in
    let flight = Handshake.Log.receive hs.log f in 

    (* This should go to HSL: 
    let (| rg,rb |) = f in
    let b =
      if hs_debug then
        IO.debug_print_string ("   *** RAW "^(print_bytes rb)^"\n")
      else false in
    let (HS #r0 r res cfg id lgref hsref) = hs in
    let b = (!hsref).hs_buffers.hs_incoming in
    let b = b @| rb in
    match parseHandshakeMessages pv kex b with
    | Error (ad, s) ->
      let _ =
        if hs_debug then
          IO.debug_print_string ("Failed to parse message: "^(string_of_ad ad)^": "^s^"\n")
        else false in
      InError (ad,s)
    | Correct(r,hsl) ->
       let hsl = List.Tot.append (!hsref).hs_buffers.hs_incoming_parsed hsl in
       hsref := {!hsref with hs_buffers = {(!hsref).hs_buffers with hs_incoming = r; hs_incoming_parsed = hsl}};
      let b =
        if hs_debug then
          print_hsl hsl
        else false in
      *)

    (* incoming transitions for our state machine *) 
    match !hs.state, flight with 

      (* CLIENT *) 
      
      | C_Idle, _ -> InError(AD_unexpected_message, "Client hasn't sent hello yet")

      | C_HelloSent ch, Some ([ServerHello sh], [digestServerHello]) -> client_ServerHello sh digestServerHello

      | C_HelloReceived n, Some ([Certificate c; ServerKeyExchange ske; ServerHelloDone], [unused_digestCert])
        when (Some? pv && pv <> Some TLS_1p3 && res = Some false && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
          (* shall we also check we have a sigAlg? *)
          client_ServerHelloDone hs c ske None

      | C_HelloReceived n, Some ([Certificate c; ServerKeyExchange ske; CertificateRequest cr; ServerHelloDone], [unused_digestCert])
        when (Some? pv && pv <> Some TLS_1p3 && res = Some false && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
          client_ServerHelloDone hs c ske (Some cr)

      | C_HelloReceived n, Some ([EncryptedExtensions ee; Certificate c; CertificateVerify cv; Finished f], [digestCert; digestCertVerify; digestServerFinished]) 
        when (Some? pv && pv = Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
          client_ServerFinished_13 hs ee None c cv f.fin_vd digestCert digestCertVerify digestServerFinished

      | C_HelloReceived n, Some ([EncryptedExtensions ee; CertificateRequest cr; Certificate c; CertificateVerify cv; Finished f], [digestCert; digestCertVerify; digestServerFinished]) 
        when (Some? pv && pv = Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
          client_ServerFinished_13 hs ee (Some cr) c cv f.fin_vd digestCert digestCertVerify digestServerFinished

      // we'll have other variants for resumption, shc as ([EncryptedExtensions ee; Finished f], [...]) 

      | C_CCSReceived n cv, Some ([Finished f], [digestServerFinished]) 
        when Some? pv && pv <> Some TLS_1p3 ->
          let svd = KeySchedule.ks_client_12_server_finished ks in // should provide digest!
          if equalBytes svd f.fin_vd then (
            hs.state := C_PostHS; // ADL: TODO need a proper renego state Idle (Some (vd,svd)))};
            InAck false true )
          else Error (AD_decode_error, "Finished MAC did not verify")

      (* SERVER *) 

      //17-03-24 how to receive binders? we need the intermediate hash 
      | S_Idle ri, Some ([ClientHello ch], [])  ->
          server_ClientHello hs ch

      | S_CCSReceived s digest, Some ([Finished f], [digestClientFinish]) 
        when (Some? pv && pv <> Some TLS_1p3) -> 
          server_ClientFinished hs f digest digestClientFinish

      | S_FinishedSent s, Some ([Finished f], [digest])
        when (Some? pv && pv = Some TLS_1p3) -> 
          server_ClientFinished_13 hs s f digest None 

      | S_FinishedSent s, Some ([Certificate c; CertificateVerify cv; Finished f], [digestSigned; digestClientFinished; _]) 
        when (Some? pv && pv = Some TLS_1p3) ->
          server_ClientFinished_13 hs s f digestClientFinished (Some (c,cv,digestSigned))  

       // are we missing the case with a Certificate but no CertificateVerify? 

      | C_Error e, _ -> InError e
      | S_Error e, _ -> InError e
      | _, _ -> InAck false false // nothing yet to process


val recv_ccs: s:hs -> ST incoming  // special case: CCS before 1p3; could merge with recv_fragment
  (requires (hs_inv s)) // could require pv <= 1p2
  (ensures (fun h0 result h1 ->
    recv_ensures s h0 result h1 /\
    (InError? result \/ result = InAck true false)
    ))
let recv_ccs hs =
    IO.hs_debug_print "CALL recv_ccs\n";
    let pv, kex = 
      match Nego.read_mode hs.nego with // not necessarily defined early enough?
      | Some n -> Some n.n_protocol_version, Some n.n_kexAlg
      | None -> None, None in

    // intuitively, receiving CCS triggers completion of the incoming flight of messages.
    match Handshake.Log.ReadCCS hs.log with
    | Error -> InError(AD_unexpected_message, "CCS received at wrong time")
    | Correct (ms, hs, digest) -> 
        match !hs.state, ms, hs with 
        | C_FinishedSent n cv, ([], []) -> (
            // we now expect the encrypted server finish, should keep the digest to verify it
            hs.state := C_CCSReceived n cv;
            Epochs.incr_reader hs.epochs;
            InAck true false )

        | C_FinishedSent n cv, ([SessionTicket st], []) -> (
            IO.hs_debug_print "WARNING: no support for session tickets";
            // we now expect the encrypted server finish, should keep the digest to verify it
            hs.state := C_CCSReceived n cv;
            Epochs.incr_reader hs.epochs;
            InAck true false )

        | S_HelloDone n, ([ClientKeyExchange cke], []) 
          when (Some? pv && pv <> Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
            server_ClientCCS hs cke digest
(*
        // FIXME support optional client c and cv
        | S_HelloDone n, [Certificate c; ClientKeyExchange cke], [digestClientKeyExchange]
          when (c.crt_chain = [] && Some? pv && pv <> Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
            server_ClientCCS hs cke digestClientKeyExchange (Some (c, None))

        | S_HelloDone n, [Certificate c; ClientKeyExchange cke; CertificateVerify cv], [digestClientKeyExchange; digestCertificateVerify]] 
          when (Some? pv && pv <> Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) ->
            server_ClientCCS hs cke digestClientKeyExchange (Some (c, Some (cv, digestCertificateVerify)))
*)
        | C_Error e, _ -> InError e
        | S_Error e, _ -> InError e
        | _, _ -> InError(AD_unexpected_message, "CCS received at wrong time")


val authorize: s:hs -> Cert.chain -> ST incoming // special case: explicit authorize (needed?)
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    (InAck? result \/ InError? result) /\ recv_ensures s h0 result h1 ))
let authorize s ch = Platform.Error.unexpected "authorize: not yet implemented"
