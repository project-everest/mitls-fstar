(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
module Handshake

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
//FIXME! Don't open so much ... gets confusing. Use module abbrevs instead
//AR: Yes ! Totally agree.
//CF: TODO
open FStar.Seq
open FStar.Set

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open Range
open HandshakeMessages // for the message syntax
//open StAE 

//16-05-31 these opens are implementation-only; overall we should open less
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
   when this flag is set to false. 

   SI: pull both these out to a Debug/Config module. *)
inline_for_extraction let hs_debug = false

// inline/normalize  too? 
let debug_print s = 
  if hs_debug then
    IO.debug_print_string s 
  else false 


(* Returns [c] if [c] is within the range of acceptable versions for [cfg],
 * [Error] otherwise. *)

// TODO : implement resumption
//val getCachedSession: cfg:config -> ch:ch -> ST (option session)
//  (requires (fun h -> True))
//  (ensures (fun h0 i h1 -> True))
//let getCachedSession cfg cg = None


(* Handshake API: TYPES, taken from FSTI *)

//17-03-24 consider using instead "if role = Client then clientState else serverServer"
//17-03-24 but that may break extraction to Kremlin and complicate typechecking
//17-03-24 we could also use two refinements. 

type digest = l:bytes{length l <= 32}
type machineState =
  | C_Idle
  | C_Wait_ServerHello
  | C_Complete

  // only after accepting TLS 1.3
  | C_Wait_Finished1

  // only after accepting TLS classic
  | C_Wait_ServerHelloDone
  | C_Wait_CCS2 of digest
  | C_Wait_Finished2 of digest

  | S_Idle
  | S_Complete

  // only after choosing TLS 1.3
  | S_Sent_ServerHello // required to start encryption
  | S_Wait_Finished2 of digest

  // only after choosing TLS classic
  | S_Wait_CCS1
  | S_Wait_Finished1
  
// Removed error states, consider adding again to ensure the machine is stuck?

//</expose for TestClient>
// internal stuff: state machine, reader/writer counters, etc.
// (will take other HS fields as parameters)

noeq type hs = | HS: 
  #region: rgn { is_hs_rgn region } ->
  r: role ->
  nonce: TLSInfo.random ->  // unique for all honest instances; locally enforced
  nego: Nego.t region r ->
  log: Handshake.Log.t region (Nego.hashAlg nego) (* embedding msg buffers *) -> 
  ks: KeySchedule.ks -> //region r -> 
  epochs: epochs region nonce ->
  state: ref machineState (*in region*) -> // state machine; should be opaque and depend on r.
  hs

// the states of the HS sub=module will be subject to a joint invariant


(* the handshake internally maintains epoch
   indexes for the current reader and writer *)

let logT (s:hs) (h:HyperStack.mem) = Epochs.epochsT s.epochs h

let stateType (s:hs) = seq (epoch s.region s.nonce) * machineState // handshake_state (HS?.r s)

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

assume val hs_invT : s:hs -> epochs:seq (epoch s.region s.nonce) -> machineState -> Type0

let hs_inv (s:hs) (h: HyperStack.mem) =
  hs_invT s (logT s h) (sel h (HS?.state s))  //An abstract invariant of HS-internal state
  /\ Epochs.containsT s.epochs h                //Nothing deep about these next two, since they can always
  /\ HyperHeap.contains_ref s.state.ref (HyperStack.HS?.h h)                 //be recovered by 'recall'; carrying them in the invariant saves the trouble

let iT (s:hs) rw (h:HyperStack.mem) =
    match rw with
    | Reader -> Epochs.readerT s.epochs h
    | Writer -> Epochs.writerT s.epochs h

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


(* -------------------- Handshake Client ------------------------ *)

val client_ClientHello: hs -> i:id -> ST (result (Outgoing i))
  (requires (fun h -> 
    True (* add the precondition that Nego and KS are in proper state *) ))
  (ensures (fun h0 i h1 -> True))
  (* TODO: what should we say here? something like:
    - The Keys Schedule state machine is in the initial state
    - The Handshake log has exactly one more message: the ClientHello computed from the input configurtion
    - The result is this ClientHello and its serialization
  *)
let client_ClientHello hs =
  (* Negotiation computes the list of groups from the configuration;
     KeySchedule computes and serializes the shares from these groups (calling into CommonDH)
     Messages should do the serialization (calling into CommonDH), but dependencies are tricky *)
  let offer = Nego.clientOffer hs.nego in (* compute offer from configuration *)
  let shares = 
    match offer.co_protocol_version with
      | TLS_1p3 -> (* compute shares for groups in offer *)
        let ks = KeySchedule.ks_client_13_1rtt_init hs.ks offer.co_namedGroups in 
        Some ks
      | _ -> 
        let si = KeySchedule.ks_client_12_init ks in 
        None 
    in
  let sid =
    match offer.co_resume with 
    | None -> empty_bytes
    | Some x -> x
    in
  (* In Extensions: prepare client extensions, including key shares *)
  let ext = Extensions.prepareExtensions offer hs.resume ri shares in
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
  Handshake.Log.send hs.log (ClientHello ch);  // TODO decompose in two steps, appending the binders
  hs.state := C_Wait_ServerHello; // we may still need to keep parts of ch
  Correct(Handshake.Log.next_fragment hs.log i)


let client_ServerHello hs sh =
  debug_print "Processing client hello...\n";
  let n = Nego.clientMode hs.nego sh in
  match n with
  | Error z -> Error z
  | Correct mode ->
    match mode.protocol_version, mode.kexAlg, mode.group, mode.share with
    | TLS_1p3, Kex_DHE, Some g, Some gy
    | TLS_1p3, Kex_ECDHE, Some g, Some gy -> (* commit to TLS 1.3 *)
      begin
        let keys = KeySchedule.ks_client_13_sh ks o_nego.n_cipher_suite g gy false in
        let ep = //? we don't have a full index yet for the epoch; reuse the one for keys??
          let h = Nego.handshakeKeyInfo hs.nego  in
          Epochs.recordInstanceToEpoch #r0 #nonce h keys in // just coercion
        Epochs.add_epoch hs.epochs ep; // actually extending the epochs log
        Epochs.incr_reader hs.epochs;
        hs_state := C_Wait_Finished1;
        InAck true false
      end
    | TLS_1p3, _, _, _ -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Unsupported group negotiated")
    | _, _, _, _ -> (* commit to TLS classic *)
      begin
        hs_state := C_Wait_ServerHelloDone;
        InAck false false
      end

(* receive Certificate...ServerHelloDone, with optional cert request. Not for TLS 1.3 *)
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
                   // debug_print("tbs = " ^ (Platform.Bytes.print_bytes tbs) ^ "\n");
                   debug_print("Signature validation status = " ^ (if valid then "OK" else "FAIL") ^ "\n");
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
                       let cfin_key, app_keys = KeySchedule.ks_12_get_keys hs.ks  in
                       let ep = 
                         let h = Negotiation.Fresh ({session_nego = n}) in
                         Epochs.recordInstanceToEpoch h keys in
                       Epochs.add_epoch hs.epochs ep;

                       (* will send CCS then encrypted Finished *)
                       let cvd = MAC.mac cfin_key digestClientKeyExchange in // or use the latest digest in case we client-sign
                       let digestClientFinished = Handshake.Log.send_CCS_tag (Finished ({fin_vd = cvd})) in
                       hs.state := C_Wait_CCS2 digestClientFinished;                       
                       InAck false false )


(* receive EncryptedExtension...ServerFinished for TLS 1.3, roughly mirroring client_ServerHelloDone *)
let client_ServerFinished_13 hs ee ocr c cv svd digestCert digestCertVerify digestServerFinished =
    match Nego.clientComplete_13 hs.nego ee ocr c cv digestCert with 
    (* here are the checks we were doing before; now hopefully in Nego:
    let valid_chain = cfg.check_peer_certificate => Cert.validate_chain c.crt_chain true cfg.peer_name cfg.ca_file in
    if not valid_chain then Error (AD_decode_error, "Certificate was not valid")
    else
    begin
       let Some cs_sigalg = n.n_sigAlg in
       let Some algs = n.n_extensions.ne_signature_algorithms in
       debug_print("cv_sig = " ^ (Platform.Bytes.print_bytes cv.cv_sig) ^ "\n");
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
             debug_print("Signature validation status = " ^ (if valid then "OK" else "FAIL") ^ "\n");
             if not valid then Error (AD_decode_error, "Certificate signature did not verify")
             else  *)
    | Error z -> Error z 
    | Correct full_mode -> 
        let (cfin_key, sfin_key, app_keys) = KeySchedule.ks_client_13_server_finished hs.ks in
        // was also calling: let keys = KeySchedule.ks_client_13_sf ks in
        // was also calling: let cvd = KeySchedule.ks_client_13_client_finished ks in
        // was also calling: let ems = KeySchedule.ks_client_13_cf ks in // ?
  
        if not (MAC.verify sfin_key digestCertVerify svd) 
        then Error (AD_decode_error, "Finished MAC did not verify")
        else (
          let digest =
            match ocr with
            | Some cr -> Handshake.Log.send_tag (Certificate ({crt_chain = []}))
            | None -> digestServerFinished in
          let cvd = MAC.mac cfin_key digest in
          Handshake.Log.send (Finished ({fin_vd = cvd}));
          let ep =
            let h = Negotiation.Fresh ({session_nego = full_mode}) in // review index?
            Epochs.recordInstanceToEpoch #r0 #id h app_keys in
          Epochs.add_epoch hs.epochs ep;
          Epochs.incr_reader hs.epochs;
          Epochs.incr_writer hs.epochs; // TODO update writer key properly
          hs.state := C_Complete; // full_mode (cvd,svd); do we still need to keep those?
          InAck true true )


(* -------------------- Handshake Server ------------------------ *)

(* called by server_ClientHello after sending TLS 1.2 ServerHello *) 
let server_ServerHelloDone hs n =
    // static precondition: n.n_protocol_version <> TLS_1p3 && Some? n.n_sigAlg && (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)
    // should instead use Nego for most of this processing
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
              begin
                lemma_repr_bytes_values (length sigv);
                let signature = (hab @| sab @| (vlbytes 2 sigv)) in
                let ske = {ske_kex_s = kex_s; ske_sig = signature} in
                Handshake.Log.send hs.log (Certificate c);
                Handshake.Log.send hs.log (ServerKeyExchange ske);
                Handshake.Log.send hs.log ServerHelloDone;
                s.state := S_SentCCS n
                // TODO: signal send_CCS and next _keys
              end
      end

(* receive ClientHello, and choose a protocol version and mode *) 
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
      match Extensions.negotiateServerExtensions mode.sm_protocol_version ch.ch_extensions ch.ch_cipher_suites cfg mode.sm_cipher_suite ri ksl false with
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

          if mode.sm_protocol_version = TLS_1p3 
          then (
            let keys = KeySchedule.ks_server_13_sh ks in
            let ep = 
              let h = Negotiation.Fresh ({session_nego = n}) in
              Epochs.recordInstanceToEpoch #r0 #id h ri in
           // Do not increment writer yet as the SH is sent in plaintext
            Epochs.add_epoch lgref ep; 
            hs.state := S_Sent_ServerHello n;
            InAck false false)

          else server_ServerHelloDon hs nego // sending our whole flight hopefully in a single packet. 
          ))

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
          hs.state := S_Wait_Finished1 n digest; // keep digest to verify the Client Finished
          InAck true false )

(* receive ClientFinish *) 
let server_ClientFinished hs digestCCS digestClientFinished =
    // to be adjusted
    let cvd = KeySchedule.ks_server_12_client_finished ks in
    if not (equalBytes cvd f.fin_vd) then Error (AD_decode_error, "Finished MAC did not verify")
    else (
        // TODO we *first* need to send CCS
        let svd = KeySchedule.ks_server_12_server_finished ks in
        Handshake.Log.send (Finished ({fin_vd = svd})); 
        InAck false false )

(* send EncryptedExtensions; Certificate; CertificateVerify; Finish (1.3) *)
val server_send_server_finished_13: hs -> i:id -> ST (result (Outgoing i))
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))
let server_ServerFinished_13 hs n = 
    // static pre: n.n_protocol_version = TLS_1p3 && Some? n.n_sigAlg && (n.n_kexAlg = Kex_DHE || n.n_kexAlg = Kex_ECDHE)
    // most of this should go to Nego
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
            hs.state := S_Wait_Finished2;
            Handshake.Log.set_flags "switch to ATK 0.5RTT" 
            Correct(Handshake.Log.next_fragment hs.log i)
            )
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
          hs.state := Complete;
          InAck true false  (*?*)  )

(* TODO: resumption *)
assume val server_send_server_finished_res: hs -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

(* Handshake API: PUBLIC Functions, taken from FSTI *)

// returns the protocol version negotiated so far
// (used for formatting outgoing packets, but not trusted)
val version: s:hs -> Tot protocolVersion
  (requires (hs_inv s))
  (ensures (fun h0 pv h1 -> h0 = h1))
let version s = Nego.version s.nego 

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
val create: r0:rid -> cfg:TLSInfo.config -> r:role -> resume:TLSInfo.resumeInfo r -> ST hs
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion r0 (HS?.region s) h0 h1 /\
    hs_inv s h1 /\
    HS?.r s = r /\
    HS?.resume s = resume /\
    HS?.cfg s = cfg /\
    logT s h1 = Seq.createEmpty ))
let handshake_state_init r0 cfg (r:role) (resume:rid) =
  let nego = Nego.create #reg r cfg resume in
  let log = HandshakeLog.create #reg (Nego.hashAlg nego) in 
  //let nonce = Nonce.mkHelloRandom r r0 in //NS: should this really be Client?
  let ks, nonce = KeySchedule.create #reg r log in
  let epochs = Epochs.create reg nonce in 
  let state = ralloc (if r = Client then C_Idle else S_Idle) in
  HS #r0 r nonce nego log ks epochs state


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


(* Outgoing *)

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

val next_fragment: hs -> i:id -> ST (result (outgoing i))
  (requires (fun h0 ->
    let es = logT s h0 in
    let j = iT s Writer h0 in
    hs_inv s h0 /\
    (if j = -1 then PlaintextID? i else let e = Seq.index es j in i = epoch_id e)
  ))
  (ensures (next_fragment_ensures s))
let next_fragment hs i =
    let outgoing = Handshake.Log.next_fragment hs.log i in
    match !hs.state with 
    | C_Idle when outgoing = Outgoing None false false false -> client_ClientHello hs i
    | S_HelloSent when outgoing = Outgoing None false false false -> server_ServerFinished_13 hs i
    | _ -> Correct outgoing // nothing to do
    
    // not needed anymore?
        (* // *)

        (* | C_Sent_CCS1 tag -> ( *)
        (*       // was: client_send_client_finished hs; *)
        (*       // we could store the MAC in OutCCS, to make this step trivial *)
        (*       let tag = KeySchedule.ks_client_12_client_finished hs.ks in *)
        (*       Handshake.Log.send hs.log (Finished ({fin_vd = tag})); *)
        (*       hs.state := C_FinishedSent n tag *)
        (*       Epochs.incr_writer lgref; *)
        (*       Outgoing None true true false ) *)

        (* | _ -> Correct outgoing // nothing to do *)

        //| C_FinishedReceived n (cvd,svd) ->
        //    hsref := {!hsref with hs_state = C (C_PostHS)};
        //    Epochs.incr_writer lgref; // Switch to ATK writer
        //    Outgoing None false true true
        //
        //| S_HelloSent n when (Some? pv && pv <> Some TLS_1p3 && res = Some false) ->
        //    server_ServerHelloDone hs n;
        //    next_fragment i hs
        // | S_Sent_ServerHello when (Some? pv && pv <> Some TLS_1p3 && res = Some true) ->
        //      server_send_server_finished_res hs;
        //      next_fragment i hs
        
        //| S_FinishedReceived n ->
        //      Epochs.incr_reader lgref; // Switch to ATK reader
        //      hs.state := S_PostHS;
        //      Outgoing None false true true
        //| S_OutCCS n ->
        //      hs.state := S_FinishedSent n  // who actually sends the ServerFinished? buffered?
        //      Outgoing None false false true
        //| _ -> Outgoing None false false false)
    

(* Incoming *)

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

val recv_fragment: s:hs -> #i:id -> message i -> ST incoming (* incoming transitions for our state machine *) 
  (requires (hs_inv s))
  (ensures (recv_ensures s))
let recv_fragment hs #i f =
    let flight = Handshake.Log.receive hs.log f in 
    match !hs.state, flight with 
      | _, None -> InAck false false // nothing happened
      
      | C_Idle, _ -> Error (AD_unexpected_message, "Client hasn't sent hello yet")
      | C_Wait_ServerHello, Some ([ServerHello sh], [digest]) -> client_ServerHello sh digest
      | C_Wait_ServerHelloDone n, Some ([Certificate c; ServerKeyExchange ske; ServerHelloDone], [unused_digestCert]) ->
          // assert (Some? pv && pv <> Some TLS_1p3 && res = Some false && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) 
          client_ServerHelloDone hs c ske None

      | C_Wait_ServerHelloDone n, Some ([Certificate c; ServerKeyExchange ske; CertificateRequest cr; ServerHelloDone], [unused_digestCert]) ->
          // assert (Some? pv && pv <> Some TLS_1p3 && res = Some false && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) 
          client_ServerHelloDone hs c ske (Some cr)

      | C_Wait_Finished1, Some ([EncryptedExtensions ee; Certificate c; CertificateVerify cv; Finished f], [digestCert; digestCertVerify; digestServerFinished]) ->
          // assert (Some? pv && pv = Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) 
          client_ServerFinished_13 hs ee None c cv f.fin_vd digestCert digestCertVerify digestServerFinished

      | C_Wait_Finished1, Some ([EncryptedExtensions ee; CertificateRequest cr; Certificate c; CertificateVerify cv; Finished f], [digestCert; digestCertVerify; digestServerFinished]) ->
          // assert (Some? pv && pv = Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE));
          client_ServerFinished_13 hs ee (Some cr) c cv f.fin_vd digestCert digestCertVerify digestServerFinished

      // we'll have other variants for resumption, shc as ([EncryptedExtensions ee; Finished f], [...]) 

      | C_Wait_Finished2 digest, Some ([Finished f], [digestServerFinished]) ->
          // assert Some? pv && pv <> Some TLS_1p3 
          let sfin_key = KeySchedule.ks_client_12_server_finished ks digest in 
          if not (MAC.verify sfin_key digest f.fin_vd) then Error (AD_decode_error, "Finished MAC did not verify") 
          else (
            hs.state := C_Complete; // ADL: TODO need a proper renego state Idle (Some (vd,svd)))};
            Correct (InAck false true))

      //17-03-24 how to receive binders? we need the intermediate hash 
      | S_Idle ri, Some ([ClientHello ch], [])  -> server_ClientHello hs ch
      | S_Wait_Finished1 s digest, Some ([Finished f], [digestClientFinish]) -> 
          server_ClientFinished hs f digest digestClientFinish

      | S_Wait_Finished2 s, Some ([Finished f], [digest]) -> server_ClientFinished_13 hs s f digest None 
      | S_Wait_Finished2 s, Some ([Certificate c; CertificateVerify cv; Finished f], [digestSigned; digestClientFinished; _]) ->
          server_ClientFinished_13 hs s f digestClientFinished (Some (c,cv,digestSigned))  

       // are we missing the case with a Certificate but no CertificateVerify? 

      | _, _ -> InAck false false // nothing yet to process


// special case: CCS before 1p3; could merge with recv_fragment
val recv_ccs: s:hs -> ST incoming  
  (requires (hs_inv s)) // could require pv <= 1p2
  (ensures (fun h0 result h1 ->
    recv_ensures s h0 result h1 /\
    (Error? result \/ result = Correct(InAck true false))
    ))
let recv_ccs hs =
    debug_print "CALL recv_ccs\n";
    // assert pv <> TLS 1.3
    // CCS triggers completion of the incoming flight of messages.
    match Handshake.Log.receive_CCS hs.log with
    | Error -> InError(AD_unexpected_message, "CCS received at wrong time")
    | Correct (ms, hs, digest) -> 
        match !hs.state, ms, hs with 
        | C_Wait_CCS2 digest, ([], []) -> (
            // we now expect the encrypted server finish, should keep the digest to verify it
            hs.state := C_CCSReceived digest;
            Epochs.incr_reader hs.epochs;
            InAck true false )

        | C_Wait_CCS2 digest, ([SessionTicket st], []) -> (
            debug_print "WARNING: no support for session tickets";
            // we now expect the encrypted server finish, should keep the digest to verify it
            hs.state := C_CCSReceived digest;
            Epochs.incr_reader hs.epochs;
            InAck true false )

        | S_Wait_CCS1, ([ClientKeyExchange cke], []) ->
            // assert (Some? pv && pv <> Some TLS_1p3 && (kex = Some Kex_DHE || kex = Some Kex_ECDHE)) 
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
        | _, _ -> Error(AD_unexpected_message, "CCS received at wrong time")


val authorize: s:hs -> Cert.chain -> ST incoming // special case: explicit authorize (needed?)
  (requires (hs_inv s))
  (ensures (fun h0 result h1 ->
    (InAck? result \/ InError? result) /\ recv_ensures s h0 result h1 ))
let authorize s ch = Platform.Error.unexpected "authorize: not yet implemented"
