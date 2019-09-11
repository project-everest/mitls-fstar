module Test.TLS.Send

module HS = FStar.HyperStack
module HSM = HandshakeMessages
module Nego = Negotiation
module HST = FStar.HyperStack.ST
module Send = TLS.Handshake.Send
module B = LowStar.Buffer

module Transcript = HSL.Transcript
module CHE = Parsers.ClientHelloExtension
module CHEs = Parsers.ClientHelloExtensions

open FStar.Integers
open FStar.HyperStack.ST
open CipherSuite
open TLSError

// TODO may require switching from Tot to Stack
assume val trace: string -> unit

noeq type handshake = | HS:
  #region: Mem.rgn {Mem.is_hs_rgn region} ->
  r: TLSConstants.role ->
  // nego: Nego.t region r ->
  #a: EverCrypt.Hash.alg ->
  stt: Send.transcript_state a ->
  #n: Ghost.erased nat ->                 // Length of the current transcript
  t:Transcript.g_transcript_n n ->                // Ghost transcript
  sto:Send.send_state ->
//  log: HandshakeLog.t {HandshakeLog.region_of log = region} ->
//  ks: KeySchedule.ks (*region*) ->
//  epochs: epochs region (Nego.nonce nego) ->
//  state: ref machineState {HS.frameOf state = region} -> // state machine; should be opaque and depend on r.
  handshake

let invariant (hs:handshake) (h:HS.mem) =
  Send.invariant hs.sto h /\
  Transcript.invariant hs.stt (Ghost.reveal hs.t) h /\
  B.loc_disjoint (Send.footprint hs.sto) (Transcript.footprint hs.stt) 
//  Nego.inv hs.nego h /\
//  B.loc_disjoint (Send.footprint hs.sto) (Nego.footprint hs.nego) /\
//  B.loc_disjoint (Transcript.footprint hs.stt) (Nego.footprint hs.nego)

let footprint (hs:handshake) =
  Send.footprint hs.sto `B.loc_union`
  Transcript.footprint hs.stt 
//`B.loc_union` Nego.footprint hs.nego

let is_state13 (hs:handshake) = Transcript.Transcript13? (Ghost.reveal hs.t)

// TODO: Should be computed using key schedule
assume val svd:HSM.handshake13_m13_finished
//TODO: Should be computed from nego + certificate13 parsers
assume val cert:HSM.handshake13_m13_certificate
// TODO: Should be computed from nego. Requires lowering to take hash instead of bytes?
assume val signature:HSM.handshake13_m13_certificate_verify

// TODO: should tag be allocated inside of a function? on the stack?

val serverFinished: hs:handshake -> tag:Hacl.Hash.Definitions.hash_t (hs.a) -> ST (result handshake)
    (requires fun h -> invariant hs h /\ B.live h tag /\ is_state13 hs /\
      Ghost.reveal hs.n < Transcript.max_transcript_size - 4 /\
      B.loc_disjoint (B.loc_buffer tag) (B.loc_region_only true Mem.tls_tables_region) /\
      B.loc_disjoint (B.loc_buffer tag) (footprint hs))
    (ensures fun h0 res h1 -> 
      B.(modifies (footprint hs `loc_union` loc_buffer tag `loc_union` loc_region_only true Mem.tls_tables_region)) h0 h1 /\
      begin match res with
      | Correct hs' -> invariant hs' h1
      | _ -> True
      end
    )

#set-options "--z3rlimit 50"

let serverFinished hs tag =
    trace "prepare Server Finished";
//  let mode = Nego.getMode hs.nego in
//  let cfg = Nego.local_config hs.nego in
    let kex = admit() in // Nego.kexAlg mode in
//  let pv = admit() in //mode.Nego.n_protocol_version in
//  let cs = admit() in //mode.Nego.n_cipher_suite in
//  let exts = admit() in //mode.Nego.n_server_extensions in
    let eexts = admit() in //match mode.Nego.n_encrypted_extensions with | None -> [] | Some ee -> ee in

    let digestFinished : result handshake =
      match kex with
      | Kex_ECDHE -> // [Certificate; CertificateVerify]
        let m = HSM.M13_encrypted_extensions eexts in
        begin
        match Send.send13 hs.stt hs.t hs.sto m with
        | Correct (sto, t') ->
          // TODO: let cert = let Some (chain, _) = mode.n_server_cert in { certificate_list = chain; certificate_request_context = empty_bytes } in
          let m = HSM.M13_certificate cert in // AF suggests to have this whole message already as part of mode, instead of just chain
          begin
          match Send.send_tag13 hs.stt t' sto m tag with
          | Correct (sto, t') ->
            begin
            // TODO: let tbs = Nego.to_be_signed pv ... tag in let signature = Nego.sign hs.nego tbs in
            match Send.send_tag13 hs.stt t' sto (HSM.M13_certificate_verify signature) tag with
            | Correct (sto, t') -> Correct (HS #hs.region hs.r hs.stt t' sto)
            | Error z -> Error z
            end
          | Error z -> Error z
          end
        | Error z -> Error z
        end
      | _ -> // PSK
        let m = HSM.M13_encrypted_extensions eexts in
        match Send.send_tag13 hs.stt hs.t hs.sto m tag with
        | Correct (sto, t') -> 
          let h1 = get() in
          Correct (HS #hs.region hs.r hs.stt t' sto)
        | Error z -> Error z
    in
    match digestFinished with
    | Correct hs' ->
      // TODO: let svd = let (| _, sfin_key |) = KS.ks_server_13_server_finished hs.ks in HMAC_UFCMA.mac sfin_key tag in
      let m = HSM.M13_finished svd in
      begin
      match Send.send_tag13 hs'.stt hs'.t hs'.sto m tag with
      | Correct (sto, t') ->
        // TODO: export, register, send signals, nego state
        Correct (HS #hs.region hs.r hs.stt t' sto)
      | Error z -> Error z
      end
    | Error z -> Error z


val server_ClientHello: 
  #region: _ -> // ns: Nego.t region TLSConstants.Server ->
  out: Send.send_state ->
  Transcript.hs_ch -> 
  ST (result handshake)
  (requires fun h0 -> 
    Mem.is_hs_rgn region /\
//  Nego.inv ns h0 /\
    Send.invariant out h0 )
//  B.loc_disjoint (Send.footprint out) (Nego.footprint ns) /\
//    (let s = HS.sel h0 in Nego.S_Init? s)) // TODO:  \/ Nego.S_HRR? s
  (ensures fun h0 r h1 -> 
    B.modifies (Send.footprint out `B.loc_union` B.loc_region_only true Mem.tls_tables_region) h0 h1 /\
    begin match r with
    | Correct hs ->
      invariant hs h1 /\
      hs.region == region /\
      hs.r == TLSConstants.Server /\
      // hs.nego == ns /\
      Transcript.ClientHello? (Ghost.reveal hs.t)
      // TODO: /\ hs.t == ...
    |  _ -> True
    end
    )
  // [S_Init | S_HRR ==> S_ClientHello m cert] 
  // ensures r = computeServerMode ns.cfg ns.nonce offer (stateful)
  // but [compute_cs13] and [negotiateCipherSuite] are pure. 

// assume val computeServerMode: result Nego.serverMode
// assume val find_cookie: Nego.offer -> option Extensions.cookie 
// assume val serverMode_hashAlg: Nego.serverMode -> Tot Hashing.Spec.alg

(*
  cfg: TLSConstants.config ->
  co: TLSConstants.offer ->
  serverRandom: TLSInfo.random ->
  ST (result serverMode)
  (requires fun h0 -> True)
  (ensures fun h0 r h1 -> 
    B.(modifies loc_none h0 h1) /\ 
    ( match r with 
      | Correct (ServerRetry hrr) -> TLS.Cookie.hrr_len hrr <= 16 // leaving enough room for the cookie 
      | _ -> True )
    )
*)

// #reset-options "--using_facts_from '* -LowParse'"

#restart-solver

#push-options "--z3rlimit 1024 --max_ifuel 12 --initial_ifuel 12"

let server_ClientHello #region ns out offer =
// TODO: match !ns.Nego.state with  | Nego.S_HRR o1 hrr -> server_ClientHello2_stateful ns o1 hrr offer
//  | Nego.S_Init _ ->
  let r =
    let sm = computeServerMode in // ns.Nego.cfg offer ns.Nego.nonce in
    match sm with
    | Error z -> Error z
    | Correct r ->
      let alg = serverMode_hashAlg r in
      let hash_len = Hacl.Hash.Definitions.hash_len alg in
      let (ts, tr) = Transcript.create region alg in
      let stateless_retry = 
        match find_cookie (HSM.M_client_hello?._0 offer) with
        | None -> Correct (tr, None)
        | Some c ->
          // stateless HRR.
          match TLS.Cookie.decrypt c with
          | Error z -> 
            // This connection is doomed: we could instead return a fatal error. 
            Error z
          | Correct (digest, extra, hrr) ->
            // TODO check consistency of sm with hrr's cs and group;
            // this is required to enforce the earlier server policy.
            // Lowering: we use the output buffer as scratch space
            // for outputting the digest (of known size) and the hrr
            // (possibly quite large), since we only need them for
            // computing the transcript digest.
            begin match Send.send_hrr ts tr out (HSM.M_message_hash digest) (HSM.M_server_hello (HM.serverHello_of_hrr hrr)) with
            | Error z ->
              // serialization failure
              Error z
            | Correct (_, tr1) ->
              // we drop the updated output state, so that we can overwrite
              // the hrr in the remainder of the function
              Correct (tr1, Some extra) // to be passed to the server nego callback
            end
      in
      begin match stateless_retry with
      | Error z -> Error z
      | Correct (tr1, stateless_retry) ->
        begin match Send.send_ch ts tr1 out offer with
        | Error z -> Error z
        | Correct (_, tr2) ->
          begin match r with
          | Nego.ServerRetry hrr ->
            if Some? stateless_retry then
              fatal Handshake_failure "negotiation failed after a retry"
            else begin
              // Internal HRR caused by group negotiation
              // We do not invoke the server nego callback in this case
              // record the initial offer and return the HRR to HS
              // TODO: allocate on the stack or use out as scratch space for digest?
              push_frame ();
              let bmdigest = B.alloca 0uy 64ul in // constant size large enough to contain any digest
              let bdigest = B.sub bmdigest 0ul hash_len in
              assert (B.length bdigest == Spec.Hash.Definitions.hash_length alg);
              let ha = TLS.Cookie.hrr_ha hrr in
              // TODO create Transcript in state Start(Some(digest0,hrr)) to compute this digest
              // using ha instead of alg; what is digest0?
              Transcript.extract_hash ts bdigest tr2;
              // TODO: lower
              let digest = FStar.Bytes.of_buffer hash_len bdigest in
              assume (TLS.Cookie.hrr_len hrr <= 16);
              let hrr = TLS.Cookie.append digest FStar.Bytes.empty_bytes hrr in
//              ns.Nego.state := Nego.S_HRR (HSM.M_client_hello?._0 offer) hrr;
              let st = HS TLSConstants.Server ns ts tr2 out in
              pop_frame ();
              Correct (st, r)
            end
          | Nego.ServerMode m cert _ ->
            let nego_cb = ns.Nego.cfg.TLSConstants.nego_callback in
            let exts0 = (HSM.M_client_hello?._0 offer).CH.extensions in
            let exts : list CHE.clientHelloExtension = List.Tot.filter CHE.CHE_Unknown_extensionType? exts0 in
            LowParseWrappers.list_bytesize_filter CHE.clientHelloExtension_bytesize CHEs.clientHelloExtensions_list_bytesize () (fun _ _ -> ()) CHE.CHE_Unknown_extensionType? exts0;
            let exts_bytes = CHEs.clientHelloExtensions_serializer32 exts in
            let r = nego_cb.TLS.Callbacks.negotiate nego_cb.TLS.Callbacks.nego_context m.Nego.n_protocol_version exts_bytes stateless_retry in
            begin match r with
            | TLS.Callbacks.Nego_abort ->
              fatal Handshake_failure "application requested to abort the handshake."
            | TLS.Callbacks.Nego_retry filling ->
              assume(CipherSuite13? m.Nego.n_cipher_suite); // from ServerMode 
              let hrr = TLS.Cookie.hrr0 (HSM.M_client_hello?._0 offer).CH.session_id m.Nego.n_cipher_suite in
              // TODO: ha vs. alg
              let ha = TLS.Cookie.hrr_ha hrr in
              // TODO: allocate on the stack or use out as scratch space for digest?
              push_frame ();
              let bmdigest = B.alloca 0uy 64ul in // constant size large enough to contain any digest
              let bdigest = B.sub bmdigest 0ul hash_len in
              Transcript.extract_hash ts bdigest tr2;
              // TODO: lower
              let digest = FStar.Bytes.of_buffer hash_len bdigest in
              assume (TLS.Cookie.hrr_len hrr <= 16);
              let hrr = TLS.Cookie.append digest FStar.Bytes.empty_bytes hrr in
//              ns.Nego.state := Nego.S_HRR (HSM.M_client_hello?._0 offer) hrr;
              let st = HS TLSConstants.Server ns ts tr2 out in
              pop_frame ();
              Correct (st, Nego.ServerRetry hrr)
            | TLS.Callbacks.Nego_accept sexts ->
              ns.Nego.state := Nego.S_ClientHello m cert;
              let st = HS TLSConstants.Server ns ts tr2 out in
              Correct (st, Nego.ServerMode m cert sexts)
            end
          end
        end
      end
  in
  let h1 = HST.get () in
  assert (
    match r with
      | Correct (hs, sm) ->
        Send.invariant hs.sto h1
      | _ -> True
  );
  r

#pop-options
