module Test.TLS.Send

module HS = FStar.HyperStack
module Nego = Negotiation
module HST = FStar.HyperStack.ST
module TS = TLS.Handshake.Send
module T = HSL.Transcript
module B = LowStar.Buffer

module HSM = Parsers.Handshake
module HSM12 = Parsers.Handshake12
module HSM13 = Parsers.Handshake13


open FStar.Integers
open FStar.HyperStack.ST
open CipherSuite
open TLSError

// TODO may require switching from Tot to Stack
assume val trace: string -> unit

noeq type handshake = | HS:
  #region: Mem.rgn {Mem.is_hs_rgn region} ->
  r: TLSConstants.role ->
  nego: Nego.t region r ->
  #a: EverCrypt.Hash.alg ->
  stt: TS.transcript_state a ->
  #n: Ghost.erased nat ->                 // Length of the current transcript
  t:T.g_transcript_n n ->                // Ghost transcript
  sto:TS.send_state ->
//  log: HandshakeLog.t {HandshakeLog.region_of log = region} ->
//  ks: KeySchedule.ks (*region*) ->
//  epochs: epochs region (Nego.nonce nego) ->
//  state: ref machineState {HS.frameOf state = region} -> // state machine; should be opaque and depend on r.
  handshake

let valid (hs:handshake) (h:HS.mem) =
  TS.invariant hs.sto h /\
  T.invariant hs.stt (Ghost.reveal hs.t) h /\
  h `HS.contains` hs.nego.Nego.state /\
  B.loc_disjoint (TS.footprint hs.sto) (T.footprint hs.stt) /\
  B.loc_disjoint (TS.footprint hs.sto) (B.loc_mreference hs.nego.Nego.state) /\
  B.loc_disjoint (T.footprint hs.stt) (B.loc_mreference hs.nego.Nego.state)

let footprint (hs:handshake) =
  TS.footprint hs.sto `B.loc_union`
  T.footprint hs.stt `B.loc_union` 
  B.loc_mreference hs.nego.Nego.state

let is_state13 (hs:handshake) = T.Transcript13? (Ghost.reveal hs.t)

// TODO: Should be computed using key schedule
assume val svd:HSM13.handshake13_m13_finished
//TODO: Should be computed from nego + certificate13 parsers
assume val cert:HSM13.handshake13_m13_certificate
// TODO: Should be computed from nego. Requires lowering to take hash instead of bytes?
assume val signature:HSM13.handshake13_m13_certificate_verify

val serverFinished: hs:handshake -> tag:Hacl.Hash.Definitions.hash_t (hs.a) -> ST (result handshake)
    (requires fun h -> valid hs h /\ B.live h tag /\ is_state13 hs /\
      Ghost.reveal hs.n < T.max_transcript_size - 4 /\
      B.loc_disjoint (B.loc_buffer tag) (B.loc_region_only true Mem.tls_tables_region) /\
      B.loc_disjoint (B.loc_buffer tag) (footprint hs))
    (ensures fun h0 res h1 -> 
      B.(modifies (footprint hs `loc_union` loc_buffer tag `loc_union` loc_region_only true Mem.tls_tables_region)) h0 h1 /\
      begin match res with
      | Correct hs' -> valid hs' h1
      | _ -> True
      end
    )

#set-options "--z3rlimit 50"

let serverFinished hs tag =
    trace "prepare Server Finished";
    let mode = Nego.getMode hs.nego in
    let cfg = Nego.local_config hs.nego in
    let kex = Nego.kexAlg mode in
    let pv = mode.Nego.n_protocol_version in
    let cs = mode.Nego.n_cipher_suite in
    let exts = mode.Nego.n_server_extensions in
    let eexts = match mode.Nego.n_encrypted_extensions with | None -> [] | Some ee -> ee in

    let digestFinished : result handshake =
      match kex with
      | Kex_ECDHE -> // [Certificate; CertificateVerify]
        let m = HSM13.M13_encrypted_extensions eexts in
        begin
        match TS.send13 hs.stt hs.t hs.sto m with
        | Correct (sto, t') ->
          let m = HSM13.M13_certificate cert in
          begin
          match TS.send_tag13 hs.stt t' sto m tag with
          | Correct (sto, t') ->
            begin
            match TS.send_tag13 hs.stt t' sto (HSM13.M13_certificate_verify signature) tag with
            | Correct (sto, t') -> Correct (HS hs.r hs.nego hs.stt t' sto)
            | Error z -> Error z
            end
          | Error z -> Error z
          end
        | Error z -> Error z
        end
      | _ -> // PSK
        let m = HSM13.M13_encrypted_extensions eexts in
        match TS.send_tag13 hs.stt hs.t hs.sto m tag with
        | Correct (sto, t') -> 
          let h1 = get() in
          Correct (HS hs.r hs.nego hs.stt t' sto)
        | Error z -> Error z
    in
    match digestFinished with
    | Correct hs' ->
      let m = HSM13.M13_finished svd in
      begin
      match TS.send_tag13 hs'.stt hs'.t hs'.sto m tag with
      | Correct (sto, t') ->
        // TODO: export, register, send signals, nego state
        Correct (HS hs.r hs.nego hs.stt t' sto)
      | Error z -> Error z
      end
    | Error z -> Error z
