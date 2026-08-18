module TLS13.System.SlotMono

(** SCRATCH module (de-risking the "flag excludes HsServerHelloSent" step).
    Goal: if the CLIENT has verified the server's Finished
    (`hs_server_finished_verified` = true), then the SERVER is NOT at
    `HsServerHelloSent`.

    Argument (mirrors ORD.lemma_inflight_sender_write_epoch_not_application_X):
      * flag true  ==> client has RECEIVED >= 4 protected records
        (field-keyed floor `client_recv_floor`, which — unlike the control-keyed
        `client_recv_potential` — SURVIVES a later fail into `ControlFailed`).
      * byte_pairing ==> raw_appdata_count(server.raw_sent)
                          >= raw_appdata_count(client.raw_received) >= 4.
      * a reachable server at `HsServerHelloSent` has SENT 0 protected records
        (`WStep.lemma_server_hsserverhellosent_sent_zero`).  0 >= 4 — false. **)

module CS    = TLS13.Spec.StateMachine
module SY    = TLS13.System
module MP    = Common.MachineProduct
module WStep = TLS13.System.WireStep
module SMR   = TLS13.Spec.StateMachine.Reachability
module CL    = TLS13.ConnectionLog
module B     = TLS13.Bytes
module Seq   = FStar.Seq
module SM    = Common.StateMachine
module CW    = TLS13.Spec.Endpoint.Wire
module CTy   = TLS13.Impl.CanonicalTypes
module EAPI  = TLS13.Spec.Endpoint.API
module EC    = TLS13.Spec.Endpoint.Client
module WFSM  = Common.WireFormatStateMachine
module WF    = Common.WireFormat
module PNTWL = TLS13.Impl.Driver.PairingNoTailWireLogs
module R     = TLS13.Record.Spec

(** The field-keyed client RECEIVE floor: once the client has verified the server
    Finished it has received at least ONE protected record; before that, the floor
    is the saturating-at-one `client_recv_min_potential`.  Being keyed on the
    persistent field `hs_server_finished_verified` (never cleared), the floor
    survives a later fail into `ControlFailed`, unlike any control-keyed count.

    ── WHY THE BOUND IS `1` AND NOT `4` ─────────────────────────────────────────
    This floor USED to read `if flag then 4 else client_recv_potential control`,
    i.e. "a client that verified the server Finished has received the whole
    FOUR-record protected server flight".  THAT IS NOW FALSE, and it was falsified
    by the internal-event (coalesced protected handshake) work, not by a proof
    problem here.  Do NOT assume `1` was always the natural bound.

    The witness: a SINGLE protected record carrying
    `EncryptedExtensions|Certificate|CertificateVerify|Finished` is delivered by
    one HEAD `ConnProtectedHandshake` step followed by three TAIL steps, and
    `CS.event_raw_delta_legal` charges a TAIL step `Seq.equal raw_received
    B.empty` -- zero bytes.  So the client reaches `hs_server_finished_verified`
    with `raw_appdata_count raw_received == 1`.

    `TLS13.System.WireStep` made the matching change upstream: its per-step client
    RECV lemma (`lemma_client_step_recv_potential`) is now stated over
    `client_recv_min_potential` (which saturates at 1) rather than the
    control-keyed `client_recv_potential`.  `client_recv_potential` survives as a
    MESSAGE count and is still used for the region-internal UPPER charge, but it
    is no longer a lower bound on RECORDS received.

    `1` is the strongest bound this technique can now support, and it is all the
    only consumer (`lemma_flag_excludes_server_hello_sent`, below) needs: it is
    contradicted against a server that has sent ZERO protected records. **)
let client_recv_floor (m:CS.connection_model) : nat =
  if m.CS.model_handshake.CS.hs_server_finished_verified
  then 1
  else WStep.client_recv_min_potential m

(** Model-level flag facts: a legal client step (a) never clears the verified
    flag, and (b) can only SET the flag fresh by moving to a control whose receive
    potential is already 4 (the two atomic server-Finished transitions land in
    `HsServerFinishedVerified`), which in particular has
    `client_recv_min_potential == 1`.

    Conjunct (b) is stated over the CONTROL potential and remains TRUE -- it is a
    statement about where the flag-setting transitions LAND, not about how many
    records were received to get there.  Conjunct (c) is the record-side fact the
    floor telescoping actually consumes. **)
#push-options "--fuel 2 --ifuel 5 --z3rlimit 40"
let lemma_client_flag_facts
  (m:CS.connection_model) (conn_ev:CS.conn_event) (m':CS.connection_model)
  : Lemma
      (requires
        CS.legal_event m conn_ev /\
        CS.step_model m conn_ev == Some m' /\
        m.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        (m.CS.model_handshake.CS.hs_server_finished_verified ==>
           m'.CS.model_handshake.CS.hs_server_finished_verified) /\
        ((~(m.CS.model_handshake.CS.hs_server_finished_verified) /\
          m'.CS.model_handshake.CS.hs_server_finished_verified) ==>
           WStep.client_recv_potential m'.CS.model_control >= 4) /\
        ((~(m.CS.model_handshake.CS.hs_server_finished_verified) /\
          m'.CS.model_handshake.CS.hs_server_finished_verified) ==>
           WStep.client_recv_min_potential m' >= 1))
  = ()
#pop-options

(** Client-step RECV floor fact, lifted to `client_step`: the wire-input appdata
    count plus the pre-step floor is at least the post-step floor. **)
#push-options "--fuel 2 --ifuel 3 --z3rlimit 40"
let lemma_client_step_recv_floor
  (st0:CS.connection_state)
  (ev:SM.event CW.wire_message CTy.client_local_event)
  (st1:CS.connection_state)
  (out:SM.step_output CW.wire_message EAPI.local_output)
  : Lemma
      (requires
        EC.client_step st0 ev st1 out /\
        st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
      (ensures
        WStep.list_appdata_count (WFSM.event_input_messages ev)
          + client_recv_floor st0.CS.cs_model
          >= client_recv_floor st1.CS.cs_model)
  = WStep.lemma_client_step_recv_potential st0 ev st1 out;
    WStep.lemma_client_step_model_stepped st0 ev st1 out;
    eliminate exists (conn_ev:CS.conn_event).
      CS.legal_event st0.CS.cs_model conn_ev /\
      CS.step_model st0.CS.cs_model conn_ev == Some st1.CS.cs_model
    with
      lemma_client_flag_facts st0.CS.cs_model conn_ev st1.CS.cs_model
#pop-options

(** Trace-level client RECV floor telescoping. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let rec lemma_client_trace_recv_floor
  (init st0 st1:CS.connection_state)
  (trace:list (SM.transition CS.connection_state CW.wire_message
                 CTy.client_local_event EAPI.local_output))
  : Lemma (requires
            SM.trace_reaches (WStep.client_sm init) st0 trace st1 /\
            st0.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint)
          (ensures
            WStep.list_appdata_count (WFSM.trace_input_messages trace)
              + client_recv_floor st0.CS.cs_model
              >= client_recv_floor st1.CS.cs_model)
          (decreases trace)
  = match trace with
    | [] -> ()
    | tr :: rest ->
      let s' = tr.SM.tr_next_state in
      assert (EC.client_step st0 tr.SM.tr_event s' tr.SM.tr_output);
      WStep.lemma_client_step_preserves_config st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_step_recv_floor st0 tr.SM.tr_event s' tr.SM.tr_output;
      lemma_client_trace_recv_floor init s' st1 rest;
      WStep.lemma_list_appdata_count_append
        (WFSM.event_input_messages tr.SM.tr_event)
        (WFSM.trace_input_messages rest)
#pop-options

(** A reachable client that has VERIFIED the server Finished has RECEIVED at least
    ONE ApplicationData-typed record.

    ── THIS LEMMA USED TO SAY `>= 4`, AND THAT IS NOW FALSE ─────────────────────
    See the `client_recv_floor` comment above for the falsifying witness: a single
    protected record carrying `EncryptedExtensions|Certificate|CertificateVerify|
    Finished` is drained by one HEAD plus three TAIL `ConnProtectedHandshake`
    steps, and `CS.event_raw_delta_legal` charges a TAIL step ZERO received bytes.
    Such a client reaches `hs_server_finished_verified` having received exactly
    ONE record.  `1` is the strongest true bound; do not read it as the bound this
    argument "naturally" gives. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_flag_recv_ge1
  (cfg:CS.connection_config)
  (client:CS.connection_state)
  : Lemma (requires
            WStep.client_reachable (CS.initial cfg) client /\
            client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures WStep.raw_appdata_count client.CS.cs_wire_log.CL.raw_received >= 1)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = WStep.client_sm init in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    with
    (
      lemma_client_trace_recv_floor init init client trace;
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (client_recv_floor init.CS.cs_model == 0);
      assert (Seq.equal (B.append init.CS.cs_wire_log.CL.raw_received sm_bytes) sm_bytes);
      assert (Seq.equal client.CS.cs_wire_log.CL.raw_received sm_bytes);
      WStep.lemma_raw_appdata_count_serialize_all in_msgs;
      WStep.lemma_raw_appdata_count_seq_equal client.CS.cs_wire_log.CL.raw_received sm_bytes
    )
#pop-options

(** A reachable client's received log is record-aligned, so appending in-flight
    bytes on the right never decreases its ApplicationData-record count. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_client_received_count_append_ge
  (cfg:CS.connection_config) (client:CS.connection_state) (extra:B.bytes)
  : Lemma (requires
            WStep.client_reachable (CS.initial cfg) client /\
            cfg.CS.config_role == CS.ClientEndpoint)
          (ensures
            WStep.raw_appdata_count
              (B.append client.CS.cs_wire_log.CL.raw_received extra)
              >= WStep.raw_appdata_count client.CS.cs_wire_log.CL.raw_received)
  = let init : EC.client_initial_state = CS.initial cfg in
    let sm = WStep.client_sm init in
    let cr = client.CS.cs_wire_log.CL.raw_received in
    eliminate exists (trace:list (SM.transition CS.connection_state CW.wire_message
                                    CTy.client_local_event EAPI.local_output)).
      SM.trace_reaches sm init trace client
    with
    (
      PNTWL.lemma_client_trace_wire_logs_match init init trace client;
      let in_msgs = WFSM.trace_input_messages trace in
      let sm_bytes = WF.serialize_all CW.tls_record_wire_format in_msgs in
      assert (init.CS.cs_wire_log.CL.raw_received == B.empty);
      assert (Seq.equal cr sm_bytes);
      assert (Seq.equal (B.append cr extra) (B.append sm_bytes extra));
      PNTWL.lemma_wire_parse_serialize_all_inverse in_msgs;
      WStep.lemma_raw_appdata_count_append sm_bytes extra in_msgs;
      WStep.lemma_raw_appdata_count_seq_equal cr sm_bytes;
      WStep.lemma_raw_appdata_count_seq_equal (B.append cr extra) (B.append sm_bytes extra)
    )
#pop-options

(** ═══════════════════════════════════════════════════════════════════════════
    THE TARGET LEMMA. **)
#push-options "--fuel 1 --ifuel 2 --z3rlimit 40"
let lemma_flag_excludes_server_hello_sent (a:SY.tls_system_state)
  : Lemma
      (requires
        SY.tls_system_inv a /\
        a.MP.client.CS.cs_model.CS.model_handshake.CS.hs_server_finished_verified)
      (ensures
        a.MP.server.CS.cs_model.CS.model_control
          =!= CS.ControlHandshaking CS.HsServerHelloSent)
  = // Pull the conjuncts we need out of the (transparent) system invariant.
    assert (SY.byte_pairing a);
    assert (SY.client_byte_reachable a);
    assert (SY.server_byte_reachable a);
    assert (a.MP.client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint);
    assert (a.MP.server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
    // Client side: the verified flag forces >= 1 received protected record.
    // (This was `>= 4` before the coalesced-protected-flight spec change; `1` is
    // now the strongest true bound, and it is all this contradiction needs,
    // because the server side below gives exactly ZERO.)
    lemma_client_flag_recv_ge1 a.MP.client.CS.cs_model.CS.model_config a.MP.client;
    // Server side: if the server were at HsServerHelloSent it would have SENT 0,
    // contradicting the byte-pairing lower bound.
    introduce
      a.MP.server.CS.cs_model.CS.model_control
        == CS.ControlHandshaking CS.HsServerHelloSent ==> False
    with
    (
      WStep.lemma_server_hsserverhellosent_sent_zero
        a.MP.server.CS.cs_model.CS.model_config a.MP.server;
      // byte_pairing relates server.raw_sent and client.raw_received.
      let ss = a.MP.server.CS.cs_wire_log.CL.raw_sent in
      let cr = a.MP.client.CS.cs_wire_log.CL.raw_received in
      match a.MP.channel with
      | MP.Quiet ->
        WStep.lemma_raw_appdata_count_seq_equal ss cr
      | MP.ToServer p ->
        WStep.lemma_raw_appdata_count_seq_equal ss cr
      | MP.ToClient p ->
        lemma_client_received_count_append_ge
          a.MP.client.CS.cs_model.CS.model_config a.MP.client p.SY.pl_raw;
        WStep.lemma_raw_appdata_count_seq_equal ss (B.append cr p.SY.pl_raw)
    )
#pop-options
