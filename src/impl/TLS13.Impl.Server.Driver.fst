module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module CPI = Common.ProtocolImplementation
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Impl.CanonicalWire
module A = Pulse.Lib.Array
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CL = TLS13.ConnectionLog
module CT = TLS13.Impl.Client.Types
module Crypto = TLS13.Crypto
module CryptoSpec = TLS13.Crypto.Spec
module CS = TLS13.Spec.ConnectionState
module CSL = TLS13.ConnectionState.Lemmas
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CQ = TLS13.Impl.ConnectionState.Queries
module ID = FStar.IndefiniteDescription
module IM = TLS13.Impl.Messages
module IO = Common.TCP
module Mat = TLS13.Impl.Server.Material
module M = TLS13.Messages
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module S = TLS13.Impl.Server
module DS = TLS13.Impl.Server.Driver.State
module DT = TLS13.Impl.Server.Driver.Transport
module DN = TLS13.Impl.Server.Driver.Network
module DL = TLS13.Impl.Server.Driver.Local
module DH = TLS13.Impl.Server.Driver.Handshake
module SQueries = TLS13.Impl.Server.CanonicalQueries
module EP = TLS13.Impl.Server.Endpoint
module SSetup = TLS13.Impl.Server.Setup
module ST = TLS13.Impl.Server.Types
module Tags = TLS13.Impl.ConnectionState.Tags
module Box = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module RS = TLS13.Record.Spec
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec
module W = TLS13.Wire.Spec
module SP = TLS13.Impl.Server.CanonicalProtocol
module WFSM = Common.WireFormatStateMachine
module SS = TLS13.Impl.Server.Send
module GSHbody = TLS13.Wire.Generated.ServerHello_body

type server_driver = DS.server_driver

noextract
let server_driver_canonical = DS.server_driver_canonical

noextract
let server_driver_canonical_progress = DS.server_driver_canonical_progress

noextract
let server_driver_endpoint_config = DS.server_driver_endpoint_config

noextract
let server_driver_endpoint_frame = DS.server_driver_endpoint_frame

noextract
let server_driver_endpoint_workflow_frame
  (d: server_driver)
  (certificate_chain_len: SZ.t)
  (certificate_chain_len_proof:
    (certificate_chain:Ghost.erased B.bytes ->
      Ghost.erased
        (SZ.v certificate_chain_len == B.length (Ghost.reveal certificate_chain))))
  (certificate_chain_len_bound:
    Ghost.erased
      (SZ.v certificate_chain_len <= Bounds.max_server_certificate_chain_len))
  (material_spec: Ghost.erased EP.server_endpoint_material_spec)
  (private_key: V.vec U8.t)
  (material_deferred_ready:
    (st:Ghost.erased CS.connection_state ->
    action:SQueries.server_deferred_action ->
      Ghost.erased
        (SQueries.server_deferred_action_ready (Ghost.reveal st) action ==>
         EP.server_endpoint_material_bytes_match_state
           (Ghost.reveal material_spec)
           (Ghost.reveal st))))
  : f:EP.server_endpoint_frame{
      f.EP.server_ep_query.SQueries.server_query_network_app_out ==
        V.vec_to_array d.server_driver_app_out /\
      SZ.v f.EP.server_ep_query.SQueries.server_query_network_app_out_len ==
        SZ.v DS.driver_app_out_capacity /\
      f.EP.server_ep_query.SQueries.server_query_local_payload ==
        V.vec_to_array d.server_driver_empty_payload /\
      SZ.v f.EP.server_ep_query.SQueries.server_query_local_payload_len == 0 /\
      f.EP.server_ep_query.SQueries.server_query_local_app_out ==
        V.vec_to_array d.server_driver_local_app_out /\
      SZ.v f.EP.server_ep_query.SQueries.server_query_local_app_out_len ==
        SZ.v DS.driver_app_out_capacity /\
      f.EP.server_ep_raw == d.server_driver_raw /\
      SZ.v f.EP.server_ep_raw_len == SZ.v DS.driver_rx_capacity /\
      f.EP.server_ep_network_out == d.server_driver_network_out /\
      SZ.v f.EP.server_ep_network_out_len == SZ.v DS.driver_network_out_capacity /\
      f.EP.server_ep_material == d.server_driver_material_payload /\
      SZ.v f.EP.server_ep_material_len == SZ.v DS.driver_material_capacity /\
      f.EP.server_ep_material_spec == material_spec /\
      f.EP.server_ep_private == private_key} =
  server_driver_endpoint_frame
    d
    (V.vec_to_array d.server_driver_app_out)
    DS.driver_app_out_capacity
    (V.vec_to_array d.server_driver_empty_payload)
    0sz
    (V.vec_to_array d.server_driver_local_app_out)
    DS.driver_app_out_capacity
    certificate_chain_len
    certificate_chain_len_proof
    certificate_chain_len_bound
    material_spec
    private_key
    material_deferred_ready

noextract
let server_driver_wire_logs_match = DS.server_driver_wire_logs_match

noextract
let server_driver_live = DS.server_driver_live

noextract
let server_driver_endpoint_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (material_spec:Ghost.erased EP.server_endpoint_material_spec)
  : slprop =
  SP.server_invariant (server_driver_canonical d) B.empty B.empty st **
  Box.pts_to d.server_driver_channel DS.no_channel **
  Box.pts_to d.server_driver_buffered_len 0sz **
  exists* empty_payload raw network_out material cv_input signature app_out local_app_out.
    V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
    V.pts_to d.server_driver_raw #1.0R raw **
    V.pts_to d.server_driver_network_out #1.0R network_out **
    V.pts_to d.server_driver_material_payload #1.0R material **
    V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
    V.pts_to d.server_driver_signature #1.0R signature **
    V.pts_to d.server_driver_app_out #1.0R app_out **
    V.pts_to d.server_driver_local_app_out #1.0R local_app_out **
    pure (
      ST.server_end_to_end_invariant st /\
      DS.server_driver_config_matches_credentials
        st
        certificate_chain
        credential_identity /\
      DS.server_driver_supported_profile_selection st credential_identity /\
      server_driver_wire_logs_match st B.empty B.empty B.empty 0sz /\
      st == Ghost.reveal d.server_driver_initial /\
      B.length empty_payload == 0 /\
      B.length raw == SZ.v DS.driver_rx_capacity /\
      B.length network_out == SZ.v DS.driver_network_out_capacity /\
      B.length material == SZ.v DS.driver_material_capacity /\
      Seq.equal material (Ghost.reveal material_spec) /\
      B.length cv_input == SZ.v DS.driver_certificate_verify_input_capacity /\
      B.length signature == SZ.v DS.driver_signature_capacity /\
      B.length app_out == SZ.v DS.driver_app_out_capacity /\
      B.length local_app_out == SZ.v DS.driver_app_out_capacity /\
      Bounds.max_certificate_verify_input_len <=
        SZ.v DS.driver_certificate_verify_input_capacity /\
      IM.max_signature_len <= SZ.v DS.driver_signature_capacity /\
      IM.max_record_fragment_len <= SZ.v DS.driver_app_out_capacity /\
      V.is_full_vec d.server_driver_empty_payload /\
      V.is_full_vec d.server_driver_raw /\
      V.is_full_vec d.server_driver_network_out /\
      V.is_full_vec d.server_driver_material_payload /\
      V.is_full_vec d.server_driver_certificate_verify_input /\
      V.is_full_vec d.server_driver_signature /\
      V.is_full_vec d.server_driver_app_out /\
      V.is_full_vec d.server_driver_local_app_out)

noextract
let server_driver_connected = DS.server_driver_connected

noextract
let server_driver_endpoint_connected = DS.server_driver_endpoint_connected

noextract
ghost fn server_driver_endpoint_connected_valid_byte_trace
  (d:server_driver)
  (cfg:SQueries.server_next_local_action_config)
  (frame:EP.server_endpoint_frame)
  (canonical_received:Ghost.erased B.bytes)
  (canonical_sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
  requires DS.server_driver_endpoint_connected
              d
              cfg
              frame
              (Ghost.reveal st)
              'certificate_chain
              'credential_identity
              (Ghost.reveal canonical_received)
              (Ghost.reveal canonical_sent)
  ensures DS.server_driver_endpoint_connected
            d
            cfg
            frame
            (Ghost.reveal st)
            'certificate_chain
            'credential_identity
            (Ghost.reveal canonical_received)
            (Ghost.reveal canonical_sent) **
          pure (WFSM.valid_byte_trace
            (SP.server_system
              (Ghost.reveal
                (DS.server_driver_canonical d).SP.canonical_server_initial))
            (Ghost.reveal canonical_received)
            (Ghost.reveal st)
            (Ghost.reveal canonical_sent)
            Seq.empty)
{
  unfold (DS.server_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal canonical_received)
    (Ghost.reveal canonical_sent));
  with ch buffered_len cv_input signature. _;
  SP.server_invariant_valid
    (DS.server_driver_canonical d)
    canonical_received
    canonical_sent
    st;
  with ch buffered_len cv_input signature.
  fold (DS.server_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal canonical_received)
    (Ghost.reveal canonical_sent))
}

noextract
let server_driver_closed = DS.server_driver_closed

let lemma_server_local_process_correct_received_unchanged
  (initial:CS.connection_state)
  (ev:CTypes.server_local_event)
  (old_out:B.bytes)
  (out_contents:B.bytes)
  (out_len:SZ.t)
  (received0:B.bytes)
  (sent0:B.bytes)
  (st0:CS.connection_state)
  (result:CPI.process_result)
  (received1:B.bytes)
  (sent1:B.bytes)
  (st1:CS.connection_state)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : Lemma
      (requires
        CPI.local_process_correct
          (SP.server_system initial)
          ev
          old_out
          out_contents
          out_len
          received0
          sent0
          st0
          result
          received1
          sent1
          st1
          wire_outputs
          local_outputs)
      (ensures Seq.equal received1 received0)
=
  match result.CPI.process_status with
  | CPI.StepOk -> ()
  | CPI.NeedMoreInput
  | CPI.ParseFailed ->
    assert False
  | CPI.OutputBufferTooSmall -> ()
  | CPI.DecodeError
  | CPI.IllegalTransition
  | CPI.ConnectionFailed -> ()

let lemma_server_driver_endpoint_local_wire_logs_match
  (initial:CS.connection_state)
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (canonical_received0:B.bytes)
  (canonical_sent0:B.bytes)
  (canonical_received1:B.bytes)
  (canonical_sent1:B.bytes)
  (transport_received:B.bytes)
  (transport_sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  (ev:CTypes.server_local_event)
  (old_out:B.bytes)
  (out_contents:B.bytes)
  (out_len:SZ.t)
  (result:CPI.process_result)
  (wire_outputs:list CW.wire_message)
  (local_outputs:list CTypes.local_output)
  : Lemma
      (requires
        SP.server_invariant_pure
          initial
          canonical_received0
          canonical_sent0
          st0 /\
        SP.server_invariant_pure
          initial
          canonical_received1
          canonical_sent1
          st1 /\
        ST.server_connection_control_not_failed st0 /\
        DS.server_driver_wire_logs_match
          st0
          transport_received
          transport_sent
          buffered
          buffered_len /\
        CPI.local_process_correct
          (SP.server_system initial)
          ev
          old_out
          out_contents
          out_len
          canonical_received0
          canonical_sent0
          st0
          result
          canonical_received1
          canonical_sent1
          st1
          wire_outputs
          local_outputs)
      (ensures
        DS.server_driver_wire_logs_match
          st1
          transport_received
          canonical_sent1
          buffered
          buffered_len)
=
  let consumed =
    ID.indefinite_description_ghost
      B.bytes
      (fun consumed ->
        DS.server_driver_wire_logs_match_witness
          st0
          transport_received
          transport_sent
          consumed
          buffered
          buffered_len) in
  assert (DS.server_driver_wire_logs_match_witness
    st0
    transport_received
    transport_sent
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  assert (Seq.equal
    st0.CS.cs_wire_log.CL.raw_received
    (Ghost.reveal consumed));
  lemma_server_local_process_correct_received_unchanged
    initial
    ev
    old_out
    out_contents
    out_len
    canonical_received0
    canonical_sent0
    st0
    result
    canonical_received1
    canonical_sent1
    st1
    wire_outputs
    local_outputs;
  assert (Seq.equal canonical_received1 canonical_received0);
  assert (Seq.equal canonical_received0 st0.CS.cs_wire_log.CL.raw_received);
  assert (Seq.equal canonical_received1 st1.CS.cs_wire_log.CL.raw_received);
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received canonical_received1);
  assert (Seq.equal st1.CS.cs_wire_log.CL.raw_received st0.CS.cs_wire_log.CL.raw_received);
  Seq.lemma_eq_elim
    st1.CS.cs_wire_log.CL.raw_received
    st0.CS.cs_wire_log.CL.raw_received;
  assert (DS.logged_received_bytes_accounted
    st1.CS.cs_wire_log.CL.raw_received
    (Ghost.reveal consumed));
  assert (Seq.equal
    st1.CS.cs_wire_log.CL.raw_received
    (Ghost.reveal consumed));
  assert (DS.server_driver_wire_logs_match_witness
    st1
    transport_received
    canonical_sent1
    (Ghost.reveal consumed)
    buffered
    buffered_len);
  assert (exists consumed1.
    DS.server_driver_wire_logs_match_witness
      st1
      transport_received
      canonical_sent1
      consumed1
      buffered
      buffered_len)

let lemma_server_driver_wire_logs_match_exists
  (st:CS.connection_state)
  (transport_received:B.bytes)
  (transport_sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        DS.server_driver_wire_logs_match
          st
          transport_received
          transport_sent
          buffered
          buffered_len)
      (ensures
        exists buffered'.
          DS.server_driver_wire_logs_match
            st
            transport_received
            transport_sent
            buffered'
            buffered_len)
=
  introduce exists (buffered':B.bytes).
    DS.server_driver_wire_logs_match
      st
      transport_received
      transport_sent
      buffered'
      buffered_len
  with buffered
  and ()

ghost fn expose_server_invariant_pure
  (srv:SP.canonical_server)
  (received:Ghost.erased B.bytes)
  (sent:Ghost.erased B.bytes)
  (st:Ghost.erased CS.connection_state)
requires
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
ensures
  SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  pure (SP.server_invariant_pure
    (Ghost.reveal srv.SP.canonical_server_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st))
{
  unfold (SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st));
  with certificate_chain credential_identity. _;
  assert (pure (SP.server_invariant_pure
    (Ghost.reveal srv.SP.canonical_server_initial)
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)));
  with certificate_chain credential_identity.
  fold (SP.server_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st))
}

let lemma_server_driver_wire_logs_match_received_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st)
      (ensures server_driver_received_log_exact_prefix st received)
=
  DS.lemma_server_driver_wire_logs_match_received_exact_prefix
    st
    received
    sent
    buffered
    buffered_len

let lemma_server_driver_wire_logs_match_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  (buffered:B.bytes)
  (buffered_len:SZ.t)
  : Lemma
      (requires
        server_driver_wire_logs_match st received sent buffered buffered_len /\
        ST.server_connection_control_not_failed st /\
        buffered_len == 0sz)
      (ensures server_driver_received_no_read_ahead st received)
=
  DS.lemma_server_driver_wire_logs_match_received_no_read_ahead
    st
    received
    sent
    buffered
    buffered_len

open TLS13.Impl.Server.Driver.State
open TLS13.Impl.Server.Driver.Transport
open TLS13.Impl.Server.Driver.Network
open TLS13.Impl.Server.Driver.Local

ghost fn server_driver_live_to_endpoint_live
  (d:server_driver)
  (st:Ghost.erased CS.connection_state)
  (certificate_chain:Ghost.erased B.bytes)
  (credential_identity:Ghost.erased CS.server_credential_identity)
  requires server_driver_live
             d
             (Ghost.reveal st)
             (Ghost.reveal certificate_chain)
             (Ghost.reveal credential_identity) **
           server_driver_canonical_progress d (Ghost.reveal st)
           ** pure (Ghost.reveal st ==
              Ghost.reveal
                (server_driver_canonical d).SP.canonical_server_initial)
  ensures exists* material_spec.
            server_driver_endpoint_live
              d
              (Ghost.reveal st)
              (Ghost.reveal certificate_chain)
              (Ghost.reveal credential_identity)
              material_spec
{
  unfold (server_driver_live
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity));
  unfold (server_driver_canonical_progress d (Ghost.reveal st));
  unfold (server_driver_buffers d B.empty 0sz);
  with empty_payload raw network_out material cv_input signature app_out local_app_out.
    assert (V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
            V.pts_to d.server_driver_raw #1.0R raw **
            V.pts_to d.server_driver_network_out #1.0R network_out **
            V.pts_to d.server_driver_material_payload #1.0R material **
            V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
            V.pts_to d.server_driver_signature #1.0R signature **
            V.pts_to d.server_driver_app_out #1.0R app_out **
            V.pts_to d.server_driver_local_app_out #1.0R local_app_out **
            pure (B.length empty_payload == 0 /\
                  B.length raw == SZ.v driver_rx_capacity /\
                  B.length network_out == SZ.v driver_network_out_capacity /\
                  B.length material == SZ.v driver_material_capacity /\
                  B.length cv_input == SZ.v driver_certificate_verify_input_capacity /\
                  B.length signature == SZ.v driver_signature_capacity /\
                  B.length app_out == SZ.v driver_app_out_capacity /\
                  B.length local_app_out == SZ.v driver_app_out_capacity));
  assert_norm (SZ.v driver_material_capacity == 64);
  assert (pure (B.length material == 64));
  let material_spec : Ghost.erased EP.server_endpoint_material_spec = Ghost.hide material;
  assert (pure (Seq.equal material (Ghost.reveal material_spec)));
  assert (pure (SP.server_invariant_pure
    (Ghost.reveal d.server_driver_initial)
    B.empty
    B.empty
    (Ghost.reveal st)));
  assert (pure (SP.server_config_matches_credentials
    (Ghost.reveal d.server_driver_initial)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)));
  fold (SP.server_invariant
    (server_driver_canonical d)
    B.empty
    B.empty
    (Ghost.reveal st));
  fold (server_driver_endpoint_live
    d
    (Ghost.reveal st)
    (Ghost.reveal certificate_chain)
    (Ghost.reveal credential_identity)
    material_spec);
}

open TLS13.Impl.Server.Driver.Handshake

let lemma_control_snapshot_app_ready
  (snapshot:CR.control_snapshot)
  (st:CS.connection_state)
  : Lemma
      (requires
        CR.control_snapshot_matches snapshot st /\
        snapshot.CR.snapshot_control_tag == 2uy)
      (ensures
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
=
  assert_norm (U8.v 2uy == 2);
  assert (U8.v snapshot.CR.snapshot_control_tag == 2);
  match st.CS.cs_model.CS.model_control with
  | CS.ControlApplicationData -> ()
  | _ -> assert False

let lemma_application_ready_close_notify_ready
  (st:CS.connection_state)
  : Lemma
    (requires server_driver_application_ready st)
    (ensures
      ST.server_local_event_input_ready
        st
        ST.LocalSendCloseNotify
        B.empty)
=
  Seq.lemma_eq_intro B.empty B.empty;
  assert (Seq.equal B.empty B.empty);
  assert (ST.server_end_to_end_invariant st);
  assert (st.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint);
  assert_norm (CS.traffic_label_for_endpoint_direction CS.ServerEndpoint CS.TrafficWrite ==
    CS.ServerTraffic);
  assert (CS.application_record_keys_installed_for_role CS.ServerEndpoint st.CS.cs_model);
  match st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic with
  | Some _ -> ()
  | None ->
    assert_norm (CS.traffic_material_for_label
      st.CS.cs_model.CS.model_handshake.CS.hs_keys
      CS.TrafficApplication
      CS.ServerTraffic ==
      st.CS.cs_model.CS.model_handshake.CS.hs_keys.CS.ks_server_application_traffic);
    assert False

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  (#supported_profile_provider: erased SP.server_supported_profile_provider)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns result: option server_driver
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some d ->
             exists* credential_identity.
               server_driver_live
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity)
                 (Ghost.reveal 'certificate_chain_bytes)
                 credential_identity **
               server_driver_canonical_progress
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity) **
               pure (ST.server_state_correct
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     CM.can_start_server
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     ST.server_end_to_end_invariant
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     Ghost.reveal
                       (server_driver_canonical d).SP.canonical_server_initial ==
                       CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity)
           | None ->
             emp)
{
  let material_payload = V.alloc 0uy DS.driver_material_capacity;
  V.to_array_pts_to material_payload;
  let material_ok =
    Crypto.random_bytes
      (V.vec_to_array material_payload)
      DS.driver_material_capacity;
  with material_seed.
    assert (pts_to (V.vec_to_array material_payload) material_seed);
  V.to_vec_pts_to material_payload;
  if not material_ok {
    V.free material_payload;
    None
  } else {
  let creds_opt =
    O.server_credentials_new
      certificate_chain
      certificate_chain_len
      private_key
      private_key_len;
  match creds_opt {
    None -> {
      V.free material_payload;
      None
    }
    Some creds -> {
      with credential_identity. assert (
        O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      let erased_identity : erased CS.server_credential_identity =
        Ghost.hide credential_identity;
      let s =
        S.new_server_erased_credential_identity
          certificate_chain
          certificate_chain_len
          #erased_identity;
      assert (pure (Ghost.reveal erased_identity == credential_identity));
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            (Ghost.reveal erased_identity)))
        as
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      let progress = MR.alloc #_ #SP.server_progress_preorder
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      MR.take_snapshot
        progress
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      let channel = Box.alloc no_channel;
      let buffered_len = Box.alloc 0sz;
      let empty_payload = V.alloc 0uy 0sz;
      let raw = V.alloc 0uy DS.driver_rx_capacity;
      let network_out = V.alloc 0uy DS.driver_network_out_capacity;
      let cv_input = V.alloc 0uy DS.driver_certificate_verify_input_capacity;
      let signature = V.alloc 0uy DS.driver_signature_capacity;
      let app_out = V.alloc 0uy DS.driver_app_out_capacity;
      let local_app_out = V.alloc 0uy DS.driver_app_out_capacity;
      assert (pure (Bounds.max_certificate_verify_input_len <=
        SZ.v DS.driver_certificate_verify_input_capacity));
      assert (pure (IM.max_signature_len <= SZ.v DS.driver_signature_capacity));
      assert (pure (IM.max_record_fragment_len <= SZ.v DS.driver_app_out_capacity));
      let d = {
        server_driver_server = s;
        server_driver_credentials = creds;
        server_driver_channel = channel;
        server_driver_buffered_len = buffered_len;
        server_driver_empty_payload = empty_payload;
        server_driver_raw = raw;
        server_driver_network_out = network_out;
        server_driver_material_payload = material_payload;
        server_driver_certificate_verify_input = cv_input;
        server_driver_signature = signature;
        server_driver_app_out = app_out;
        server_driver_local_app_out = local_app_out;
        server_driver_progress = progress;
        server_driver_initial =
          Ghost.hide
            (CR.server_initial_state
              (Ghost.reveal 'certificate_chain_bytes)
              credential_identity);
        server_driver_supported_profile =
          Ghost.hide
            ((Ghost.reveal supported_profile_provider)
              (CR.server_initial_state
                (Ghost.reveal 'certificate_chain_bytes)
                credential_identity));
      };
      rewrite (Box.pts_to channel no_channel) as
        (Box.pts_to d.server_driver_channel no_channel);
      rewrite (Box.pts_to buffered_len 0sz) as
        (Box.pts_to d.server_driver_buffered_len 0sz);
      rewrite (V.pts_to empty_payload #1.0R (Seq.create 0 0uy)) as
        (V.pts_to d.server_driver_empty_payload #1.0R (Seq.create 0 0uy));
      rewrite
        (V.pts_to raw #1.0R (Seq.create (SZ.v DS.driver_rx_capacity) 0uy))
        as
        (V.pts_to d.server_driver_raw #1.0R (Seq.create (SZ.v DS.driver_rx_capacity) 0uy));
      rewrite
        (V.pts_to network_out #1.0R (Seq.create (SZ.v DS.driver_network_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_network_out #1.0R (Seq.create (SZ.v DS.driver_network_out_capacity) 0uy));
      rewrite
        (V.pts_to material_payload #1.0R material_seed)
        as
        (V.pts_to d.server_driver_material_payload #1.0R material_seed);
      rewrite
        (V.pts_to cv_input #1.0R (Seq.create (SZ.v DS.driver_certificate_verify_input_capacity) 0uy))
        as
        (V.pts_to d.server_driver_certificate_verify_input #1.0R
          (Seq.create (SZ.v DS.driver_certificate_verify_input_capacity) 0uy));
      rewrite
        (V.pts_to signature #1.0R (Seq.create (SZ.v DS.driver_signature_capacity) 0uy))
        as
        (V.pts_to d.server_driver_signature #1.0R
          (Seq.create (SZ.v DS.driver_signature_capacity) 0uy));
      rewrite
        (V.pts_to app_out #1.0R (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_app_out #1.0R
          (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy));
      rewrite
        (V.pts_to local_app_out #1.0R (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy))
        as
        (V.pts_to d.server_driver_local_app_out #1.0R
          (Seq.create (SZ.v DS.driver_app_out_capacity) 0uy));
      rewrite
        (S.connection_exactly
          s
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (S.connection_exactly
          d.server_driver_server
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      rewrite
        (O.is_server_credentials
          creds
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        as
        (O.is_server_credentials
          d.server_driver_credentials
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity);
      rewrite
        (MR.pts_to progress #1.0R
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (MR.pts_to d.server_driver_progress #1.0R
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      rewrite
        (MR.snapshot progress
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (MR.snapshot d.server_driver_progress
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity));
      assert (pure (Ghost.reveal d.server_driver_initial ==
        CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
      rewrite
        (MR.snapshot d.server_driver_progress
          (CR.server_initial_state
            (Ghost.reveal 'certificate_chain_bytes)
            credential_identity))
        as
        (MR.snapshot d.server_driver_progress
          (Ghost.reveal d.server_driver_initial));
      fold (server_driver_canonical_progress d
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity));
      fold (server_driver_buffers d B.empty 0sz);
      fold (server_driver_live
        d
        (CR.server_initial_state
          (Ghost.reveal 'certificate_chain_bytes)
          credential_identity)
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity);
      Some d
    }
  }
  }
}

noextract
fn accept_endpoint
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (fuel:SZ.t)
  (certificate_chain_len:SZ.t)
  (certificate_chain_len_proof:
    (certificate_chain:Ghost.erased B.bytes ->
      Ghost.erased
        (SZ.v certificate_chain_len == B.length (Ghost.reveal certificate_chain))))
  (certificate_chain_len_bound:
    Ghost.erased
      (SZ.v certificate_chain_len <= Bounds.max_server_certificate_chain_len))
  (material_spec:Ghost.erased EP.server_endpoint_material_spec)
  (private_key:V.vec U8.t)
  (material_deferred_ready:
    (st:Ghost.erased CS.connection_state ->
    action:SQueries.server_deferred_action ->
      Ghost.erased
        (SQueries.server_deferred_action_ready (Ghost.reveal st) action ==>
         EP.server_endpoint_material_bytes_match_state
           (Ghost.reveal material_spec)
           (Ghost.reveal st))))
  requires server_driver_endpoint_live d 'st0 'certificate_chain 'credential_identity material_spec **
           pts_to bind_host 'bind_host_bytes **
           V.pts_to private_key #1.0R 'private_key_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 B.length 'private_key_bytes == 32 /\
                 Seq.equal 'private_key_bytes
                   (EP.server_endpoint_private_bytes_of_material
                     (Ghost.reveal material_spec)))
  returns result:option EP.server_endpoint_run_result
  ensures pts_to bind_host 'bind_host_bytes **
          (let cfg = server_driver_endpoint_config d in
           let frame =
             server_driver_endpoint_workflow_frame
               d
               certificate_chain_len
               certificate_chain_len_proof
               certificate_chain_len_bound
               material_spec
               private_key
               material_deferred_ready in
           match result with
           | None ->
             server_driver_endpoint_live d 'st0 'certificate_chain 'credential_identity material_spec **
             V.pts_to private_key #1.0R 'private_key_bytes
           | Some _ ->
             exists* st1 received1 sent1.
               server_driver_endpoint_connected
                 d
                 cfg
                 frame
                 st1
                 'certificate_chain
                 'credential_identity
                 received1
                 sent1)
{
  let cfg = server_driver_endpoint_config d;
  let frame =
    server_driver_endpoint_workflow_frame
      d
      certificate_chain_len
      certificate_chain_len_proof
      certificate_chain_len_bound
      material_spec
      private_key
      material_deferred_ready;
  unfold (server_driver_endpoint_live d 'st0 'certificate_chain 'credential_identity material_spec);
  with empty_payload raw network_out material cv_input signature app_out local_app_out. _;
  let listener_opt = IO.listen_tcp bind_host bind_host_len port;
  match listener_opt {
    None -> {
      with empty_payload raw network_out material cv_input signature app_out local_app_out.
      fold (server_driver_endpoint_live d 'st0 'certificate_chain 'credential_identity material_spec);
      None
    }
    Some listener -> {
      let ch_opt = IO.accept_tcp listener;
      IO.close_listener listener;
      match ch_opt {
        None -> {
          with empty_payload raw network_out material cv_input signature app_out local_app_out.
          fold (server_driver_endpoint_live d 'st0 'certificate_chain 'credential_identity material_spec);
          None
        }
        Some ch -> {
          Box.(d.server_driver_channel := Some ch);
          V.to_array_pts_to d.server_driver_empty_payload;
          V.to_array_pts_to d.server_driver_app_out;
          V.to_array_pts_to d.server_driver_local_app_out;
          assert (pure (forall (i:nat{i < B.length empty_payload}).
            Seq.index empty_payload i == Seq.index B.empty i));
          Seq.lemma_eq_intro empty_payload B.empty;
          Seq.lemma_eq_elim empty_payload B.empty;
          rewrite
            (pts_to (V.vec_to_array d.server_driver_empty_payload) empty_payload)
            as
            (pts_to (V.vec_to_array d.server_driver_empty_payload) B.empty);
          assert (pure (frame.EP.server_ep_query.SQueries.server_query_network_app_out ==
            V.vec_to_array d.server_driver_app_out));
          assert (pure (SZ.v frame.EP.server_ep_query.SQueries.server_query_network_app_out_len ==
            SZ.v DS.driver_app_out_capacity));
          assert (pure (frame.EP.server_ep_query.SQueries.server_query_local_payload ==
            V.vec_to_array d.server_driver_empty_payload));
          assert (pure (SZ.v frame.EP.server_ep_query.SQueries.server_query_local_payload_len ==
            0));
          assert (pure (frame.EP.server_ep_query.SQueries.server_query_local_app_out ==
            V.vec_to_array d.server_driver_local_app_out));
          assert (pure (SZ.v frame.EP.server_ep_query.SQueries.server_query_local_app_out_len ==
            SZ.v DS.driver_app_out_capacity));
          assert (pure (frame.EP.server_ep_material == d.server_driver_material_payload));
          assert (pure (SZ.v frame.EP.server_ep_material_len ==
            SZ.v DS.driver_material_capacity));
          assert (pure (frame.EP.server_ep_raw == d.server_driver_raw));
          assert (pure (SZ.v frame.EP.server_ep_raw_len == SZ.v DS.driver_rx_capacity));
          assert (pure (frame.EP.server_ep_network_out == d.server_driver_network_out));
          assert (pure (SZ.v frame.EP.server_ep_network_out_len ==
            SZ.v DS.driver_network_out_capacity));
          assert (pure (frame.EP.server_ep_material_spec == material_spec));
          assert (pure (frame.EP.server_ep_private == private_key));
          assert_norm (SZ.v 32sz == 32);
          assert (pure (SZ.v frame.EP.server_ep_private_len == 32));
          rewrite
            (pts_to (V.vec_to_array d.server_driver_app_out) app_out)
            as
            (pts_to
              frame.EP.server_ep_query.SQueries.server_query_network_app_out
              app_out);
          rewrite
            (pts_to (V.vec_to_array d.server_driver_empty_payload) B.empty)
            as
            (pts_to
              frame.EP.server_ep_query.SQueries.server_query_local_payload
              B.empty);
          rewrite
            (pts_to (V.vec_to_array d.server_driver_local_app_out) local_app_out)
            as
            (pts_to
              frame.EP.server_ep_query.SQueries.server_query_local_app_out
              local_app_out);
          with app_out.
          fold (SQueries.server_network_persistent_resource frame.EP.server_ep_query);
          with local_app_out.
          fold (SQueries.server_local_persistent_resource frame.EP.server_ep_query);
          fold (SQueries.server_next_local_action_frame_ready
            (server_driver_canonical d)
            cfg
            frame.EP.server_ep_query
            'st0);
          rewrite
            (V.pts_to d.server_driver_material_payload #1.0R material)
            as
            (V.pts_to frame.EP.server_ep_material #1.0R material);
          rewrite
            (V.pts_to d.server_driver_raw #1.0R raw)
            as
            (V.pts_to frame.EP.server_ep_raw #1.0R raw);
          rewrite
            (V.pts_to d.server_driver_network_out #1.0R network_out)
            as
            (V.pts_to frame.EP.server_ep_network_out #1.0R network_out);
          rewrite
            (V.pts_to private_key #1.0R 'private_key_bytes)
            as
            (V.pts_to
              frame.EP.server_ep_private
              #1.0R
              'private_key_bytes);
          assert (pure (SZ.v frame.EP.server_ep_material_len == 64));
          assert (pure (B.length material == SZ.v frame.EP.server_ep_material_len));
          assert (pure (EP.server_endpoint_material_bytes frame ==
            Ghost.reveal material_spec));
          assert (pure (Seq.equal material (EP.server_endpoint_material_bytes frame)));
          assert (pure (B.length 'private_key_bytes ==
            SZ.v frame.EP.server_ep_private_len));
          assert (pure (EP.server_endpoint_private_bytes frame ==
            EP.server_endpoint_private_bytes_of_material (Ghost.reveal material_spec)));
          assert (pure (Seq.equal
            'private_key_bytes
            (EP.server_endpoint_private_bytes frame)));
          with material 'private_key_bytes.
          fold (EP.server_endpoint_payloads_ready frame);
          fold (EP.server_endpoint_frame_ready
            (server_driver_canonical d)
            cfg
            frame
            'st0);
          let empty_received = B.empty;
          with empty_received raw network_out.
          fold (EP.server_endpoint_io_ready
            (server_driver_canonical d)
            ch
            frame
            B.empty
            B.empty
            'st0);
          let run_result =
            EP.server_endpoint_run_workflow
              (server_driver_canonical d)
              cfg
              frame
              ch
              d.server_driver_buffered_len
              false
              true
              false
              fuel
              (Ghost.hide B.empty)
              (Ghost.hide B.empty)
              'st0;
          with received1 sent1 st1 buffered_len1.
            assert (
              SP.server_invariant
                (server_driver_canonical d)
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1) **
              EP.server_endpoint_frame_ready
                (server_driver_canonical d)
                cfg
                frame
                (Ghost.reveal st1) **
              EP.server_endpoint_io_ready
                (server_driver_canonical d)
                ch
                frame
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1) **
              Box.pts_to d.server_driver_buffered_len buffered_len1);
          expose_server_invariant_pure
            (server_driver_canonical d)
            received1
            sent1
            st1;
          assert (pure (ST.server_end_to_end_invariant (Ghost.reveal st1)));
          assert (pure (DS.server_driver_config_matches_credentials
            (Ghost.reveal st1)
            (Ghost.reveal 'certificate_chain)
            (Ghost.reveal 'credential_identity)));
          (Ghost.reveal (DS.server_driver_canonical d).SP.canonical_server_supported_profile)
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1)
            (Ghost.reveal 'certificate_chain)
            (Ghost.reveal 'credential_identity);
          assert (pure (DS.server_driver_supported_profile_selection
            (Ghost.reveal st1)
            (Ghost.reveal 'credential_identity)));
          rewrite
            (EP.server_endpoint_frame_ready
              (server_driver_canonical d)
              cfg
              frame
              (Ghost.reveal st1))
            as
            (EP.server_endpoint_frame_ready
              (server_driver_canonical d)
              (server_driver_endpoint_config d)
              (server_driver_endpoint_workflow_frame
                d
                certificate_chain_len
                certificate_chain_len_proof
                certificate_chain_len_bound
                material_spec
                private_key
                material_deferred_ready)
              (Ghost.reveal st1));
          rewrite
            (EP.server_endpoint_io_ready
              (server_driver_canonical d)
              ch
              frame
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1))
            as
            (EP.server_endpoint_io_ready
              (server_driver_canonical d)
              ch
              (server_driver_endpoint_workflow_frame
                d
                certificate_chain_len
                certificate_chain_len_proof
                certificate_chain_len_bound
                material_spec
                private_key
                material_deferred_ready)
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1));
          with ch buffered_len1 cv_input signature.
          fold (server_driver_endpoint_connected
            d
            (server_driver_endpoint_config d)
            (server_driver_endpoint_workflow_frame
              d
              certificate_chain_len
              certificate_chain_len_proof
              certificate_chain_len_bound
              material_spec
              private_key
              material_deferred_ready)
            (Ghost.reveal st1)
            (Ghost.reveal 'certificate_chain)
            (Ghost.reveal 'credential_identity)
            (Ghost.reveal received1)
            (Ghost.reveal sent1));
          Some run_result
        }
      }
    }
  }
}

fn accept
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg ->
                    CS.cipher_suite_offered
                      cfg.CS.server_supported_cipher_suites
                      T.TLS_CHACHA20_POLY1305_SHA256 /\
                    CS.named_group_offered
                      cfg.CS.server_supported_groups
                      T.X25519 /\
                    CS.signature_scheme_offered
                      cfg.CS.server_allowed_signature_schemes
                      T.Rsa_pss_rsae_sha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns status:server_workflow_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerWorkflowClosed ->
             exists* st1.
               server_driver_closed d st1 'certificate_chain 'credential_identity **
               pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config)
           | ServerWorkflowOk ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (server_driver_application_ready st1 /\
                    st1.CS.cs_model.CS.model_config ==
                      'st0.CS.cs_model.CS.model_config /\
                    server_driver_sent_log_exact st1 sent /\
                    server_driver_received_log_accounted st1 received /\
                    server_driver_received_log_exact_prefix st1 received /\
                    server_driver_received_no_read_ahead st1 received)
           | _ ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent **
               pure (st1.CS.cs_model.CS.model_config ==
                 'st0.CS.cs_model.CS.model_config))
{
  let result =
    accept_start_read_client_hello_select_derive_send_server_hello_drain_empty_once
      d
      bind_host
      bind_host_len
      port
      network_fuel
      local_fuel;
  match result {
    ServerDriverAcceptServerHelloDrainListenFailed -> {
      close_live_without_transport d;
      ServerWorkflowClosed
    }
    ServerDriverAcceptServerHelloDrainAcceptFailed -> {
      close_live_without_transport d;
      ServerWorkflowClosed
    }
    ServerDriverAcceptServerHelloDrainClientHelloWait wait -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
      if (wait.server_driver_client_hello_wait_exhausted) {
        ServerWorkflowExhausted
      } else {
        if (wait.server_driver_client_hello_wait_last.ST.response.ST.status = ST.NeedMoreInput) {
          ServerWorkflowNeedMoreInput
        } else {
          ServerWorkflowStepFailed
        }
      }
    }
    ServerDriverAcceptServerHelloDrainMaterialFailed -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainSelectionNotReady -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainDeriveFailed -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainSendNotReady -> {
      with st1 received sent.
        assert (server_driver_connected
          d
          st1
          'certificate_chain
          'credential_identity
          received
          sent **
        pure (st1.CS.cs_model.CS.model_config ==
          'st0.CS.cs_model.CS.model_config));
      ServerWorkflowStepFailed
    }
    ServerDriverAcceptServerHelloDrainOk drain -> {
      with st1 received sent.
        assert (
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received
            sent **
          pure (st1.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config));
      if (drain.server_driver_local_drain_exhausted) {
        ServerWorkflowExhausted
      } else {
        match drain.server_driver_local_drain_last {
          ServerDriverLocalUnsupported -> {
            ServerWorkflowStepFailed
          }
          ServerDriverLocalStepFailed -> {
            ServerWorkflowStepFailed
          }
          ServerDriverLocalNotReady -> {
            let net = DN.read_process_network_until_ready d network_fuel;
            with st_net received_net sent_net net_app_out.
              assert (
                server_driver_connected_with_app_out
                  d
                  st_net
                  'certificate_chain
                  'credential_identity
                  received_net
                  sent_net
                  net_app_out **
                pure (st_net.CS.cs_model.CS.model_config ==
                  st1.CS.cs_model.CS.model_config));
            assert (pure (st_net.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config));
            forget_server_driver_connected_app_out d;
            if (net.DN.server_driver_network_loop_exhausted) {
              ServerWorkflowExhausted
            } else {
              if (net.DN.server_driver_network_loop_last.ST.response.ST.status = ST.StepOk) {
                let drain_after_client_finished =
                  DL.drain_ready_empty_local_actions d local_fuel;
                with st2 received2 sent2.
                  assert (
                    server_driver_connected
                      d
                      st2
                      'certificate_chain
                      'credential_identity
                      received2
                      sent2 **
                    pure (st2.CS.cs_model.CS.model_config ==
                      st_net.CS.cs_model.CS.model_config));
                assert (pure (st2.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config));
                if (drain_after_client_finished.DL.server_driver_local_drain_exhausted) {
                  ServerWorkflowExhausted
                } else {
                  match drain_after_client_finished.DL.server_driver_local_drain_last {
                    ServerDriverLocalUnsupported -> {
                      ServerWorkflowStepFailed
                    }
                    ServerDriverLocalStepFailed -> {
                      ServerWorkflowStepFailed
                    }
                    _ -> {
                      let snapshot = DN.server_driver_control_snapshot d;
                      with st3 received3 sent3.
                        assert (server_driver_connected
                          d
                          st3
                          'certificate_chain
                          'credential_identity
                          received3
                          sent3);
                      assert (pure (st3.CS.cs_model.CS.model_config ==
                        st2.CS.cs_model.CS.model_config));
                      assert (pure (st3.CS.cs_model.CS.model_config ==
                        'st0.CS.cs_model.CS.model_config));
                      assert (pure (CR.control_snapshot_matches snapshot st3));
                      let app_ready = snapshot.CR.snapshot_control_tag = 2uy;
                      if app_ready {
                        assert (pure (snapshot.CR.snapshot_control_tag == 2uy));
                        lemma_control_snapshot_app_ready snapshot st3;
                        assert (pure (
                          st3.CS.cs_model.CS.model_control ==
                            CS.ControlApplicationData));
                        unfold (server_driver_connected
                          d
                          st3
                          'certificate_chain
                          'credential_identity
                          received3
                          sent3);
                        with ch buffered buffered_len.
                          assert (Box.pts_to d.server_driver_channel (Some ch) **
                                  IO.is_channel ch received3 sent3 **
                                  server_driver_buffers d buffered buffered_len);
                        unfold (server_driver_buffers d buffered buffered_len);
                        with empty_payload raw network_out material cv_input signature app_out local_app_out.
                          assert (
                            Box.pts_to d.server_driver_buffered_len buffered_len **
                            V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
                            V.pts_to d.server_driver_raw #1.0R raw **
                            V.pts_to d.server_driver_network_out #1.0R network_out **
                            V.pts_to d.server_driver_material_payload #1.0R material **
                            V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
                            V.pts_to d.server_driver_signature #1.0R signature **
                            V.pts_to d.server_driver_app_out #1.0R app_out **
                            V.pts_to d.server_driver_local_app_out #1.0R local_app_out);
                        let current_buffered_len = Box.(!d.server_driver_buffered_len);
                        assert (pure (current_buffered_len == buffered_len));
                        fold (server_driver_buffers d buffered buffered_len);
                        assert (pure (ST.server_end_to_end_invariant st3));
                        rewrite (S.connection_exactly d.server_driver_server st3) as
                          (CR.connection_exactly d.server_driver_server st3);
                        let app_keys_ready =
                          CQ.server_application_record_keys_installed_runtime
                            d.server_driver_server;
                        rewrite (CR.connection_exactly d.server_driver_server st3) as
                          (S.connection_exactly d.server_driver_server st3);
                        let retained_empty = current_buffered_len = 0sz;
                        if retained_empty {
                          assert (pure (buffered_len == 0sz));
                          if app_keys_ready {
                            assert (pure (CS.application_record_keys_installed_for_role
                              CS.ServerEndpoint
                              st3.CS.cs_model));
                            CSL.lemma_server_application_ready_stable_x25519_key_share_projection
                              st3;
                            assert (pure (server_driver_sent_log_exact st3 sent3));
                            lemma_server_driver_wire_logs_match_received_accounted
                              st3
                              received3
                              sent3
                              buffered
                              buffered_len;
                            assert (pure (server_driver_received_log_accounted st3 received3));
                            assert (pure (ST.server_connection_control_not_failed st3));
                            lemma_server_driver_wire_logs_match_received_exact_prefix
                              st3
                              received3
                              sent3
                              buffered
                              buffered_len;
                            assert (pure (server_driver_received_log_exact_prefix st3 received3));
                            lemma_server_driver_wire_logs_match_received_no_read_ahead
                              st3
                              received3
                              sent3
                              buffered
                              buffered_len;
                            assert (pure (server_driver_received_no_read_ahead st3 received3));
                            fold (server_driver_connected
                              d
                              st3
                              'certificate_chain
                              'credential_identity
                              received3
                              sent3);
                            assert (pure (server_driver_application_ready st3));
                            ServerWorkflowOk
                          } else {
                            fold (server_driver_connected
                              d
                              st3
                              'certificate_chain
                              'credential_identity
                              received3
                              sent3);
                            ServerWorkflowStepFailed
                          }
                        } else {
                          fold (server_driver_connected
                            d
                            st3
                            'certificate_chain
                            'credential_identity
                            received3
                            sent3);
                          ServerWorkflowNeedMoreInput
                        }
                      } else {
                        ServerWorkflowNeedMoreInput
                      }
                    }
                  }
                }
              } else {
                ServerWorkflowStepFailed
              }
            }
          }
          ServerDriverLocalProcessed -> {
            ServerWorkflowNeedMoreInput
          }
        }
      }
    }
  }
}

fn send
  (d:server_driver)
  (payload:array U8.t)
  (payload_len:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to payload 'payload_bytes **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 ST.server_local_event_input_ready
                   'st0
                   ST.LocalSendApplicationData
                   (Ghost.reveal 'payload_bytes))
  returns status:server_workflow_status
  ensures exists* st1 sent'.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            'received
            sent' **
          pts_to payload 'payload_bytes **
          pure (server_driver_send_correct
            'st0
            st1
            status
            (Ghost.reveal 'payload_bytes)
            (Ghost.reveal 'sent)
            sent' /\
            st1.CS.cs_model.CS.model_config ==
              'st0.CS.cs_model.CS.model_config /\
            server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
            server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
            server_driver_sent_log_exact st1 sent' /\
            server_driver_received_log_accounted st1 (Ghost.reveal 'received))
{
  unfold (server_driver_connected
     d
     'st0
     (Ghost.reveal 'certificate_chain)
     (Ghost.reveal 'credential_identity)
     (Ghost.reveal 'received)
     (Ghost.reveal 'sent));
  with ch0 buffered0 buffered_len0.
     assert (Box.pts_to d.server_driver_channel (Some ch0) **
             IO.is_channel ch0 (Ghost.reveal 'received) (Ghost.reveal 'sent) **
             server_driver_buffers d buffered0 buffered_len0 **
             pure (server_driver_wire_logs_match
               'st0
               (Ghost.reveal 'received)
               (Ghost.reveal 'sent)
               buffered0
               buffered_len0));
  assert (pure (server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent)));
  lemma_server_driver_wire_logs_match_received_accounted
     'st0
     (Ghost.reveal 'received)
     (Ghost.reveal 'sent)
     buffered0
     buffered_len0;
  assert (pure (server_driver_received_log_accounted 'st0 (Ghost.reveal 'received)));
  fold (server_driver_connected
     d
     'st0
     (Ghost.reveal 'certificate_chain)
     (Ghost.reveal 'credential_identity)
     (Ghost.reveal 'received)
     (Ghost.reveal 'sent));
  let resp = send_application_data_once d payload payload_len;
  with st1 sent'.
    assert (server_driver_connected
      d
      st1
      'certificate_chain
      'credential_identity
      'received
      sent');
  lemma_server_driver_local_write_correct_preserves_config
    'st0
    st1
    resp
    ST.LocalSendApplicationData
    (Ghost.reveal 'payload_bytes)
    (Ghost.reveal 'sent)
    sent';
  unfold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    (Ghost.reveal 'received)
    sent');
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch (Ghost.reveal 'received) sent' **
            server_driver_buffers d buffered buffered_len **
            pure (server_driver_wire_logs_match st1 (Ghost.reveal 'received) sent' buffered buffered_len));
  assert (pure (server_driver_sent_log_exact st1 sent'));
  lemma_server_driver_wire_logs_match_received_accounted
    st1
    (Ghost.reveal 'received)
    sent'
    buffered
    buffered_len;
  assert (pure (server_driver_received_log_accounted st1 (Ghost.reveal 'received)));
  fold (server_driver_connected
    d
    st1
    'certificate_chain
    'credential_identity
    (Ghost.reveal 'received)
    sent');
  if (resp.ST.status = ST.StepOk) {
    ServerWorkflowOk
  } else {
    ServerWorkflowStepFailed
  }
}


noextract
let server_endpoint_send_frame_remainder
  (frame:EP.server_endpoint_frame)
  : slprop =
  SQueries.server_network_persistent_resource frame.EP.server_ep_query **
  pts_to frame.EP.server_ep_query.SQueries.server_query_local_payload B.empty **
  EP.server_endpoint_payloads_ready frame **
  pure (SZ.v frame.EP.server_ep_query.SQueries.server_query_local_payload_len == 0)

noextract
fn prepare_endpoint_send_api_ready
  (d:server_driver)
  (cfg:SQueries.server_next_local_action_config)
  (frame:EP.server_endpoint_frame)
  (ch:IO.channel)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (payload_bytes:B.bytes)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (transport_received0:Ghost.erased B.bytes)
  (transport_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires EP.server_endpoint_frame_ready
             (DS.server_driver_canonical d)
             cfg
             frame
             (Ghost.reveal st0) **
           EP.server_endpoint_io_ready
             (DS.server_driver_canonical d)
             ch
             frame
             (Ghost.reveal transport_received0)
             (Ghost.reveal transport_sent0)
             (Ghost.reveal st0) **
           pts_to payload payload_bytes **
           pure (B.length payload_bytes == SZ.v payload_len /\
                 Seq.equal (Ghost.reveal canonical_sent0) (Ghost.reveal transport_sent0) /\
                 ST.server_local_event_input_ready
                   (Ghost.reveal st0)
                   ST.LocalSendApplicationData
                   payload_bytes)
  returns local_frame:SP.tls_server_local_bridge_frame
  ensures EP.server_api_local_action_ready
            (DS.server_driver_canonical d)
            ch
            frame
            (Ghost.reveal canonical_received0)
            (Ghost.reveal canonical_sent0)
            (Ghost.reveal st0)
            (server_driver_endpoint_send_event payload_bytes)
            local_frame **
          server_endpoint_send_frame_remainder frame **
          pure (
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload == payload /\
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload_len == payload_len /\
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out ==
              frame.EP.server_ep_query.SQueries.server_query_local_app_out /\
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out_len ==
              frame.EP.server_ep_query.SQueries.server_query_local_app_out_len)
{
  let ev = server_driver_endpoint_send_event payload_bytes;
  unfold (EP.server_endpoint_frame_ready
    (DS.server_driver_canonical d)
    cfg
    frame
    (Ghost.reveal st0));
  unfold (SQueries.server_next_local_action_frame_ready
    (DS.server_driver_canonical d)
    cfg
    frame.EP.server_ep_query
    (Ghost.reveal st0));
  unfold (SQueries.server_network_persistent_resource
    frame.EP.server_ep_query);
  with network_current. _;
  unfold (SQueries.server_local_persistent_resource
    frame.EP.server_ep_query);
  with local_current. _;
  let old_local_out = Ghost.hide local_current;
  let local_base : SP.tls_server_local_frame = {
    SP.tls_server_local_payload = payload;
    SP.tls_server_local_payload_len = payload_len;
    SP.tls_server_local_app_out =
      frame.EP.server_ep_query.SQueries.server_query_local_app_out;
    SP.tls_server_local_app_out_len =
      frame.EP.server_ep_query.SQueries.server_query_local_app_out_len;
    SP.tls_server_local_old_app_out = old_local_out;
  };
  let local_frame : SP.tls_server_local_bridge_frame = {
    SP.tls_server_local_bridge_base = local_base;
  };
  unfold (EP.server_endpoint_io_ready
    (DS.server_driver_canonical d)
    ch
    frame
    (Ghost.reveal transport_received0)
    (Ghost.reveal transport_sent0)
    (Ghost.reveal st0));
  with raw_received raw_bytes network_out_bytes. _;
  rewrite
    (IO.is_channel ch raw_received (Ghost.reveal transport_sent0))
    as
    (IO.is_channel ch raw_received (Ghost.reveal canonical_sent0));
  rewrite
    (pts_to payload payload_bytes)
    as
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
      payload_bytes);
  rewrite
    (pts_to
      frame.EP.server_ep_query.SQueries.server_query_local_app_out
      local_current)
    as
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
      (Ghost.reveal old_local_out));
  fold (SP.server_local_bridge_frame_pre
    ev
    local_frame
    (Ghost.reveal st0)
    (V.vec_to_array frame.EP.server_ep_network_out)
    frame.EP.server_ep_network_out_len
    network_out_bytes);
  fold (EP.server_api_local_action_ready
    (DS.server_driver_canonical d)
    ch
    frame
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0)
    (Ghost.reveal st0)
    ev
    local_frame);
  fold (SQueries.server_network_persistent_resource
    frame.EP.server_ep_query);
  fold (server_endpoint_send_frame_remainder frame);
  rewrite
    (EP.server_api_local_action_ready
      (DS.server_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      ev
      local_frame)
    as
    (EP.server_api_local_action_ready
      (DS.server_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      (server_driver_endpoint_send_event payload_bytes)
      local_frame);
  local_frame
}

noextract
fn send_endpoint
  (d:server_driver)
  (cfg:SQueries.server_next_local_action_config)
  (frame:EP.server_endpoint_frame)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (payload_bytes:B.bytes)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires server_driver_endpoint_connected
              d
              cfg
              frame
              (Ghost.reveal st0)
              'certificate_chain
              'credential_identity
              (Ghost.reveal canonical_received0)
              (Ghost.reveal canonical_sent0) **
           pts_to payload payload_bytes **
           pure (B.length payload_bytes == SZ.v payload_len /\
                 ST.server_connection_control_not_failed (Ghost.reveal st0) /\
                 ST.server_local_event_input_ready
                   (Ghost.reveal st0)
                   ST.LocalSendApplicationData
                   payload_bytes)
  returns result:CPI.process_result
  ensures exists* (canonical_received1:Ghost.erased B.bytes)
                  (canonical_sent1:Ghost.erased B.bytes)
                  (st1:Ghost.erased CS.connection_state).
           server_driver_endpoint_connected
             d
             cfg
             frame
             (Ghost.reveal st1)
             'certificate_chain
             'credential_identity
             (Ghost.reveal canonical_received1)
             (Ghost.reveal canonical_sent1) **
           pts_to payload payload_bytes **
           pure (exists (old_out:B.bytes)
                        (out_contents:B.bytes)
                        (wire_outputs:list CW.wire_message)
                        (local_outputs:list CTypes.local_output).
             CPI.local_process_correct
               (SP.server_system
                 (Ghost.reveal
                   (server_driver_canonical d).SP.canonical_server_initial))
               (server_driver_endpoint_send_event payload_bytes)
               old_out
               out_contents
               frame.EP.server_ep_network_out_len
               (Ghost.reveal canonical_received0)
               (Ghost.reveal canonical_sent0)
               (Ghost.reveal st0)
               result
               (Ghost.reveal canonical_received1)
               (Ghost.reveal canonical_sent1)
               (Ghost.reveal st1)
               wire_outputs
               local_outputs)
{
  let ev = server_driver_endpoint_send_event payload_bytes;
  unfold (DS.server_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st0)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0));
  with ch buffered_len cv_input signature. _;
  expose_server_invariant_pure
    (DS.server_driver_canonical d)
    canonical_received0
    canonical_sent0
    st0;
  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite
    (EP.server_endpoint_io_ready
      (DS.server_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0))
    as
    (EP.server_endpoint_io_ready
      (DS.server_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0));
  let local_frame =
    prepare_endpoint_send_api_ready
      d
      cfg
      frame
      concrete_ch
      payload
      payload_len
      payload_bytes
      canonical_received0
      canonical_sent0
      canonical_received0
      canonical_sent0
      st0;
  rewrite
    (EP.server_api_local_action_ready
      (DS.server_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      (server_driver_endpoint_send_event payload_bytes)
      local_frame)
    as
    (EP.server_api_local_action_ready
      (DS.server_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      ev
      local_frame);
  let result =
    EP.server_run_api_local_action
      (DS.server_driver_canonical d)
      frame
      concrete_ch
      ev
      local_frame
      canonical_received0
      canonical_sent0
      st0;
  with received1 sent1 st1 old_out out_contents wire_outputs local_outputs.
    assert (
      SP.server_invariant
        (DS.server_driver_canonical d)
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      EP.server_endpoint_io_ready
        (DS.server_driver_canonical d)
        concrete_ch
        frame
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      SP.server_local_bridge_frame_post
        ev
        local_frame
        result
        (Ghost.reveal old_out)
        (Ghost.reveal out_contents)
        (Ghost.reveal st0)
        (Ghost.reveal st1)
        (Ghost.reveal wire_outputs)
        (Ghost.reveal local_outputs));
  assert (pure (ev == server_driver_endpoint_send_event payload_bytes));
  assert (pure (CPI.local_process_correct
    (SP.server_system
      (Ghost.reveal
        (server_driver_canonical d).SP.canonical_server_initial))
    (server_driver_endpoint_send_event payload_bytes)
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    frame.EP.server_ep_network_out_len
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)));
  expose_server_invariant_pure
    (DS.server_driver_canonical d)
    received1
    sent1
    st1;
  unfold (SP.server_local_bridge_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  with app_out. _;
  rewrite
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
      payload_bytes)
    as
    (pts_to payload payload_bytes);
  rewrite
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
      app_out)
    as
    (pts_to
      frame.EP.server_ep_query.SQueries.server_query_local_app_out
      app_out);
  unfold (server_endpoint_send_frame_remainder frame);
  fold (SQueries.server_local_persistent_resource
    frame.EP.server_ep_query);
  fold (SQueries.server_network_persistent_resource
    frame.EP.server_ep_query);
  fold (SQueries.server_next_local_action_frame_ready
    (DS.server_driver_canonical d)
    cfg
    frame.EP.server_ep_query
    (Ghost.reveal st1));
  fold (EP.server_endpoint_frame_ready
    (DS.server_driver_canonical d)
    cfg
    frame
    (Ghost.reveal st1));
  unfold (EP.server_endpoint_io_ready
    (DS.server_driver_canonical d)
    concrete_ch
    frame
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1));
  with raw_received1 raw_bytes1 network_out_bytes1. _;
  fold (EP.server_endpoint_io_ready
    (DS.server_driver_canonical d)
    concrete_ch
    frame
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1));
  rewrite
    (Box.pts_to d.server_driver_channel (Some ch))
    as
    (Box.pts_to d.server_driver_channel (Some concrete_ch));
  assert (pure (ST.server_end_to_end_invariant (Ghost.reveal st1)));
  assert (pure (DS.server_driver_config_matches_credentials
    (Ghost.reveal st1)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (SP.server_config_matches_credentials
    (Ghost.reveal (DS.server_driver_canonical d).SP.canonical_server_initial)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  (Ghost.reveal (DS.server_driver_canonical d).SP.canonical_server_supported_profile)
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity);
  assert (pure (SP.server_supported_profile_selection
    (Ghost.reveal st1)
    (Ghost.reveal 'credential_identity)));
  assert (pure (DS.server_driver_supported_profile_selection
    (Ghost.reveal st1)
    (Ghost.reveal 'credential_identity)));
  assert (pure (ST.server_end_to_end_invariant (Ghost.reveal st1) /\
    DS.server_driver_config_matches_credentials
      (Ghost.reveal st1)
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity) /\
    DS.server_driver_supported_profile_selection
      (Ghost.reveal st1)
      (Ghost.reveal 'credential_identity) /\
    SZ.v buffered_len <= SZ.v frame.EP.server_ep_raw_len /\
    B.length cv_input == SZ.v driver_certificate_verify_input_capacity /\
    B.length signature == SZ.v driver_signature_capacity /\
    Bounds.max_certificate_verify_input_len <=
      SZ.v driver_certificate_verify_input_capacity /\
    IM.max_signature_len <= SZ.v driver_signature_capacity /\
    V.is_full_vec d.server_driver_certificate_verify_input /\
    V.is_full_vec d.server_driver_signature));
  with concrete_ch buffered_len cv_input signature.
  fold (DS.server_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st1)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal received1)
    (Ghost.reveal sent1));
  assert (
    DS.server_driver_endpoint_connected
      d
      cfg
      frame
      (Ghost.reveal st1)
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity)
      (Ghost.reveal received1)
      (Ghost.reveal sent1) **
    pts_to payload payload_bytes **
    pure (CPI.local_process_correct
      (SP.server_system
        (Ghost.reveal
          (server_driver_canonical d).SP.canonical_server_initial))
      (server_driver_endpoint_send_event payload_bytes)
      (Ghost.reveal old_out)
      (Ghost.reveal out_contents)
      frame.EP.server_ep_network_out_len
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs)));
  result
}

noextract
fn receive_endpoint
  (d:server_driver)
  (cfg:SQueries.server_next_local_action_config)
  (frame:EP.server_endpoint_frame)
  (fuel:SZ.t)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires DS.server_driver_endpoint_connected
              d
              cfg
              frame
              (Ghost.reveal st0)
              'certificate_chain
              'credential_identity
              (Ghost.reveal canonical_received0)
              (Ghost.reveal canonical_sent0)
  returns result:EP.server_endpoint_run_result
  ensures exists* (canonical_received1:Ghost.erased B.bytes)
                  (canonical_sent1:Ghost.erased B.bytes)
                  (st1:Ghost.erased CS.connection_state).
           DS.server_driver_endpoint_connected
             d
             cfg
             frame
             (Ghost.reveal st1)
             'certificate_chain
             'credential_identity
             (Ghost.reveal canonical_received1)
             (Ghost.reveal canonical_sent1)
{
  unfold (DS.server_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st0)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0));
  with ch buffered_len cv_input signature. _;
  expose_server_invariant_pure
    (DS.server_driver_canonical d)
    canonical_received0
    canonical_sent0
    st0;
  assert (pure (SP.server_config_matches_credentials
    (Ghost.reveal (DS.server_driver_canonical d).SP.canonical_server_initial)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite
    (EP.server_endpoint_io_ready
      (DS.server_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0))
    as
    (EP.server_endpoint_io_ready
      (DS.server_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0));
  let result =
    EP.server_endpoint_run_workflow
      (DS.server_driver_canonical d)
      cfg
      frame
      concrete_ch
      d.server_driver_buffered_len
      true
      false
      false
      fuel
      canonical_received0
      canonical_sent0
      st0;
  with received1 sent1 st1 buffered_len1. _;
  expose_server_invariant_pure
    (DS.server_driver_canonical d)
    received1
    sent1
    st1;
  assert (pure (ST.server_end_to_end_invariant (Ghost.reveal st1)));
  assert (pure (SP.server_config_matches_credentials
    (Ghost.reveal (DS.server_driver_canonical d).SP.canonical_server_initial)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (DS.server_driver_config_matches_credentials
    (Ghost.reveal st1)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  (Ghost.reveal (DS.server_driver_canonical d).SP.canonical_server_supported_profile)
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity);
  assert (pure (DS.server_driver_supported_profile_selection
    (Ghost.reveal st1)
    (Ghost.reveal 'credential_identity)));
  rewrite
    (Box.pts_to d.server_driver_channel (Some ch))
    as
    (Box.pts_to d.server_driver_channel (Some concrete_ch));
  with concrete_ch buffered_len1 cv_input signature.
  fold (DS.server_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st1)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal received1)
    (Ghost.reveal sent1));
  result
}

noextract
fn prepare_endpoint_close_api_ready
  (d:server_driver)
  (cfg:SQueries.server_next_local_action_config)
  (frame:EP.server_endpoint_frame)
  (ch:IO.channel)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (transport_received0:Ghost.erased B.bytes)
  (transport_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires EP.server_endpoint_frame_ready
             (DS.server_driver_canonical d)
             cfg
             frame
             (Ghost.reveal st0) **
           EP.server_endpoint_io_ready
             (DS.server_driver_canonical d)
             ch
             frame
             (Ghost.reveal transport_received0)
             (Ghost.reveal transport_sent0)
             (Ghost.reveal st0) **
           pts_to payload B.empty **
           pure (SZ.v payload_len == 0 /\
                 Seq.equal (Ghost.reveal canonical_sent0) (Ghost.reveal transport_sent0) /\
                 ST.server_local_event_input_ready
                   (Ghost.reveal st0)
                   ST.LocalSendCloseNotify
                   B.empty)
  returns local_frame:SP.tls_server_local_bridge_frame
  ensures EP.server_api_local_action_ready
            (DS.server_driver_canonical d)
            ch
            frame
            (Ghost.reveal canonical_received0)
            (Ghost.reveal canonical_sent0)
            (Ghost.reveal st0)
            server_driver_endpoint_close_event
            local_frame **
          server_endpoint_send_frame_remainder frame **
          pure (
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload == payload /\
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload_len == payload_len /\
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out ==
              frame.EP.server_ep_query.SQueries.server_query_local_app_out /\
            local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out_len ==
              frame.EP.server_ep_query.SQueries.server_query_local_app_out_len)
{
  let ev = server_driver_endpoint_close_event;
  assert (pure (B.length B.empty == SZ.v payload_len));
  unfold (EP.server_endpoint_frame_ready
    (DS.server_driver_canonical d)
    cfg
    frame
    (Ghost.reveal st0));
  unfold (SQueries.server_next_local_action_frame_ready
    (DS.server_driver_canonical d)
    cfg
    frame.EP.server_ep_query
    (Ghost.reveal st0));
  unfold (SQueries.server_network_persistent_resource
    frame.EP.server_ep_query);
  with network_current. _;
  unfold (SQueries.server_local_persistent_resource
    frame.EP.server_ep_query);
  with local_current. _;
  let old_local_out = Ghost.hide local_current;
  let local_base : SP.tls_server_local_frame = {
    SP.tls_server_local_payload = payload;
    SP.tls_server_local_payload_len = payload_len;
    SP.tls_server_local_app_out =
      frame.EP.server_ep_query.SQueries.server_query_local_app_out;
    SP.tls_server_local_app_out_len =
      frame.EP.server_ep_query.SQueries.server_query_local_app_out_len;
    SP.tls_server_local_old_app_out = old_local_out;
  };
  let local_frame : SP.tls_server_local_bridge_frame = {
    SP.tls_server_local_bridge_base = local_base;
  };
  unfold (EP.server_endpoint_io_ready
    (DS.server_driver_canonical d)
    ch
    frame
    (Ghost.reveal transport_received0)
    (Ghost.reveal transport_sent0)
    (Ghost.reveal st0));
  with raw_received raw_bytes network_out_bytes. _;
  rewrite
    (IO.is_channel ch raw_received (Ghost.reveal transport_sent0))
    as
    (IO.is_channel ch raw_received (Ghost.reveal canonical_sent0));
  rewrite
    (pts_to payload B.empty)
    as
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
      B.empty);
  rewrite
    (pts_to
      frame.EP.server_ep_query.SQueries.server_query_local_app_out
      local_current)
    as
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
      (Ghost.reveal old_local_out));
  fold (SP.server_local_bridge_frame_pre
    ev
    local_frame
    (Ghost.reveal st0)
    (V.vec_to_array frame.EP.server_ep_network_out)
    frame.EP.server_ep_network_out_len
    network_out_bytes);
  fold (EP.server_api_local_action_ready
    (DS.server_driver_canonical d)
    ch
    frame
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0)
    (Ghost.reveal st0)
    ev
    local_frame);
  fold (SQueries.server_network_persistent_resource
    frame.EP.server_ep_query);
  fold (server_endpoint_send_frame_remainder frame);
  rewrite
    (EP.server_api_local_action_ready
      (DS.server_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      ev
      local_frame)
    as
    (EP.server_api_local_action_ready
      (DS.server_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      server_driver_endpoint_close_event
      local_frame);
  local_frame
}

noextract
fn close_endpoint
  (d:server_driver)
  (cfg:SQueries.server_next_local_action_config)
  (frame:EP.server_endpoint_frame)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (canonical_received0:Ghost.erased B.bytes)
  (canonical_sent0:Ghost.erased B.bytes)
  (st0:Ghost.erased CS.connection_state)
  requires DS.server_driver_endpoint_connected
              d
              cfg
              frame
              (Ghost.reveal st0)
              'certificate_chain
              'credential_identity
              (Ghost.reveal canonical_received0)
              (Ghost.reveal canonical_sent0) **
           pts_to payload B.empty **
           pure (SZ.v payload_len == 0 /\
                 ST.server_connection_control_not_failed (Ghost.reveal st0) /\
                 ST.server_local_event_input_ready
                   (Ghost.reveal st0)
                   ST.LocalSendCloseNotify
                   B.empty)
  returns result:CPI.process_result
  ensures exists* (canonical_received1:Ghost.erased B.bytes)
                  (canonical_sent1:Ghost.erased B.bytes)
                  (st1:Ghost.erased CS.connection_state).
           DS.server_driver_endpoint_connected
             d
             cfg
             frame
             (Ghost.reveal st1)
             'certificate_chain
             'credential_identity
             (Ghost.reveal canonical_received1)
             (Ghost.reveal canonical_sent1) **
           pts_to payload B.empty **
           pure (exists (old_out:B.bytes)
                         (out_contents:B.bytes)
                         (wire_outputs:list CW.wire_message)
                         (local_outputs:list CTypes.local_output).
             CPI.local_process_correct
               (SP.server_system
                 (Ghost.reveal
                   (server_driver_canonical d).SP.canonical_server_initial))
               server_driver_endpoint_close_event
               old_out
               out_contents
               frame.EP.server_ep_network_out_len
               (Ghost.reveal canonical_received0)
               (Ghost.reveal canonical_sent0)
               (Ghost.reveal st0)
               result
               (Ghost.reveal canonical_received1)
               (Ghost.reveal canonical_sent1)
               (Ghost.reveal st1)
               wire_outputs
               local_outputs)
{
  let ev = server_driver_endpoint_close_event;
  unfold (DS.server_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st0)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0));
  with ch buffered_len cv_input signature. _;
  expose_server_invariant_pure
    (DS.server_driver_canonical d)
    canonical_received0
    canonical_sent0
    st0;
  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite
    (EP.server_endpoint_io_ready
      (DS.server_driver_canonical d)
      ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0))
    as
    (EP.server_endpoint_io_ready
      (DS.server_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0));
  let local_frame =
    prepare_endpoint_close_api_ready
      d
      cfg
      frame
      concrete_ch
      payload
      payload_len
      canonical_received0
      canonical_sent0
      canonical_received0
      canonical_sent0
      st0;
  rewrite
    (EP.server_api_local_action_ready
      (DS.server_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      server_driver_endpoint_close_event
      local_frame)
    as
    (EP.server_api_local_action_ready
      (DS.server_driver_canonical d)
      concrete_ch
      frame
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      ev
      local_frame);
  let result =
    EP.server_run_api_local_action
      (DS.server_driver_canonical d)
      frame
      concrete_ch
      ev
      local_frame
      canonical_received0
      canonical_sent0
      st0;
  with received1 sent1 st1 old_out out_contents wire_outputs local_outputs.
    assert (
      SP.server_invariant
        (DS.server_driver_canonical d)
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      EP.server_endpoint_io_ready
        (DS.server_driver_canonical d)
        concrete_ch
        frame
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      SP.server_local_bridge_frame_post
        ev
        local_frame
        result
        (Ghost.reveal old_out)
        (Ghost.reveal out_contents)
        (Ghost.reveal st0)
        (Ghost.reveal st1)
        (Ghost.reveal wire_outputs)
        (Ghost.reveal local_outputs));
  assert (pure (ev == server_driver_endpoint_close_event));
  assert (pure (CPI.local_process_correct
    (SP.server_system
      (Ghost.reveal
        (server_driver_canonical d).SP.canonical_server_initial))
    server_driver_endpoint_close_event
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    frame.EP.server_ep_network_out_len
    (Ghost.reveal canonical_received0)
    (Ghost.reveal canonical_sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)));
  expose_server_invariant_pure
    (DS.server_driver_canonical d)
    received1
    sent1
    st1;
  unfold (SP.server_local_bridge_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  with app_out. _;
  rewrite
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_payload
      B.empty)
    as
    (pts_to payload B.empty);
  rewrite
    (pts_to
      local_frame.SP.tls_server_local_bridge_base.SP.tls_server_local_app_out
      app_out)
    as
    (pts_to
      frame.EP.server_ep_query.SQueries.server_query_local_app_out
      app_out);
  unfold (server_endpoint_send_frame_remainder frame);
  fold (SQueries.server_local_persistent_resource
    frame.EP.server_ep_query);
  fold (SQueries.server_network_persistent_resource
    frame.EP.server_ep_query);
  fold (SQueries.server_next_local_action_frame_ready
    (DS.server_driver_canonical d)
    cfg
    frame.EP.server_ep_query
    (Ghost.reveal st1));
  fold (EP.server_endpoint_frame_ready
    (DS.server_driver_canonical d)
    cfg
    frame
    (Ghost.reveal st1));
  unfold (EP.server_endpoint_io_ready
    (DS.server_driver_canonical d)
    concrete_ch
    frame
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1));
  with raw_received1 raw_bytes1 network_out_bytes1. _;
  fold (EP.server_endpoint_io_ready
    (DS.server_driver_canonical d)
    concrete_ch
    frame
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1));
  rewrite
    (Box.pts_to d.server_driver_channel (Some ch))
    as
    (Box.pts_to d.server_driver_channel (Some concrete_ch));
  assert (pure (ST.server_end_to_end_invariant (Ghost.reveal st1)));
  assert (pure (DS.server_driver_config_matches_credentials
    (Ghost.reveal st1)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  assert (pure (SP.server_config_matches_credentials
    (Ghost.reveal (DS.server_driver_canonical d).SP.canonical_server_initial)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)));
  (Ghost.reveal (DS.server_driver_canonical d).SP.canonical_server_supported_profile)
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal st1)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity);
  assert (pure (SP.server_supported_profile_selection
    (Ghost.reveal st1)
    (Ghost.reveal 'credential_identity)));
  assert (pure (DS.server_driver_supported_profile_selection
    (Ghost.reveal st1)
    (Ghost.reveal 'credential_identity)));
  assert (pure (ST.server_end_to_end_invariant (Ghost.reveal st1) /\
    DS.server_driver_config_matches_credentials
      (Ghost.reveal st1)
      (Ghost.reveal 'certificate_chain)
      (Ghost.reveal 'credential_identity) /\
    DS.server_driver_supported_profile_selection
      (Ghost.reveal st1)
      (Ghost.reveal 'credential_identity) /\
    SZ.v buffered_len <= SZ.v frame.EP.server_ep_raw_len /\
    B.length cv_input == SZ.v driver_certificate_verify_input_capacity /\
    B.length signature == SZ.v driver_signature_capacity /\
    Bounds.max_certificate_verify_input_len <=
      SZ.v driver_certificate_verify_input_capacity /\
    IM.max_signature_len <= SZ.v driver_signature_capacity /\
    V.is_full_vec d.server_driver_certificate_verify_input /\
    V.is_full_vec d.server_driver_signature));
  with concrete_ch buffered_len cv_input signature.
  fold (DS.server_driver_endpoint_connected
    d
    cfg
    frame
    (Ghost.reveal st1)
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal received1)
    (Ghost.reveal sent1));
  assert (pure (exists (old_out0:B.bytes)
                       (out_contents0:B.bytes)
                       (wire_outputs0:list CW.wire_message)
                       (local_outputs0:list CTypes.local_output).
    CPI.local_process_correct
      (SP.server_system
        (Ghost.reveal
          (server_driver_canonical d).SP.canonical_server_initial))
      server_driver_endpoint_close_event
      old_out0
      out_contents0
      frame.EP.server_ep_network_out_len
      (Ghost.reveal canonical_received0)
      (Ghost.reveal canonical_sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      wire_outputs0
      local_outputs0));
  result
}

fn receive
  (d:server_driver)
  (out:array U8.t)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pts_to out 'out_bytes **
           pure (B.length 'out_bytes == SZ.v out_len)
  returns result:server_receive_result
  ensures exists* st1 received' sent' out_bytes.
          server_driver_connected
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent' **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                SZ.v result.server_receive_len <= SZ.v out_len /\
                st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
                server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
                server_driver_sent_log_exact st1 sent' /\
                server_driver_received_log_accounted st1 received' /\
                (exists loop app_out.
                  server_driver_receive_correct
                    'st0
                    st1
                    result
                    loop
                    (Ghost.reveal 'sent)
                    sent'
                    app_out
                    out_bytes))
{
  unfold (server_driver_connected
    d
    'st0
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent));
  with ch0 buffered0 buffered_len0.
    assert (Box.pts_to d.server_driver_channel (Some ch0) **
            IO.is_channel ch0 (Ghost.reveal 'received) (Ghost.reveal 'sent) **
            server_driver_buffers d buffered0 buffered_len0 **
            pure (server_driver_wire_logs_match
              'st0
              (Ghost.reveal 'received)
              (Ghost.reveal 'sent)
              buffered0
              buffered_len0));
  assert (pure (server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent)));
  lemma_server_driver_wire_logs_match_received_accounted
    'st0
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent)
    buffered0
    buffered_len0;
  assert (pure (server_driver_received_log_accounted 'st0 (Ghost.reveal 'received)));
  fold (server_driver_connected
    d
    'st0
    (Ghost.reveal 'certificate_chain)
    (Ghost.reveal 'credential_identity)
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent));
  let loop = read_process_network_until_ready d network_fuel;
  with st1 received' sent' loop_app_out.
    assert (server_driver_connected_with_app_out
      d
      st1
      'certificate_chain
      'credential_identity
      received'
      sent'
      loop_app_out **
      pure (st1.CS.cs_model.CS.model_config ==
        'st0.CS.cs_model.CS.model_config /\
      (loop.server_driver_network_loop_exhausted == false ==>
        loop.server_driver_network_loop_last.ST.response.ST.status <>
          ST.NeedMoreInput /\
        server_driver_network_process_correct
          'st0
          st1
            loop.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent' /\
          server_driver_network_process_correct_for_app_out
            'st0
            st1
            loop.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent'
            loop_app_out)));
  unfold (server_driver_connected_with_app_out
    d
    st1
    'certificate_chain
    'credential_identity
    received'
    sent'
    loop_app_out);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch received' sent' **
            server_driver_buffers_with_app_out d buffered buffered_len loop_app_out **
            pure (server_driver_wire_logs_match st1 received' sent' buffered buffered_len));
  assert (pure (server_driver_sent_log_exact st1 sent'));
  lemma_server_driver_wire_logs_match_received_accounted
    st1
    received'
    sent'
    buffered
    buffered_len;
  assert (pure (server_driver_received_log_accounted st1 received'));
  fold (server_driver_connected_with_app_out
    d
    st1
    'certificate_chain
    'credential_identity
    received'
    sent'
    loop_app_out);
  if (loop.server_driver_network_loop_exhausted) {
    let result = {
      server_receive_status = ServerWorkflowExhausted;
      server_receive_len = 0sz;
    };
    assert (pure (server_driver_receive_correct
      'st0
      st1
      result
      loop
      (Ghost.reveal 'sent)
      sent'
      B.empty
      (Ghost.reveal 'out_bytes)));
    forget_server_driver_connected_app_out d;
    result
  } else {
    match loop.server_driver_network_loop_last.ST.response.ST.status {
      ST.StepOk -> {
        unfold (server_driver_connected_with_app_out
          d
          st1
          'certificate_chain
          'credential_identity
          received'
          sent'
          loop_app_out);
        with ch buffered buffered_len.
          assert (Box.pts_to d.server_driver_channel (Some ch) **
                  IO.is_channel ch received' sent' **
                  server_driver_buffers_with_app_out
                    d
                    buffered
                    buffered_len
                    loop_app_out);
        unfold (server_driver_buffers_with_app_out
          d
          buffered
          buffered_len
          loop_app_out);
        with empty_payload raw network_out material cv_input signature local_app_out.
          assert (
            Box.pts_to d.server_driver_buffered_len buffered_len **
            V.pts_to d.server_driver_empty_payload #1.0R empty_payload **
            V.pts_to d.server_driver_raw #1.0R raw **
            V.pts_to d.server_driver_network_out #1.0R network_out **
            V.pts_to d.server_driver_material_payload #1.0R material **
            V.pts_to d.server_driver_certificate_verify_input #1.0R cv_input **
            V.pts_to d.server_driver_signature #1.0R signature **
            V.pts_to d.server_driver_app_out #1.0R loop_app_out **
            V.pts_to d.server_driver_local_app_out #1.0R local_app_out);
        let copy_len = loop.server_driver_network_loop_last.ST.response.ST.app_out_len;
        let app_fits = SZ.lte copy_len out_len;
        let app_src_fits = SZ.lte copy_len DS.driver_app_out_capacity;
        if (app_fits && app_src_fits) {
          V.to_array_pts_to d.server_driver_app_out;
          A.pts_to_len (V.vec_to_array d.server_driver_app_out);
          A.pts_to_len out;
          assert (pure (SZ.v copy_len <= SZ.v out_len));
          assert (pure (SZ.v copy_len <= SZ.v DS.driver_app_out_capacity));
          assert (pure (B.length loop_app_out == SZ.v DS.driver_app_out_capacity));
          assert (pure (A.length (V.vec_to_array d.server_driver_app_out) ==
            B.length loop_app_out));
          assert (pure (A.length out == SZ.v out_len));
          assert (pure (SZ.v copy_len <= A.length (V.vec_to_array d.server_driver_app_out)));
          assert (pure (SZ.v copy_len <= A.length out));
          let _ = A.memcpy_l copy_len (V.vec_to_array d.server_driver_app_out) out;
          with out_bytes.
            assert (pts_to out out_bytes);
          A.pts_to_len out;
          assert (pure (B.length out_bytes == SZ.v out_len));
          assert (pure (SZ.v copy_len <= B.length loop_app_out));
          assert (pure (Seq.equal
            (ST.response_app_out
              loop.server_driver_network_loop_last.ST.response
              loop_app_out)
            (Seq.slice loop_app_out 0 (SZ.v copy_len))));
          Seq.lemma_len_slice out_bytes 0 (SZ.v copy_len);
          Seq.lemma_len_slice loop_app_out 0 (SZ.v copy_len);
          assert (pure (Seq.equal
            out_bytes
            (Seq.append
              (Seq.slice loop_app_out 0 (SZ.v copy_len))
              (Seq.slice (Ghost.reveal 'out_bytes) (SZ.v copy_len) (A.length out)))));
          Seq.lemma_len_slice loop_app_out 0 (SZ.v copy_len);
          assert (pure (Seq.length (Seq.slice loop_app_out 0 (SZ.v copy_len)) == SZ.v copy_len));
          SeqP.append_slices
            (Seq.slice loop_app_out 0 (SZ.v copy_len))
            (Seq.slice (Ghost.reveal 'out_bytes) (SZ.v copy_len) (A.length out));
          Seq.lemma_eq_elim
            out_bytes
            (Seq.append
              (Seq.slice loop_app_out 0 (SZ.v copy_len))
              (Seq.slice (Ghost.reveal 'out_bytes) (SZ.v copy_len) (A.length out)));
          assert (pure (Seq.equal
            (Seq.slice out_bytes 0 (SZ.v copy_len))
            (Seq.slice loop_app_out 0 (SZ.v copy_len))));
          V.to_vec_pts_to d.server_driver_app_out;
          fold (server_driver_buffers_with_app_out
            d
            buffered
            buffered_len
            loop_app_out);
          fold (server_driver_connected_with_app_out
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent'
            loop_app_out);
          let result = {
            server_receive_status = ServerWorkflowOk;
            server_receive_len = copy_len;
          };
          assert (pure (server_driver_network_process_correct_for_app_out
            'st0
            st1
            loop.server_driver_network_loop_last
            (Ghost.reveal 'sent)
            sent'
            loop_app_out));
          assert (pure (server_driver_receive_copyout_correct
            result
            loop.server_driver_network_loop_last.ST.response
            loop_app_out
            out_bytes));
          assert (pure (server_driver_receive_correct
            'st0
            st1
            result
            loop
            (Ghost.reveal 'sent)
            sent'
            loop_app_out
            out_bytes));
          forget_server_driver_connected_app_out d;
          result
        } else {
          fold (server_driver_buffers_with_app_out
            d
            buffered
            buffered_len
            loop_app_out);
          fold (server_driver_connected_with_app_out
            d
            st1
            'certificate_chain
            'credential_identity
            received'
            sent'
            loop_app_out);
          let result = {
            server_receive_status = ServerWorkflowStepFailed;
            server_receive_len = 0sz;
          };
          assert (pure (server_driver_receive_correct
            'st0
            st1
            result
            loop
            (Ghost.reveal 'sent)
            sent'
            loop_app_out
            (Ghost.reveal 'out_bytes)));
          forget_server_driver_connected_app_out d;
          result
        }
      }
      ST.NeedMoreInput -> {
        let result = {
          server_receive_status = ServerWorkflowNeedMoreInput;
          server_receive_len = 0sz;
        };
        assert (pure (server_driver_receive_correct
          'st0
          st1
          result
          loop
          (Ghost.reveal 'sent)
          sent'
          loop_app_out
          (Ghost.reveal 'out_bytes)));
        forget_server_driver_connected_app_out d;
        result
      }
      ST.DecodeError -> {
        let result = {
          server_receive_status = ServerWorkflowStepFailed;
          server_receive_len = 0sz;
        };
        assert (pure (server_driver_receive_correct
          'st0
          st1
          result
          loop
          (Ghost.reveal 'sent)
          sent'
          loop_app_out
          (Ghost.reveal 'out_bytes)));
        forget_server_driver_connected_app_out d;
        result
      }
      ST.IllegalTransition -> {
        let result = {
          server_receive_status = ServerWorkflowStepFailed;
          server_receive_len = 0sz;
        };
        assert (pure (server_driver_receive_correct
          'st0
          st1
          result
          loop
          (Ghost.reveal 'sent)
          sent'
          loop_app_out
          (Ghost.reveal 'out_bytes)));
        forget_server_driver_connected_app_out d;
        result
      }
      ST.OutputBufferTooSmall -> {
        let result = {
          server_receive_status = ServerWorkflowStepFailed;
          server_receive_len = 0sz;
        };
        assert (pure (server_driver_receive_correct
          'st0
          st1
          result
          loop
          (Ghost.reveal 'sent)
          sent'
          loop_app_out
          (Ghost.reveal 'out_bytes)));
        forget_server_driver_connected_app_out d;
        result
      }
      ST.ConnectionFailed -> {
        let result = {
          server_receive_status = ServerWorkflowStepFailed;
          server_receive_len = 0sz;
        };
        assert (pure (server_driver_receive_correct
          'st0
          st1
          result
          loop
          (Ghost.reveal 'sent)
          sent'
          loop_app_out
          (Ghost.reveal 'out_bytes)));
        forget_server_driver_connected_app_out d;
        result
      }
    }
  }
}

fn close
  (d:server_driver)
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires server_driver_connected
              d
              'st0
              'certificate_chain
              'credential_identity
              'received
              'sent **
           pure (server_driver_application_ready 'st0)
  returns status:server_workflow_status
  ensures exists* st1.
          server_driver_closed d st1 'certificate_chain 'credential_identity **
          pure (status == ServerWorkflowClosed /\
                st1.CS.cs_model.CS.model_config ==
                  'st0.CS.cs_model.CS.model_config /\
                server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
                server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
                server_driver_close_correct
                  'st0
                  st1
                  (Ghost.reveal 'sent))
{
  unfold (server_driver_connected
   d
   'st0
   (Ghost.reveal 'certificate_chain)
   (Ghost.reveal 'credential_identity)
   (Ghost.reveal 'received)
   (Ghost.reveal 'sent));
  with ch0 buffered0 buffered_len0.
   assert (Box.pts_to d.server_driver_channel (Some ch0) **
           IO.is_channel ch0 (Ghost.reveal 'received) (Ghost.reveal 'sent) **
           server_driver_buffers d buffered0 buffered_len0 **
           pure (server_driver_wire_logs_match
             'st0
             (Ghost.reveal 'received)
             (Ghost.reveal 'sent)
             buffered0
             buffered_len0));
  assert (pure (server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent)));
  lemma_server_driver_wire_logs_match_received_accounted
   'st0
   (Ghost.reveal 'received)
   (Ghost.reveal 'sent)
   buffered0
   buffered_len0;
  assert (pure (server_driver_received_log_accounted 'st0 (Ghost.reveal 'received)));
  fold (server_driver_connected
   d
   'st0
   (Ghost.reveal 'certificate_chain)
   (Ghost.reveal 'credential_identity)
   (Ghost.reveal 'received)
   (Ghost.reveal 'sent));
  lemma_application_ready_close_notify_ready 'st0;
  let resp = DL.send_close_notify_once d;
  with st1 sent'.
    assert (server_driver_connected
      d
      st1
      'certificate_chain
      'credential_identity
      'received
      sent');
  lemma_server_driver_local_write_correct_preserves_config
    'st0
    st1
    resp
    ST.LocalSendCloseNotify
    B.empty
    (Ghost.reveal 'sent)
    sent';
  assert (pure (server_driver_close_correct
    'st0
    st1
    (Ghost.reveal 'sent)));
  close_transport_once d;
  assert (server_driver_closed d st1 'certificate_chain 'credential_identity);
  assert (pure (ServerWorkflowClosed == ServerWorkflowClosed /\
    st1.CS.cs_model.CS.model_config ==
      'st0.CS.cs_model.CS.model_config /\
    server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
    server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
    server_driver_close_correct
      'st0
      st1
      (Ghost.reveal 'sent)));
  assert (exists* st_after.
    server_driver_closed d st_after 'certificate_chain 'credential_identity **
    pure (ServerWorkflowClosed == ServerWorkflowClosed /\
          st_after.CS.cs_model.CS.model_config ==
            'st0.CS.cs_model.CS.model_config /\
          server_driver_sent_log_exact 'st0 (Ghost.reveal 'sent) /\
          server_driver_received_log_accounted 'st0 (Ghost.reveal 'received) /\
          server_driver_close_correct
            'st0
            st_after
            (Ghost.reveal 'sent)));
  ServerWorkflowClosed
}
