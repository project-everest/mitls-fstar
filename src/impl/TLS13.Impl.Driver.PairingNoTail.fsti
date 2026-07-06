module TLS13.Impl.Driver.PairingNoTail

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module CD = TLS13.Impl.Client.Driver
module ClientCP = TLS13.Impl.Client.CanonicalProtocol
module CS = TLS13.Spec.ConnectionState
module Pairing = TLS13.Impl.Driver.Pairing
module PTS = TLS13.Impl.Driver.PairingTraceShape
module SD = TLS13.Impl.Server.Driver
module Seq = FStar.Seq
module ServerCP = TLS13.Impl.Server.CanonicalProtocol
module SM = Common.StateMachine
module TCP = Common.TCP
module WFSM = Common.WireFormatStateMachine

val lemma_valid_byte_trace_inverts_to_state_trace
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine
    state
    wire_message
    local_event
    local_output)
  (input_bytes:TCP.bytes)
  (st1:state)
  (output_bytes:TCP.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        WFSM.valid_byte_trace
          system
          input_bytes
          st1
          output_bytes
          residual_input)
      (ensures
        exists trace.
          SM.trace_reaches
            system.WFSM.wfsm_state_machine
            system.WFSM.wfsm_state_machine.SM.sm_initial_state
            trace
            st1)

val lemma_client_valid_byte_trace_preserves_connection_state_consistent
  (client_initial:CS.connection_state)
  (client:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        CS.connection_state_consistent client_initial /\
        WFSM.valid_byte_trace
          (ClientCP.client_system client_initial)
          client_received
          client
          client_sent
          residual_input)
      (ensures CS.connection_state_consistent client)

val lemma_server_valid_byte_trace_preserves_connection_state_consistent
  (server_initial:CS.connection_state)
  (server:CS.connection_state)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        CS.connection_state_consistent server_initial /\
        WFSM.valid_byte_trace
          (ServerCP.server_system server_initial)
          server_received
          server
          server_sent
          residual_input)
      (ensures CS.connection_state_consistent server)

val lemma_client_valid_byte_trace_preserves_connection_state_replay_consistent
  (client_initial:CS.connection_state)
  (client:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        CS.connection_state_sent_seal_replay_consistent client_initial /\
        CS.connection_state_received_decode_replay_consistent client_initial /\
        WFSM.valid_byte_trace
          (ClientCP.client_system client_initial)
          client_received
          client
          client_sent
          residual_input)
      (ensures
        CS.connection_state_sent_seal_replay_consistent client /\
        CS.connection_state_received_decode_replay_consistent client)

val lemma_server_valid_byte_trace_preserves_connection_state_replay_consistent
  (server_initial:CS.connection_state)
  (server:CS.connection_state)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        CS.connection_state_sent_seal_replay_consistent server_initial /\
        CS.connection_state_received_decode_replay_consistent server_initial /\
        WFSM.valid_byte_trace
          (ServerCP.server_system server_initial)
          server_received
          server
          server_sent
          residual_input)
      (ensures
        CS.connection_state_sent_seal_replay_consistent server /\
        CS.connection_state_received_decode_replay_consistent server)

noextract
let client_no_tail_application_ready_boundary
  (client:CS.connection_state)
  : prop =
  CD.client_driver_application_ready client /\
  FStar.List.Tot.length client.CS.cs_event_log == 16

noextract
let server_no_tail_application_ready_boundary
  (server:CS.connection_state)
  : prop =
  // Stale milestone boundary: the satisfiable final server no-tail shape should
  // include the server handshake read-key install before ClientFinished, making
  // the server length 16.  Keep this predicate only for the older exact-shape
  // wrappers until the role-local inversion stack is corrected.
  SD.server_driver_application_ready server /\
  FStar.List.Tot.length server.CS.cs_event_log == 15

noextract
let server_no_tail_application_ready_boundary16
  (server:CS.connection_state)
  : prop =
  // Corrected server no-tail boundary: the server must install both handshake
  // directions before receiving the protected ClientFinished, so the final
  // satisfiable no-tail length is 16.
  SD.server_driver_application_ready server /\
  FStar.List.Tot.length server.CS.cs_event_log == 16

noextract
let paired_no_tail_application_ready_boundary
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_no_tail_application_ready_boundary client /\
  server_no_tail_application_ready_boundary server

noextract
let paired_no_tail_application_ready_boundary16
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  client_no_tail_application_ready_boundary client /\
  server_no_tail_application_ready_boundary16 server

val lemma_paired_successful_handshake_complete_event_log_shape_no_tail
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PTS.paired_successful_handshake_complete_event_log_shape client server)
      (ensures
        FStar.List.Tot.length client.CS.cs_event_log == 16 /\
        FStar.List.Tot.length server.CS.cs_event_log == 15 /\
        CS.connection_state_no_key_update_trace client /\
        CS.connection_state_no_key_update_trace server)

val lemma_paired_successful_handshake_complete_state_trace_no_tail
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        PTS.paired_successful_handshake_complete_state_trace client server)
      (ensures
        paired_no_tail_application_ready_boundary client server /\
        CS.connection_state_no_key_update_trace client /\
        CS.connection_state_no_key_update_trace server)

noextract
let paired_no_tail_state_trace_with_paired_handshake_event_trace
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  paired_no_tail_application_ready_boundary client server /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server /\
  Pairing.paired_handshake_event_trace client server

val lemma_client_server_application_record_material_agrees_from_no_tail_state_trace_with_paired_handshake_event_trace
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        paired_no_tail_state_trace_with_paired_handshake_event_trace
          client
          server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)

noextract
let paired_valid_byte_traces_at_no_tail_boundary_with_paired_handshake_event_trace
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  WFSM.valid_byte_trace
    (ClientCP.client_system client_initial)
    client_received
    client
    client_sent
    Seq.empty /\
  WFSM.valid_byte_trace
    (ServerCP.server_system server_initial)
    server_received
    server
    server_sent
    Seq.empty /\
  Seq.equal client_sent server_received /\
  Seq.equal server_sent client_received /\
  paired_no_tail_state_trace_with_paired_handshake_event_trace
    client
    server

val lemma_client_server_application_record_material_agrees_from_valid_byte_traces_at_no_tail_boundary_with_paired_handshake_event_trace
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        paired_valid_byte_traces_at_no_tail_boundary_with_paired_handshake_event_trace
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)

val lemma_successful_handshake_complete_state_trace_from_no_tail_event_log_shape
  (client:CS.connection_state)
  (server:CS.connection_state)
  : Lemma
      (requires
        paired_no_tail_application_ready_boundary client server /\
        CS.paired_wire_logs client server /\
        Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
          client
          server /\
        PTS.paired_successful_handshake_complete_event_log_shape client server)
      (ensures
        PTS.paired_successful_handshake_complete_state_trace client server)

noextract
let paired_valid_byte_traces_at_no_tail_boundary_with_successful_event_log_shape
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  WFSM.valid_byte_trace
    (ClientCP.client_system client_initial)
    client_received
    client
    client_sent
    Seq.empty /\
  WFSM.valid_byte_trace
    (ServerCP.server_system server_initial)
    server_received
    server
    server_sent
    Seq.empty /\
  Seq.equal client_sent server_received /\
  Seq.equal server_sent client_received /\
  paired_no_tail_application_ready_boundary client server /\
  CS.paired_wire_logs client server /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server /\
  PTS.paired_successful_handshake_complete_event_log_shape client server

val lemma_client_server_application_record_material_agrees_from_valid_byte_traces_at_no_tail_boundary_with_successful_event_log_shape
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        paired_valid_byte_traces_at_no_tail_boundary_with_successful_event_log_shape
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic)
          client
          server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic)
          client
          server)

(**
  STATUS / HONESTY NOTE -- please read before citing this predicate as an
  audit surface.

  An earlier version of this predicate required
  [TLS13.Impl.Driver.PairingNormalizedBoundary.paired_supported_normalized_replay_boundary],
  an AEAD-level protected-replay/projection witness (an explicit
  [PairingCleanBoundary.handshake_complete_boundary_witnesses] record threading
  ~30 intermediate connection-state [CS.step_model] transitions).  That witness
  is undeniably heavy, so a later revision swapped it for the
  message-content-level trace-shape boundary in
  [TLS13.Impl.Driver.PairingTraceShape], namely
  [PTS.paired_successful_handshake_complete_event_log_shape].  That swap is
  *not* the clean win it may look like, and this predicate should not be
  described as "clean" or as avoiding a strong extra hypothesis: it still
  demands, buried inside [PTS.paired_successful_handshake_complete_event_log_shape],
  that both endpoints' final handshake-model slots hold *the same* record value
  for each of ClientHello, ServerHello, EncryptedExtensions, Certificate and
  CertificateVerify (e.g. [client.hs_client_hello == Some ch /\
  server.hs_client_hello == Some ch] for one shared [ch]).

  That is too strong for real, wire-driven byte traces.  [M.client_hello],
  [M.server_hello], [M.encrypted_extensions], [M.certificate_msg] and
  [M.certificate_verify] all carry a raw [body: bytes] field alongside their
  structured fields, and the two endpoints do not populate it the same way:
  the sending/generating side's local copy of a message it authored does not
  need to retain the wire fragment, while the receiving/parsing side's copy is
  produced by the wire parser and carries the fragment it actually read off
  the network (see the discussion at the top of
  [TLS13.Spec.WireFormatLemmas], e.g. [server_hello_wire_equivalent]'s doc
  comment).  So on a genuine send/receive pair, [client_ch] and [server_ch]
  (and similarly for sh/ee/cert/cv) generally cannot be the same F* record;
  requiring one shared witness for both sides' model slots asks for something
  a real trace will not produce, not merely a modeling inconvenience.

  Put differently: this predicate is defined directly from
  [WFSM.valid_byte_trace] on both endpoints, the paired transport bytes,
  [paired_no_tail_application_ready_boundary], [CS.paired_wire_logs],
  [Pairing.client_server_driver_first_epoch_no_key_update_state_inputs], and
  the trace-shape boundary
  [PTS.paired_successful_handshake_complete_event_log_shape] -- so it has no
  [PairingNormalizedBoundary.paired_supported_normalized_replay_boundary] and
  no [TLS13.Impl.Driver.PairingNormalizedShape] protected-projection witness in
  its statement, but the [PTS.paired_successful_handshake_complete_event_log_shape]
  conjunct is doing exactly the same kind of illegitimate work those witnesses
  were doing: it is a strong, not-yet-derived hypothesis about the shape of
  the final state, not something proved from
  [WFSM.valid_byte_trace]/[paired_no_tail_application_ready_boundary]/
  [Pairing.client_server_driver_first_epoch_no_key_update_state_inputs] alone,
  and (per the body-field mismatch above) it is not even satisfiable by real
  parser-produced traces in the form written here.

  This legacy predicate also uses [paired_no_tail_application_ready_boundary],
  whose server side is the stale length-15 milestone.  The corrected satisfiable
  server no-tail boundary is [paired_no_tail_application_ready_boundary16]; the
  length-15 exact shape omits the server handshake-read install that is required
  before receiving the protected ClientFinished.

  The genuinely desired role-local no-tail inversion theorem -- deriving
  [CS.supported_profile_client_server_key_material_agrees] and the paired
  [CS.peer_record_material_agrees] facts from nothing more than
  [WFSM.valid_byte_trace] on each endpoint, the paired transport bytes,
  [paired_no_tail_application_ready_boundary], and
  [Pairing.client_server_driver_first_epoch_no_key_update_state_inputs] (with
  [CS.paired_wire_logs] derived rather than assumed) -- is NOT implemented by
  this module.  Reaching it would require, at minimum: (1) a role-local
  inversion lemma per endpoint showing that an application-ready state with an
  event log of the fixed no-tail length (16 for the client, and now also 16 for
  the corrected server target once the handshake read install is included) must
  have the specific canonical message-sequence shape.  The current
  normalized no-tail stack has verified this only through the client
  post-shared-secret handshake install and the server sent ServerHello prefix;
  and (2) deriving the staged protected replay/install facts needed by the
  corrected v2 protected bridge.  That bridge can produce
  [PWL.paired_protected_handshake_event_projection_pairs] without the stale
  pre-install alignment assumption, but the no-tail inversion proof still has to
  extract its staged replay premises from the endpoint logs.  See
  PAIRING_THEOREM.md for the up-to-date account of what remains open.
**)
noextract
let paired_supported_no_tail_valid_byte_traces
  (client_initial:CS.connection_state)
  (server_initial:CS.connection_state)
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  WFSM.valid_byte_trace
    (ClientCP.client_system client_initial)
    client_received
    client
    client_sent
    Seq.empty /\
  WFSM.valid_byte_trace
    (ServerCP.server_system server_initial)
    server_received
    server
    server_sent
    Seq.empty /\
  Seq.equal client_sent server_received /\
  Seq.equal server_sent client_received /\
  paired_no_tail_application_ready_boundary client server /\
  CS.paired_wire_logs client server /\
  Pairing.client_server_driver_first_epoch_no_key_update_state_inputs
    client
    server /\
  PTS.paired_successful_handshake_complete_event_log_shape client server

(**
  NOT the final no-tail inversion theorem: see the status note on
  [paired_supported_no_tail_valid_byte_traces] above.  Its precondition still
  contains [PTS.paired_successful_handshake_complete_event_log_shape], an
  exact cross-endpoint record-equality hypothesis that real parser-produced
  traces are not expected to satisfy.  Read this as a type-checked but
  non-final milestone, not as "key material agreement from valid byte traces
  alone."
**)
val lemma_client_server_application_record_material_agrees_from_no_tail_valid_byte_traces
  (client_initial server_initial: CS.connection_state)
  (client server: CS.connection_state)
  (client_received client_sent server_received server_sent: B.bytes)
  : Lemma
      (requires
        paired_supported_no_tail_valid_byte_traces
          client_initial
          server_initial
          client
          server
          client_received
          client_sent
          server_received
          server_sent)
      (ensures CS.supported_profile_client_server_key_material_agrees client server /\
               CS.peer_record_material_agrees (CS.traffic_id CS.TrafficApplication CS.ClientTraffic) client server /\
               CS.peer_record_material_agrees (CS.traffic_id CS.TrafficApplication CS.ServerTraffic) client server)
