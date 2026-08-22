module TLS13.ConnectionState.ProtectedWireClientFinishedInversion

(**
  The counting-free CLIENT-FINISHED bridge: produces the FIFTH (client Finished)
  protected-handshake projection pair of the flagship
  [ProtectedWireBase.paired_protected_handshake_event_projection_pairs]
  (ProtectedWireBase.fsti:449-452) from the flagship JOINT byte facts.

  Re-based (Option C) off plain [CS.connection_state] endpoints instead of a
  [TLS13.System.tls_system_state] wrapper, so the module no longer imports
  [TLS13.System] (breaking the module dependency cycle that would otherwise
  arise when [TLS13.System.lemma_pw_establish] calls this bridge).  The
  hypotheses are the System-free restatements of the corresponding
  [TLS13.System] predicates, a SUBSET of the facts [lemma_pw_establish]
  provides.

  DIRECTION.  Unlike the four server-flight pairs (server sends, client
  receives), the client Finished is SENT by the CLIENT and RECEIVED by the
  SERVER, so the pair projects
      sent     = [M.Finished client_cf]   (the CLIENT's own [hs_client_finished])
      received = [M.Finished server_cf]    (the SERVER's [hs_client_finished])
  exactly mirroring the fifth conjunct of the flagship predicate.

  MODEL-FIX-1.  The client's SEND of its Finished (StateMachine.fst:809) is
  ATOMIC (installs client-application WRITE keys and lands at
  [ControlApplicationData]); symmetrically the server's RECEIPT
  (StateMachine.fst:774) atomically installs client-application READ keys.  The
  pair is built at the PRE-CF models (handshake-epoch records still aligned)
  with the atomic application-key install folded into the ABSTRACT tail.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module SMReplay = TLS13.Spec.StateMachine.Replay
module CCShape = TLS13.ConnectionState.ClientCanonicalShape
module SCShape = TLS13.ConnectionState.ServerCanonicalShape
module CD = TLS13.Impl.Client.Driver
module SD = TLS13.Impl.Server.Driver
module WStep = TLS13.System.WireStep
module WFL = TLS13.Spec.WireFormatLemmas

open TLS13.ConnectionState.ProtectedWireBase

(* ------------------------------------------------------------------ *)
(* The allowed flagship facts (System-free restatements; identical to *)
(* the server-flight bridge's input bundle).                          *)
(* ------------------------------------------------------------------ *)

(** The four cleartext hellos are recorded on both endpoints. **)
let four_hellos_present (client server : CS.connection_state) : prop =
  Some? client.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
  Some? server.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
  Some? client.CS.cs_model.CS.model_handshake.CS.hs_server_hello /\
  Some? server.CS.cs_model.CS.model_handshake.CS.hs_server_hello

(** The endpoint roles. **)
let roles_ok (client server : CS.connection_state) : prop =
  client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
  server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint

(** System-free restatement of [TLS13.System.hello_key_shares_ok]. **)
let hks_ok (client server : CS.connection_state) : prop =
  (Some? client.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
   Some? server.CS.cs_model.CS.model_handshake.CS.hs_client_hello /\
   Some? client.CS.cs_model.CS.model_handshake.CS.hs_server_hello /\
   Some? server.CS.cs_model.CS.model_handshake.CS.hs_server_hello) ==>
    WFL.paired_cleartext_hello_key_shares client server

(** The complete allowed-hypothesis bundle — identical to the server-flight
    bridge's [server_flight_bridge_inputs], a SUBSET of [lemma_pw_establish]. **)
let client_finished_bridge_inputs (client server : CS.connection_state) : prop =
  WStep.client_reachable (CS.initial client.CS.cs_model.CS.model_config) client /\
  WStep.server_reachable (CS.initial server.CS.cs_model.CS.model_config) server /\
  Seq.equal client.CS.cs_wire_log.CL.raw_sent server.CS.cs_wire_log.CL.raw_received /\
  Seq.equal server.CS.cs_wire_log.CL.raw_sent client.CS.cs_wire_log.CL.raw_received /\
  CD.client_driver_application_ready client /\
  SD.server_driver_application_ready server /\
  hks_ok client server /\
  four_hellos_present client server /\
  roles_ok client server /\
  (* CROSS-RECORD REASSEMBLY.  This bridge routes through
     [ProtectedWireServerFlightInversion.lemma_client_normalized_appdata_exact_spine_from_replays_and_pairing],
     whose input bundle carries the same conjunct: the client's exact spine has
     no slot for a BUFFERING protected-handshake step.  In the paired system the
     client never buffers -- the ATLAS server emits exactly one record per
     handshake message, so the STEP-1 guard of
     [CS.legal_protected_handshake_step] makes a buffering step ILLEGAL --
     buffering is exercised only against a FOREIGN server, which this bridge
     does not describe.  Proving that here would need the cross-endpoint
     record-material agreement, which lives ABOVE [TLS13.System]; so it is taken
     as an input and discharged by the caller. *)
  CCShape.no_buffering_steps client.CS.cs_event_log /\
  (* The SERVER-side sibling, for the SAME reason and with the same discharge.
     A cleartext-handshake BUFFERING step takes delivery of a record without
     delivering any message, so it has no slot in the exact server spine that
     [SCShape.lemma_server_canonical_appdata_exact_spine] reconstructs, and that
     lemma now requires its absence.  In the PAIRED system the peer is the
     verified ATLAS client, which emits its ClientHello as exactly ONE record,
     so the server never has cause to buffer; cross-record ClientHellos arise
     only against a FOREIGN client, which this bridge does not describe. *)
  SCShape.no_cleartext_buffering_steps server.CS.cs_event_log /\
  (* And the CLIENT-side cleartext sibling, for the same reason: the client can
     now buffer too ([EC.client_wire_received_event] admits a
     [ConnCleartextHandshake] step so a ServerHello split across records can be
     reassembled), and such a step has no slot in the exact client spine that
     [CCShape.lemma_client_canonical_appdata_exact_spine] reconstructs.  In the
     PAIRED system the peer is the verified server, which emits its ServerHello
     as exactly ONE record. *)
  CCShape.no_cleartext_buffering_steps client.CS.cs_event_log

(* ------------------------------------------------------------------ *)
(* The CLIENT-FINISHED projection pair, PINNED to the ACTUAL model     *)
(* handshake fields on both endpoints (mirroring ProtectedWireBase.    *)
(* fsti:449-452): the SENT side projects the CLIENT's real             *)
(* [hs_client_finished], the RECEIVED side projects the SERVER's.      *)
(* ------------------------------------------------------------------ *)
let client_finished_pair_conclusion (client server : CS.connection_state) : prop =
  let client_hs = client.CS.cs_model.CS.model_handshake in
  let server_hs = server.CS.cs_model.CS.model_handshake in
  match client_hs.CS.hs_client_finished, server_hs.CS.hs_client_finished with
  | Some client_cf, Some server_cf ->
    (exists (client_finished:protected_message_replay).
      protected_handshake_event_projection_pair
        client_finished
        (M.Finished client_cf)
        (M.Finished server_cf))
  | _, _ ->
    False

val lemma_client_finished_pair_from_replays_and_pairing
  (client server : CS.connection_state)
  : Lemma
      (requires client_finished_bridge_inputs client server)
      (ensures client_finished_pair_conclusion client server)
