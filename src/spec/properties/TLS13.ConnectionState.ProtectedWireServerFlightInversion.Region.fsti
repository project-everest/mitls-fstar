module TLS13.ConnectionState.ProtectedWireServerFlightInversion.Region

(**
  Counting-free byte-neutral region-collapse helpers for Stage 3 of the
  server-flight derivation.

  A run of LOCAL-or-opposite-direction events is byte-neutral on the stream it
  does not touch:

    * a [ConnLocalEvent] contributes an EMPTY delta on BOTH the sent and the
      received raw streams ([event_raw_delta_legal] forces both deltas empty),
    * a [ConnNetworkEvent] with [message_direction = Received] contributes an
      EMPTY delta on the SENT stream,
    * a [ConnNetworkEvent] with [message_direction = Sent] contributes an EMPTY
      delta on the RECEIVED stream.

  Consequently a whole such run collapses to the empty byte string on the
  untouched stream.  This is exactly the Caution-1 fact used to collapse the
  server / client handshake-install [region] (all elements are LOCAL installs)
  when feeding the [ProtectedWireServerFlight.fsti:1090] producer.

  These lemmas are self-contained: they depend only on the survivor
  [ProtectedWireReplay] head-peel lemmas and the core replay / canonical
  definitions.  No counting (no `length == 16 / 14`) is used.
**)

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module SMReplay = TLS13.Spec.StateMachine.Replay
module Seq = FStar.Seq
module L = FStar.List.Tot

(** An event that contributes an EMPTY delta on the SENT stream: any local
    event, or a Received network event. *)
let is_empty_sent_ev (ev:CS.conn_event) : bool =
  CS.ConnLocalEvent? ev ||
  (CS.ConnNetworkEvent? ev &&
   (CS.ConnNetworkEvent?._0 ev).CL.message_direction = CL.Received)

(** An event that contributes an EMPTY delta on the RECEIVED stream: any local
    event, or a Sent network event. *)
let is_empty_recv_ev (ev:CS.conn_event) : bool =
  CS.ConnLocalEvent? ev ||
  (CS.ConnNetworkEvent? ev &&
   (CS.ConnNetworkEvent?._0 ev).CL.message_direction = CL.Sent)

(** A run of [is_empty_sent_ev] events produces no SENT bytes. *)
val lemma_empty_sent_tail_collapses
  (model:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_sent_seal_replay model evs rs rr final /\
        L.for_all is_empty_sent_ev evs)
      (ensures Seq.equal rs B.empty)
      (decreases evs)

(** A run of [is_empty_recv_ev] events produces no RECEIVED bytes. *)
val lemma_empty_recv_tail_collapses
  (model:CS.connection_model) (evs:list CS.conn_event)
  (rs rr:B.bytes) (final:CS.connection_model)
  : Lemma
      (requires
        SMReplay.conn_events_received_decode_replay model evs rs rr final /\
        L.for_all is_empty_recv_ev evs)
      (ensures Seq.equal rr B.empty)
      (decreases evs)
