module TLS13.Spec.InternalEvent.Baseline

module CS = TLS13.Spec.StateMachine
module CL = TLS13.ConnectionLog
module M = TLS13.Messages
module T = TLS13.Types
module B = TLS13.Bytes
module W = TLS13.Wire.Spec
module R = TLS13.Record.Spec
module X = TLS13.X509.Spec
module Seq = FStar.Seq

(* B1 *)

let lemma_head_charges_exactly_one_record model step raw_sent raw_received = ()

let lemma_tail_charges_nothing model step raw_sent raw_received = ()

(* B2 *)

let lemma_pending_retained_iff_residual model fragment parsed = ()

let lemma_head_requires_empty_pending model step = ()

let lemma_tail_is_determined_by_state model step = ()

(* B3 *)

let lemma_cursor_strictly_advances model step = ()

let lemma_residual_decreases model step stepped =
  lemma_cursor_strictly_advances model step;
  lemma_pending_retained_iff_residual
    model
    step.CS.protected_handshake_fragment
    (step.CS.protected_handshake_offset + step.CS.protected_handshake_consumed)

(* B4 *)

let lemma_tail_preserves_record_read model step stepped = ()

let lemma_tail_finished_keeps_stepped_record_state model step stepped = ()

(* B5 *)

let lemma_single_message_record_is_a_head_step model step stepped = ()

let lemma_single_message_routes_agree model step =
  TLS13.Spec.StateMachine.Replay.lemma_single_message_head_step_legal model step;
  TLS13.Spec.StateMachine.Replay.lemma_single_message_head_step_model model step

(* B7 *)

let lemma_certificate_blocks_the_pipeline model step = ()

let lemma_no_protected_step_at_certificate_received model step = ()

let lemma_validate_certificate_unblocks_and_preserves_pending model peer = ()

let lemma_local_event_charges_nothing model local raw_sent raw_received = ()

(* B8 *)

let lemma_legal_step_is_a_stream_parse model step =
  W.lemma_parse_handshake_stream_def
    (Seq.slice step.CS.protected_handshake_fragment
               step.CS.protected_handshake_offset
               (B.length step.CS.protected_handshake_fragment))

let lemma_network_receive_is_a_saturated_stream_parse fragment msg =
  W.lemma_parse_handshake_stream_whole fragment;
  W.lemma_parse_handshake_stream_def fragment
