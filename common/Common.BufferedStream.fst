module Common.BufferedStream

#lang-pulse

(**

  Protocol-independent scheduling / read-authorisation layer for a buffered
  stream, built on top of [Common.BufferedTCP].  It has two layers.

  ---------------------------------------------------------------------------
  Layer 1 — the PURE classifier model (for protocols that *have* a pure
  classifier, e.g. a length-prefixed framer).
  ---------------------------------------------------------------------------

  A *stream processor* is a pure classifier

        sp_classify : state -> pending -> classification output error

  returning one of [NeedMore] / [Progress consumed] / [Yield consumed out] /
  [Reject err].  On top of it this module proves, as pure facts:

    * [needs_more] — the classifier says [NeedMore] for the *exact* current
      [state] and [pending].  IMPORTANT: [needs_more] is a duplicable *pure
      fact*, NOT a linear capability and NOT something that is "consumed".  It is
      the process-before-read *gate*: it records that a read is warranted.  The
      non-duplicable *right* to perform a read is the caller's stream ownership,
      modelled linearly in Layer 2 below.

    * [NeedMore] is an exact stutter (no consumption, progress or output), and
      committing it is a buffer no-op ([lemma_needmore_stutter],
      [lemma_needmore_apply_noop]).

    * positive consumption is bounded by the pending length
      ([lemma_progress_positive], [lemma_consumption_bounded]).

    * conclusive decisions are prefix-stable under appended read-ahead
      ([lemma_conclusive_prefix_stable], [lemma_conclusive_prefix_stable2]) — the
      justification for processing the current pending before reading.

  The commit effects are threaded back to the [Common.BufferedTCP] buffer so the
  whole [received = committed ++ pending] transport invariant is preserved by
  every pure scheduler step ([lemma_step_commit_preserves]).

  ---------------------------------------------------------------------------
  Layer 2 — the RELATIONAL adapter (for effectful endpoints, e.g. TLS 1.3).
  ---------------------------------------------------------------------------

  TLS has NO pure pre-classifier: its receive step is an effectful, relational
  process that mutates connection/crypto state and returns a status
  ([StepOk]/[NeedMoreInput]/errors) plus a consumed length.  To model this
  honestly, [buffered_stream_endpoint] is a Pulse class in which:

    * [bse_owns e st received committed b] is the endpoint's *linear* stream
      ownership (an [slprop]); linearity is genuine — it is the caller's
      non-duplicable resources.  It fixes the exact current state [st], the exact
      full received transport history [received], the committed prefix and the
      physical buffer [b], with [received == committed ++ pending b] as the real
      invariant ([bse_owns_wf]).

    * [bse_terminal e st received] is terminal ownership after a fatal (Reject)
      decision — the endpoint is done (matches TLS [ConnectionFailed]).

    * [bse_read_auth e st received b] is an abstract *linear read-authorisation
      resource* indexed by the exact live configuration ([received], [st], [b]),
      so it goes stale the instant a read changes the history/buffer.  It is
      *produced* only by the NeedMore case of [bse_process] and *consumed* by
      [bse_read]; being abstract, a client cannot fabricate it, so
      process-before-read is enforced at the type level.

    * [bse_process] classifies the current pending RELATIONALLY, threading the
      received history UNCHANGED through the live cases (processing does not read
      the network): NeedMore is an *exact stutter* — it yields [bse_read_auth]
      only when the buffer still has free space ([BT.free_space b' > 0]); if the
      buffer is FULL it instead goes to [bse_buffer_full] (a scheduler failure)
      and NEVER yields read authorisation (no zero-length reads).  Progress/Yield
      stay live and advance committed/buffer (must process again); Reject goes
      terminal.

    * [bse_read] consumes the authorisation and the live ownership, reads a chunk,
      and re-establishes live ownership at the advanced history
      [received' = received ++ chunk] and the append-read buffer.

  The module depends on [Common.BufferedTCP] and never the reverse.

**)

open Pulse.Lib.Pervasives

module Seq = FStar.Seq
module TCP = Common.TCP
module BT  = Common.BufferedTCP

(* ================================================================== *)
(*  Layer 1: pure classifier model                                    *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(*  Item (5): generic stream-processor classification                 *)
(* ------------------------------------------------------------------ *)

type classification (output:Type0) (error:Type0) =
  | NeedMore : classification output error
  | Progress : consumed:nat -> classification output error
  | Yield    : consumed:nat -> out:output -> classification output error
  | Reject   : err:error -> classification output error

(** A decision is conclusive when it is not [NeedMore]. *)
let is_conclusive (#output #error:Type0) (d:classification output error) : bool =
  match d with
  | NeedMore -> false
  | _ -> true

(** How many pending bytes a decision consumes. *)
let consumed_of (#output #error:Type0) (d:classification output error) : nat =
  match d with
  | NeedMore -> 0
  | Progress k -> k
  | Yield k _ -> k
  | Reject _ -> 0

(** A decision makes forward progress (consumes and advances). *)
let makes_progress (#output #error:Type0) (d:classification output error) : bool =
  match d with
  | Progress _ -> true
  | Yield _ _ -> true
  | _ -> false

(** A decision emits an application output. *)
let produces_output (#output #error:Type0) (d:classification output error) : bool =
  match d with
  | Yield _ _ -> true
  | _ -> false

(* ------------------------------------------------------------------ *)
(*  The stream-processor classifier laws                              *)
(* ------------------------------------------------------------------ *)

(**
  Positive consumption is bounded: a decision never consumes more than the
  pending bytes, and a progress-making decision consumes at least one byte
  (so it cannot masquerade as a stutter).
**)
let consumption_law
  (#state #output #error:Type0)
  (classify:state -> TCP.bytes -> classification output error)
  (st:state)
  (pending:TCP.bytes)
  : prop =
  consumed_of (classify st pending) <= Seq.length pending /\
  (makes_progress (classify st pending) ==> consumed_of (classify st pending) > 0)

(**
  Conclusive decisions are prefix-stable: reading ahead (appending [extra]
  bytes) does not change a conclusive decision.
**)
let prefix_stable_law
  (#state #output #error:Type0)
  (classify:state -> TCP.bytes -> classification output error)
  (st:state)
  (pending:TCP.bytes)
  (extra:TCP.bytes)
  : prop =
  is_conclusive (classify st pending) ==>
    classify st (Seq.append pending extra) == classify st pending

noextract
class stream_processor (state:Type0) (output:Type0) (error:Type0) =
{
  sp_classify:
    state -> TCP.bytes -> classification output error;

  sp_consumption:
    st:state ->
    pending:TCP.bytes ->
      Lemma (consumption_law sp_classify st pending);

  sp_prefix_stable:
    st:state ->
    pending:TCP.bytes ->
    extra:TCP.bytes ->
      Lemma
        (requires is_conclusive (sp_classify st pending))
        (ensures
          sp_classify st (Seq.append pending extra) == sp_classify st pending);
}

(* ------------------------------------------------------------------ *)
(*  Both classifier laws hold, at the predicate level, for any instance *)
(* ------------------------------------------------------------------ *)

(** Every instance satisfies the reusable [consumption_law] predicate. *)
let lemma_instance_consumption_law
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma (ensures consumption_law sp.sp_classify st pending)
= sp.sp_consumption st pending

(** Every instance satisfies the reusable [prefix_stable_law] predicate. *)
let lemma_instance_prefix_stable_law
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending extra:TCP.bytes)
  : Lemma (ensures prefix_stable_law sp.sp_classify st pending extra)
= if is_conclusive (sp.sp_classify st pending)
  then sp.sp_prefix_stable st pending extra
  else ()

(* ------------------------------------------------------------------ *)
(*  Bounded consumption                                               *)
(* ------------------------------------------------------------------ *)

let lemma_consumption_bounded
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures consumed_of (sp.sp_classify st pending) <= Seq.length pending)
= sp.sp_consumption st pending

let lemma_progress_positive
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (requires makes_progress (sp.sp_classify st pending))
      (ensures
        0 < consumed_of (sp.sp_classify st pending) /\
        consumed_of (sp.sp_classify st pending) <= Seq.length pending)
= sp.sp_consumption st pending

(* ------------------------------------------------------------------ *)
(*  Item (6a): the process-before-read gate  [needs_more]             *)
(* ------------------------------------------------------------------ *)

(**
  [needs_more sp st pending] holds precisely when the classifier says [NeedMore]
  for the *exact* [st] and [pending].  It is a duplicable PURE fact — the
  process-before-read gate — NOT a linear capability and NOT "consumed" by
  reading.  The non-duplicable right to read is the caller's stream ownership
  (Layer 2, [bse_owns] / [bse_read_auth]).
**)
let needs_more
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : prop =
  sp.sp_classify st pending == NeedMore

let lemma_needs_more_iff
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures (needs_more sp st pending <==> sp.sp_classify st pending == NeedMore))
= ()

(** [needs_more] and a conclusive decision are mutually exclusive. *)
let lemma_needmore_not_conclusive
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (requires needs_more sp st pending)
      (ensures ~(is_conclusive (sp.sp_classify st pending)))
= ()

let lemma_conclusive_not_needs_more
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (requires is_conclusive (sp.sp_classify st pending))
      (ensures ~(needs_more sp st pending))
= ()

(**
  The gate is *state specific*: [needs_more] at [st] cannot coexist with a
  conclusive decision at a state [st'] on the same pending — so [st =!= st'].
**)
let lemma_needs_more_state_specific
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st st':state)
  (pending:TCP.bytes)
  : Lemma
      (requires needs_more sp st pending /\ is_conclusive (sp.sp_classify st' pending))
      (ensures ~(st == st'))
= ()

(**
  The gate is *pending specific*: [needs_more] at [pending] cannot coexist with a
  conclusive decision at a different [pending'] in the same state — so
  [pending =!= pending'].  After the pending bytes change (e.g. by a read), the
  gate must be re-derived.
**)
let lemma_needs_more_pending_specific
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending pending':TCP.bytes)
  : Lemma
      (requires needs_more sp st pending /\ is_conclusive (sp.sp_classify st pending'))
      (ensures ~(pending == pending'))
= ()

(* ------------------------------------------------------------------ *)
(*  Item (6b): NeedMore is a stutter / no output                      *)
(* ------------------------------------------------------------------ *)

let lemma_needmore_stutter
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (requires needs_more sp st pending)
      (ensures
        consumed_of (sp.sp_classify st pending) == 0 /\
        ~(makes_progress (sp.sp_classify st pending)) /\
        ~(produces_output (sp.sp_classify st pending)))
= ()

(* ------------------------------------------------------------------ *)
(*  Item (6c): conclusive decisions are prefix-stable                 *)
(* ------------------------------------------------------------------ *)

(** One read-ahead: a conclusive decision is unchanged by appended bytes. *)
let lemma_conclusive_prefix_stable
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending extra:TCP.bytes)
  : Lemma
      (requires is_conclusive (sp.sp_classify st pending))
      (ensures sp.sp_classify st (Seq.append pending extra) == sp.sp_classify st pending)
= sp.sp_prefix_stable st pending extra

(** Two successive read-aheads: still the same conclusive decision. *)
let lemma_conclusive_prefix_stable2
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending extra1 extra2:TCP.bytes)
  : Lemma
      (requires is_conclusive (sp.sp_classify st pending))
      (ensures
        sp.sp_classify st (Seq.append (Seq.append pending extra1) extra2)
        == sp.sp_classify st pending)
= sp.sp_prefix_stable st pending extra1;
  sp.sp_prefix_stable st (Seq.append pending extra1) extra2

(* ------------------------------------------------------------------ *)
(*  Item (6): explicit process-before-read phases                     *)
(* ------------------------------------------------------------------ *)

(**
  The two scheduling phases of the process-before-read discipline.  In the
  [Reading] phase the scheduler must read more bytes; in the [Processing] phase
  it must act on a conclusive decision.  The phase is *computed from* the current
  state and pending bytes, so "which phase" is dictated by the classifier.
**)
type phase =
  | Reading
  | Processing

let current_phase
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : phase =
  if is_conclusive (sp.sp_classify st pending) then Processing else Reading

(** The [Reading] phase is *exactly* where the gate [needs_more] holds. *)
let lemma_phase_reading_iff_needs_more
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures (current_phase sp st pending == Reading <==> needs_more sp st pending))
= ()

(** The [Processing] phase is *exactly* where the decision is conclusive. *)
let lemma_phase_processing_iff_conclusive
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures
        (current_phase sp st pending == Processing <==>
         is_conclusive (sp.sp_classify st pending)))
= ()

(**
  The process-before-read *dichotomy*: in any configuration the scheduler is in
  exactly one of two phases — a read phase (the gate holds and the decision is
  not yet conclusive) or a process phase (the decision is conclusive and the gate
  does not hold).  This licenses "process first, read only on [NeedMore]".
**)
let lemma_process_read_dichotomy
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures
        (needs_more sp st pending /\ ~(is_conclusive (sp.sp_classify st pending))) \/
        (is_conclusive (sp.sp_classify st pending) /\ ~(needs_more sp st pending)))
= ()

(* ------------------------------------------------------------------ *)
(*  Pure scheduler step effects on the buffered-TCP state             *)
(* ------------------------------------------------------------------ *)

(**
  The transport-and-buffer invariant a concrete wrapper maintains: the buffer is
  well-formed (fixed capacity, dense pending prefix) and the received stream is
  the committed prefix followed by the buffer's pending region.
**)
let stream_invariant
  (received committed:TCP.bytes)
  (b:BT.phys_buffer)
  : prop =
  BT.buffer_wf b /\ BT.received_split received committed b

(** The classifier's consumption is always a valid commit count for the buffer. *)
let lemma_commit_count_ok
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b:BT.phys_buffer)
  : Lemma
      (requires BT.buffer_wf b)
      (ensures consumed_of (sp.sp_classify st (BT.pending b)) <= b.BT.pb_filled)
= sp.sp_consumption st (BT.pending b);
  BT.lemma_pending_length b

(**
  Commit a scheduler decision to the buffer: the committed prefix grows by the
  consumed bytes and the buffer is compacted.
**)
let step_commit
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (committed:TCP.bytes)
  (b:BT.phys_buffer)
  : (TCP.bytes & BT.phys_buffer) =
  let k = consumed_of (sp.sp_classify st (BT.pending b)) in
  (BT.committed_after committed b k, BT.compact b k)

(**
  Core scheduler theorem: committing *any* classifier decision preserves the
  whole [received = committed ++ pending] invariant and the fixed-capacity
  buffer well-formedness.
**)
let lemma_step_commit_preserves
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (received committed:TCP.bytes)
  (b:BT.phys_buffer)
  : Lemma
      (requires stream_invariant received committed b)
      (ensures
        (let (committed', b') = step_commit sp st committed b in
         stream_invariant received committed' b'))
= lemma_commit_count_ok sp st b;
  let k = consumed_of (sp.sp_classify st (BT.pending b)) in
  BT.lemma_commit_preserves_full received committed b k;
  BT.lemma_compact_wf b k

(** The committed stream only ever grows when a decision is committed. *)
let lemma_step_commit_extends
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (committed:TCP.bytes)
  (b:BT.phys_buffer)
  : Lemma
      (ensures
        (let (committed', _) = step_commit sp st committed b in
         TCP.bytes_extends committed committed'))
= let k = consumed_of (sp.sp_classify st (BT.pending b)) in
  BT.lemma_committed_after_extends committed b k

(**
  Committing a [NeedMore] decision is a buffer no-op: the committed prefix and
  the pending region are unchanged — a genuine stutter that only a read can
  break.
**)
let lemma_needmore_apply_noop
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (committed:TCP.bytes)
  (b:BT.phys_buffer)
  : Lemma
      (requires needs_more sp st (BT.pending b) /\ BT.buffer_wf b)
      (ensures
        (let (committed', b') = step_commit sp st committed b in
         Seq.equal committed' committed /\
         Seq.equal (BT.pending b') (BT.pending b)))
= BT.lemma_compact_pending b 0;
  Seq.append_empty_r committed;
  Seq.lemma_eq_intro (BT.committed_after committed b 0) committed

(* ------------------------------------------------------------------ *)
(*  Item (6d): a warranted read (a PURE fact, not a capability)       *)
(* ------------------------------------------------------------------ *)

(**
  A PURE specification of a warranted read: the classifier needs more input at
  the exact current [st] and pending [BT.pending b], the delivered [chunk] fits
  the free capacity, and [b'] is the append-read of [chunk] into [b].

  This is a *pure fact*, NOT a linear capability and NOT "consumed" by reading.
  It records that a read is warranted; the non-duplicable *right* to perform it
  is the caller's stream ownership — the [bse_read_auth] token of the Layer-2
  relational adapter [buffered_stream_endpoint].
**)
let read_warranted
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : prop =
  needs_more sp st (BT.pending b) /\
  BT.chunk_fits b chunk /\
  b' == BT.append_read b chunk

(** The buffer effect of a warranted read: pending grows by [chunk]. *)
let lemma_read_warranted_effect
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires read_warranted sp st b b' chunk /\ BT.buffer_wf b)
      (ensures
        BT.buffer_wf b' /\
        BT.capacity b' == BT.capacity b /\
        Seq.equal (BT.pending b') (Seq.append (BT.pending b) chunk))
= BT.lemma_append_read_wf b chunk;
  BT.lemma_append_read_capacity b chunk;
  BT.lemma_append_read_pending b chunk

(**
  Process-before-read: a read is warranted only in the [Reading] phase, never in
  the [Processing] phase.  So the scheduler always processes a conclusive
  decision before it is allowed to read again.
**)
let lemma_read_only_in_reading_phase
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires read_warranted sp st b b' chunk)
      (ensures current_phase sp st (BT.pending b) == Reading)
= ()

(**
  Core scheduler theorem for reads: a warranted read preserves the invariant,
  extending the received stream by exactly the delivered chunk.
**)
let lemma_step_read_preserves
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (received committed:TCP.bytes)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires read_warranted sp st b b' chunk /\ stream_invariant received committed b)
      (ensures stream_invariant (Seq.append received chunk) committed b')
= BT.lemma_append_read_extends_received received committed b chunk;
  BT.lemma_append_read_wf b chunk

(**
  After a read the pending region is [BT.pending b ++ chunk]; whether a further
  read is warranted depends on a *fresh* classification of that new pending.  The
  scheduler therefore re-enters the process-before-read dichotomy at [b'].
**)
let lemma_after_read_dichotomy
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b':BT.phys_buffer)
  : Lemma
      (ensures
        (needs_more sp st (BT.pending b') /\ ~(is_conclusive (sp.sp_classify st (BT.pending b')))) \/
        (is_conclusive (sp.sp_classify st (BT.pending b')) /\ ~(needs_more sp st (BT.pending b'))))
= ()

(**
  If the classifier concludes on the current pending, then it would have reached
  the *same* decision after any read-ahead.  Hence it is always sound to process
  the current pending *before* reading: reading first can never turn a conclusive
  decision into a different one.
**)
let lemma_process_before_read_sound
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires
        is_conclusive (sp.sp_classify st (BT.pending b)) /\
        BT.buffer_wf b /\
        BT.chunk_fits b chunk /\
        b' == BT.append_read b chunk)
      (ensures sp.sp_classify st (BT.pending b') == sp.sp_classify st (BT.pending b))
= BT.lemma_append_read_pending b chunk;
  sp.sp_prefix_stable st (BT.pending b) chunk;
  Seq.lemma_eq_elim (BT.pending b') (Seq.append (BT.pending b) chunk)

(* ================================================================== *)
(*  Layer 2: relational post-processing adapter (effectful endpoints) *)
(* ================================================================== *)

(**
  The buffer transition induced by a relational decision.  This does NOT assume a
  pure classifier: it relates a *decision value* [d] (obtained by actually
  running an effectful process step) to the committed/buffer transition.

    - [NeedMore] and [Reject] are exact stutters (no consumption);
    - [Progress]/[Yield] commit [consumed] pending bytes via the
      [Common.BufferedTCP] [committed_after]/[compact] model, with the
      consumption positive and bounded by the live count.
**)
let process_transition
  (#output #error:Type0)
  (d:classification output error)
  (committed committed':TCP.bytes)
  (b b':BT.phys_buffer)
  : prop =
  match d with
  | NeedMore ->
    Seq.equal committed' committed /\ b' == b
  | Reject _ ->
    // Reject is a TERMINAL decision handled by the [bse_terminal] branch of the
    // class, NOT by this live transition — so its case here is irrelevant.
    True
  | Progress k ->
    0 < k /\ k <= b.BT.pb_filled /\
    Seq.equal committed' (BT.committed_after committed b k) /\
    b' == BT.compact b k
  | Yield k _ ->
    0 < k /\ k <= b.BT.pb_filled /\
    Seq.equal committed' (BT.committed_after committed b k) /\
    b' == BT.compact b k

(** The NeedMore case of a relational process is an exact stutter, consuming 0. *)
let lemma_process_transition_needmore_stutter
  (#output #error:Type0)
  (d:classification output error)
  (committed committed':TCP.bytes)
  (b b':BT.phys_buffer)
  : Lemma
      (requires process_transition d committed committed' b b' /\ d == NeedMore)
      (ensures Seq.equal committed' committed /\ b' == b /\ consumed_of d == 0)
= ()

(**
  A *live* relational process step (NeedMore / Progress / Yield) preserves the
  transport invariant.  The received stream is unchanged — processing consumes
  from the pending region, it does not read the network — while the
  committed/pending boundary moves for the progress cases.  (Reject is terminal
  and handled separately; it is excluded here.)
**)
let lemma_process_transition_preserves
  (#output #error:Type0)
  (d:classification output error)
  (received committed committed':TCP.bytes)
  (b b':BT.phys_buffer)
  : Lemma
      (requires
        process_transition d committed committed' b b' /\
        ~(Reject? d) /\
        BT.received_split received committed b /\
        BT.buffer_wf b)
      (ensures
        BT.received_split received committed' b' /\ BT.buffer_wf b')
= match d with
  | NeedMore -> ()
  | Reject _ -> ()
  | Progress k ->
    BT.lemma_commit_preserves_full received committed b k;
    BT.lemma_compact_wf b k
  | Yield k _ ->
    BT.lemma_commit_preserves_full received committed b k;
    BT.lemma_compact_wf b k

(**
  A read step extends the received stream by exactly the delivered chunk, keeping
  the [received = committed ++ pending] invariant (committed is unchanged).
**)
let lemma_read_extends_received
  (received committed:TCP.bytes)
  (b:BT.phys_buffer)
  (chunk:TCP.bytes)
  (b':BT.phys_buffer)
  : Lemma
      (requires
        BT.received_split received committed b /\
        BT.buffer_wf b /\
        BT.chunk_fits b chunk /\
        b' == BT.append_read b chunk)
      (ensures
        BT.received_split (Seq.append received chunk) committed b' /\
        BT.buffer_wf b')
= BT.lemma_append_read_extends_received received committed b chunk;
  BT.lemma_append_read_wf b chunk

(**
  The endpoint-level post of a read step: the result buffer [b'] is well-formed,
  of the same fixed capacity, its dense pending region is the old pending
  followed by the delivered chunk, AND the exact received history advances by
  that SAME chunk ([received' = received ++ chunk]).  The chunk is a squashed
  existential, so the Pulse existentials in [bse_read] stay inferable.  It is
  stated on the *pending* (the transport-observable dense prefix), not the full
  physical array, so it is realised by the real [Common.BufferedTCP.read_append]
  primitive, not only the canonical [append_read] model.
**)
let read_delivers
  (received received':TCP.bytes)
  (b b':BT.phys_buffer)
  : prop =
  BT.buffer_wf b' /\
  BT.capacity b' == BT.capacity b /\
  (exists (chunk:TCP.bytes).
     BT.chunk_fits b chunk /\
     Seq.equal (BT.pending b') (Seq.append (BT.pending b) chunk) /\
     Seq.equal received' (Seq.append received chunk))

(** [read_delivers] holds after appending any fitting chunk (canonical model). *)
let lemma_read_delivers_intro
  (received:TCP.bytes)
  (b:BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires BT.buffer_wf b /\ BT.chunk_fits b chunk)
      (ensures read_delivers received (Seq.append received chunk) b (BT.append_read b chunk))
= BT.lemma_append_read_wf b chunk;
  BT.lemma_append_read_capacity b chunk;
  BT.lemma_append_read_pending b chunk;
  introduce exists (c:TCP.bytes).
      BT.chunk_fits b c /\
      Seq.equal (BT.pending (BT.append_read b chunk)) (Seq.append (BT.pending b) c) /\
      Seq.equal (Seq.append received chunk) (Seq.append received c)
  with chunk and ()

(**
  The real [Common.BufferedTCP.read_append] primitive establishes [read_delivers]:
  from its transport postcondition (buffer well-formed, capacity preserved, dense
  prefix == old pending ++ chunk, history advanced by chunk) the process-gated
  [bse_read] caller derives the class contract for the append-read buffer.
**)
let lemma_read_append_read_delivers
  (received raw_before raw_after:TCP.bytes)
  (capacity filled new_filled:nat)
  (chunk:TCP.bytes)
  : Lemma
      (requires
        Seq.length raw_before == capacity /\
        Seq.length raw_after == capacity /\
        filled <= capacity /\
        new_filled <= capacity /\
        BT.buffer_wf (BT.mk_phys_buffer raw_after new_filled) /\
        BT.chunk_fits (BT.mk_phys_buffer raw_before filled) chunk /\
        Seq.equal (BT.pending (BT.mk_phys_buffer raw_after new_filled))
                  (Seq.append (BT.pending (BT.mk_phys_buffer raw_before filled)) chunk))
      (ensures
        read_delivers received (Seq.append received chunk)
          (BT.mk_phys_buffer raw_before filled) (BT.mk_phys_buffer raw_after new_filled))
= introduce exists (c:TCP.bytes).
      BT.chunk_fits (BT.mk_phys_buffer raw_before filled) c /\
      Seq.equal (BT.pending (BT.mk_phys_buffer raw_after new_filled))
                (Seq.append (BT.pending (BT.mk_phys_buffer raw_before filled)) c) /\
      Seq.equal (Seq.append received chunk) (Seq.append received c)
  with chunk and ()

(**
  [read_delivers] re-establishes the [received = committed ++ pending] invariant
  at the advanced history [received'] and the append-read buffer [b'].
**)
let lemma_read_delivers_preserves
  (received received' committed:TCP.bytes)
  (b b':BT.phys_buffer)
  : Lemma
      (requires
        BT.received_split received committed b /\
        BT.buffer_wf b /\
        read_delivers received received' b b')
      (ensures
        BT.buffer_wf b' /\ BT.received_split received' committed b')
= let chunk = FStar.IndefiniteDescription.indefinite_description_ghost
                TCP.bytes
                (fun chunk -> BT.chunk_fits b chunk /\
                              Seq.equal (BT.pending b') (Seq.append (BT.pending b) chunk) /\
                              Seq.equal received' (Seq.append received chunk)) in
  Seq.lemma_eq_elim received (Seq.append committed (BT.pending b));
  Seq.lemma_eq_elim (BT.pending b') (Seq.append (BT.pending b) chunk);
  Seq.lemma_eq_elim received' (Seq.append received chunk);
  Seq.append_assoc committed (BT.pending b) chunk

(**
  The relational buffered-stream endpoint contract that a concrete effectful
  endpoint (e.g. a TLS 1.3 driver) instantiates.  See the module header for the
  semantics; in particular [bse_read_auth] is the linear read-authorisation
  resource that makes process-before-read type-enforced, and there is NO pure
  pre-classifier.

  Ownership is indexed by the EXACT received transport history, so [bse_owns_wf]
  proves the real invariant [received_split received committed b] (not a
  tautology).  The approved scheduling semantics are:

    * NeedMore        => stay LIVE (exact stutter) and yield read authorisation;
    * Progress/Yield  => stay LIVE, advanced (the scheduler must process again);
    * Reject          => go TERMINAL ([bse_terminal]); TLS fatal processing may
                         have consumed input, so no stutter and no live ownership
                         is required or returned (matches TLS [ConnectionFailed]).
**)
noextract
class buffered_stream_endpoint
  (endpoint:Type0)
  (state:Type0)
  (output:Type0)
  (error:Type0)
  (result:Type0)
  =
{
  (* Pure projection of a concrete result value to its abstract decision. *)
  bse_decide:
    result -> GTot (classification output error);

  (* Live stream ownership indexed by the exact received history, committed
     prefix and buffer.  [received] is the authoritative full transport history;
     [received == committed ++ pending b] is the invariant (see [bse_owns_wf]). *)
  bse_owns:
    endpoint -> state -> TCP.bytes -> TCP.bytes -> BT.phys_buffer -> slprop;

  (* Terminal ownership after a fatal (Reject) decision: no further processing. *)
  bse_terminal:
    endpoint -> state -> TCP.bytes -> slprop;

  (* Terminal SCHEDULER-FAILURE ownership: the classifier said NeedMore but the
     fixed-capacity buffer is FULL, so no (non-zero) read is possible.  This is a
     scheduler failure distinct from a protocol [Reject]; read authorisation is
     REFUSED here (never fabricated at a full buffer). *)
  bse_buffer_full:
    endpoint -> state -> TCP.bytes -> slprop;

  (* Linear read-authorisation resource, indexed by the exact LIVE configuration
     (received history, state, buffer) so it goes stale as soon as a read changes
     the history/buffer. *)
  bse_read_auth:
    endpoint -> state -> TCP.bytes -> BT.phys_buffer -> slprop;

  (* Live ownership entails the real transport invariant. *)
  bse_owns_wf:
    e:endpoint ->
    st:Ghost.erased state ->
    received:Ghost.erased TCP.bytes ->
    committed:Ghost.erased TCP.bytes ->
    b:Ghost.erased BT.phys_buffer ->
      stt_ghost unit emp_inames
        (bse_owns e (Ghost.reveal st) (Ghost.reveal received) (Ghost.reveal committed) (Ghost.reveal b))
        (fun _ ->
          bse_owns e (Ghost.reveal st) (Ghost.reveal received) (Ghost.reveal committed) (Ghost.reveal b) **
          pure (
            BT.buffer_wf (Ghost.reveal b) /\
            BT.received_split (Ghost.reveal received) (Ghost.reveal committed) (Ghost.reveal b)));

  (* The effectful, relational process-before-read step.  The received history is
     threaded UNCHANGED through the live cases (processing does not read the
     network).
       NeedMore  => exact stutter; if the buffer still has free space it stays
                    LIVE and yields read authorisation, but if the buffer is FULL
                    it goes to [bse_buffer_full] (a scheduler failure) and NEVER
                    yields read authorisation — no zero-length reads.
       Progress/Yield => stay LIVE, advance committed/buffer (must process again).
       Reject    => go terminal ([bse_terminal]). *)
  bse_process:
    e:endpoint ->
    st:Ghost.erased state ->
    received:Ghost.erased TCP.bytes ->
    committed:Ghost.erased TCP.bytes ->
    b:Ghost.erased BT.phys_buffer ->
      stt result
        (bse_owns e (Ghost.reveal st) (Ghost.reveal received) (Ghost.reveal committed) (Ghost.reveal b))
        (fun r ->
          match bse_decide r with
          | Reject _ ->
            (exists* st' received'. bse_terminal e st' received')
          | NeedMore ->
            (exists* st' committed' b'.
              pure (
                process_transition (bse_decide r) (Ghost.reveal committed) committed' (Ghost.reveal b) b' /\
                st' == Ghost.reveal st) **
              // NeedMore stutters (b' == b), so this is exactly [BT.can_read b']:
              (if BT.free_space (Ghost.reveal b) > 0
               then
                 bse_owns e st' (Ghost.reveal received) committed' b' **
                 bse_read_auth e st' (Ghost.reveal received) b'
               else
                 bse_buffer_full e st' (Ghost.reveal received)))
          | Progress _ ->
            (exists* st' committed' b'.
              bse_owns e st' (Ghost.reveal received) committed' b' **
              pure (process_transition (bse_decide r) (Ghost.reveal committed) committed' (Ghost.reveal b) b'))
          | Yield _ _ ->
            (exists* st' committed' b'.
              bse_owns e st' (Ghost.reveal received) committed' b' **
              pure (process_transition (bse_decide r) (Ghost.reveal committed) committed' (Ghost.reveal b) b')));

  (* The read step: consume the linear read authorisation (only obtainable from a
     NeedMore process) and the live ownership, read a chunk, and re-establish live
     ownership at the advanced history [received' = received ++ chunk] and the
     append-read buffer.  This is what enforces process-before-read. *)
  bse_read:
    e:endpoint ->
    st:Ghost.erased state ->
    received:Ghost.erased TCP.bytes ->
    committed:Ghost.erased TCP.bytes ->
    b:Ghost.erased BT.phys_buffer ->
      stt unit
        (bse_owns e (Ghost.reveal st) (Ghost.reveal received) (Ghost.reveal committed) (Ghost.reveal b) **
         bse_read_auth e (Ghost.reveal st) (Ghost.reveal received) (Ghost.reveal b) **
         pure (BT.buffer_wf (Ghost.reveal b) /\ BT.can_read (Ghost.reveal b)))
        (fun _ ->
          exists* received' b'.
            bse_owns e (Ghost.reveal st) received' (Ghost.reveal committed) b' **
            pure (read_delivers (Ghost.reveal received) received' (Ghost.reveal b) b'));
}
