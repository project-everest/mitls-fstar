# Internal Events: One Canonical Client Receive Semantics

Date: 2026-08-01
Status: Proposed for review
Gate: `make -j128 verify test`

---

## 1. Problem

The client has two receive semantics, and only one of them is packaged as a
`Common.ProtocolImplementation`.

### 1.1 The fork is in the spec, not just the implementation

`TLS13.Spec.StateMachine` gives a protected handshake record two different
representations depending on how many messages it contains.

`legal_protected_handshake_step` (`src/spec/core/TLS13.Spec.StateMachine.fst:1496`)
admits a *head* step only when the record holds strictly more than one message:

```fstar
  (if step.protected_handshake_head
   then
     offset == 0 /\
     consumed < B.length fragment /\      (* strictly less: >1 message *)
     protected_handshake_buffer_empty model
   else
     Seq.equal fragment model...hb_encrypted_server_handshake_bytes /\
     offset == model...hb_encrypted_server_handshake_parsed)
```

So:

| Record contents | Representation |
|---|---|
| exactly one handshake message | `ConnNetworkEvent` (one message, one record) |
| two or more handshake messages | `ConnProtectedHandshake` head, then tails |

The head step is not record-only: it accounts for the raw record *and*
processes the first message atomically.

### 1.2 The fork propagates to the implementation

`TLS13.Impl.Client.fsti` exports three receive primitives:

- `process_network_bytes` (line 376)
- `process_coalesced_network_bytes` (line 433)
- `process_pending_protected_handshake` (line 482)

`TLS13.Impl.Client.CanonicalProtocol` packages only `process_network_bytes`.
`TLS13.Impl.Client.Engine` calls the other two. The Engine path proves
`coalesced_network_bytes_end_to_end_correct` and preserves
`client_end_to_end_invariant`, but establishes none of:

- `client_progress_preorder`
- `WFSM.valid_byte_trace` for `client_protocol_implementation`
- `CI.channel_state_valid`

### 1.3 Root cause

`TLS13.Spec.Endpoint.Client.client_step` binds one wire record to exactly one
semantic message:

```fstar
  | SM.WireEvent wire ->
    exists msg.
      let conn_ev = CS.ConnNetworkEvent { message_direction = Received;
                                          message_value = msg } in
      SMCan.canonical_wire_step st0 st1 conn_ev ... /\
      network_input_message_projection st0 wire msg /\ ...
```

The canonical endpoint machine structurally cannot express a record carrying
several messages. That is why the Chromium path had to fork.

---

## 2. Design

```text
one physical TLS record
  -> one WireEvent transition          (parse, decrypt, account, retain plaintext)
  -> zero or more internal transitions (one semantic message each)
```

### 2.1 An internal event is a distinguished local event

An **internal event** is a `LocalEvent` that is:

1. selected by the implementation from its current state, not supplied by a
   caller; and
2. classified as internal by a protocol-supplied syntactic predicate.

There is **no new constructor in `Common.StateMachine.event`** and **no fifth
type parameter** on the generic classes.

This is not a shortcut. The generic layers already implement internal steps
under exactly this reading:

**`Common.SystemProduct`** already treats "internal" as a first-class move
family with the right channel discipline:

> *an INTERNAL move (a party steps with no channel interaction) is enabled only
> when the channel is QUIET and leaves it QUIET*

with fields `client_local` / `server_local`, gated in `product_step` by
`is_quiet a /\ i.client_local a b`.

**`Common.MachineProduct`** already derives those families from `LocalEvent`
steps, splitting on wire output:

```fstar
(** Client INTERNAL: a local event that emits nothing on the wire. **)
let mp_client_local ... =
  i.moves.uses_client_local /\
  (exists local c' out.
     i.cstep a.client (SM.LocalEvent local) c' out /\
     out.SM.so_wire_outputs == [] /\
     b == { a with client = c' })
```

and `full_duplex_moves` already sets `uses_client_local = uses_server_local =
True`.

**`Common.WireFormatStateMachine.event_input_messages`** already returns `[]`
for `LocalEvent`, so `valid_byte_trace` already charges local steps zero
transport bytes.

**`Common.ProtocolImplementation.local_process_correct`** (line 383) already
proves, for `StepOk`:

```fstar
  sm_step st0 (SM.LocalEvent ev) st1 (step_output wire_outputs local_outputs) /\
  Seq.equal received1 received0 /\
  Seq.equal sent1 (Seq.append sent0 produced)
```

plus `OutputBufferTooSmall` and `local_error_refines_state_machine`.

**`TLS13.Spec.Endpoint.Client.client_step`'s `LocalEvent` case is already
existential over the connection event**:

```fstar
  | SM.LocalEvent local ->
    exists conn_ev raw_sent.
      client_representation_matches st0 local conn_ev /\ ...
```

so a concrete singleton repr can match a `conn_event` whose ghost fields are
pinned by state — which is precisely "implementation-selected". Note that
`legal_protected_handshake_step` already pins `offset` to
`hb_encrypted_server_handshake_parsed`.

### 2.2 Consequences

- `Common.StateMachine`, `Common.WireFormatStateMachine`,
  `Common.SystemProduct`, `Common.MachineProduct` and
  `Common.ChannelImplementation` need **no signature change**.
- The five sample protocols sharing `../common` (`calc_sample`, `ftp_sample`,
  `http_sample`, `tftp_sample`, `ymodem_sample`) need **no migration**.
- `Common.BufferedStream.buffered_stream_endpoint` is abstract over `state` and
  `result` and never mentions `local_event`; it needs no signature change.

### 2.3 Local events may emit wire output — generically

This is already true and already used. `TLS13.Spec.Endpoint.Client.local_event`
contains `ClientSendClientHello`, `ClientSendClientFinished`,
`ClientSendApplicationData`, `ClientSendKeyUpdate`, `ClientSendCloseNotify`;
`client_step` matches them with `client_wire_outputs_match`;
`local_process_correct` serializes the outputs and appends them to `sent`; and
`MachineProduct.mp_client_send` puts the payload in flight.

Therefore a wire-emitting internal step requires **no new machinery**: it is
classified `mp_client_send` rather than `mp_client_local`. We do not restrict
internal steps to be wire-silent. TLS's internal step happens to emit nothing.

The one semantic consequence to respect: both families are quiet-gated by
`product_step`, so a wire-emitting internal step is enabled only when the
single-slot channel is quiet, and it leaves a message in flight. A scheduler
for such a protocol must account for that. TLS's `ProcessPendingHandshake`
emits nothing, so it does not arise here.

---

## 3. TLS model changes

### 3.1 Record receipt

The client `WireEvent` for a handshake record must:

1. validate the record header and content type;
2. select the read epoch and key material;
3. authenticate and decrypt when protected;
4. advance the record read sequence exactly once;
5. append the physical record exactly once to `raw_received`;
6. store the recovered plaintext and a zero parse offset in connection state;
7. perform **no** handshake-semantic transition.

### 3.2 Pending plaintext state

Replace the `protected_handshake_head` encoding with an explicit structure that
records:

- the plaintext bytes;
- the current parse offset;
- whether the source record was cleartext or protected;
- that the offset is in bounds;
- that the processed prefix corresponds exactly to prior internal events.

The existing `hb_encrypted_server_handshake_bytes` /
`hb_encrypted_server_handshake_parsed` pair is the starting point, but the new
structure must not carry the head/tail asymmetry.

`protected_handshake_buffer_empty` already expresses the emptiness condition
that the record transition requires as a precondition; keep that requirement
(see decision **D3**).

### 3.3 Internal transition

One internal step:

1. requires retained plaintext with a non-empty unprocessed suffix;
2. parses exactly one handshake message at the current offset;
3. requires that message to be legal in the current control state;
4. performs the corresponding handshake transition;
5. advances the offset by exactly the parsed length;
6. leaves `raw_received`, `raw_sent` and the record sequence unchanged;
7. clears the pending structure exactly at exhaustion.

`Finished` retains its current atomic semantics, including application
read-key installation.

### 3.4 Concrete event representation

- Add one `local_event_kind` constructor in
  `src/impl/TLS13.Impl.Client.Types.fst:117` (e.g. `LocalProcessPendingHandshake`).
- Add one `local_event` constructor in
  `src/spec/core/TLS13.Spec.Endpoint.Client.fst:26`.
- Add one positive case to `client_local_event_matches`; its `| _, _ -> False`
  catch-all keeps the match exhaustive.
- Reuse the `client_event_representation` instance in
  `src/impl/TLS13.Impl.CanonicalTypes.fst:169` unchanged in shape.

### 3.5 Required composition lemma

Prove, and expose through `.fsti`, a composite:

> for a record `r` whose plaintext parses to messages `m₁ … mₙ`, the trace
> `Wire(r) :: Internal(m₁) :: … :: Internal(mₙ)` reaches the same state that
> the pre-refactor event sequence reached.

This is the abstraction that lets `TLS13.Impl.Driver.Pairing` (2157 + 1674
lines) and `TLS13.System` (3235 lines) keep reasoning message-wise instead of
re-deriving record structure. It is a required deliverable of Phase 2, not an
optional convenience.

### 3.6 Streaming parser, not a global signature change

The internal step parses one message at an offset, so it needs a parser
returning a *consumed length*. `src/spec/core/TLS13.Wire.Spec.fsti` declares 26
parsers; 20 already return one. The six that do not are all **whole-input**
parsers — they consume their entire argument by construction, so their consumed
length is definitionally `B.length input`:

| Parser | Call sites |
|---|---|
| `parse_tls_message` | 187 |
| `parse_plaintext` | 79 |
| `parse_key_update` | 15 |
| `parse_ignored_post_handshake` | 14 |
| `parse_supported_server_hello` | 14 |
| `parse_sealed_record` | 2 |

Changing their signatures would touch 311 call sites to convey no information.
`parse_tls_message content_type fragment` in particular parses a record's
*entire* fragment: the boundary comes from record framing, which is why it
carries no length.

The genuine need is a *streaming* parser over multi-message plaintext, which is
`parse_handshake` — and it already returns `(handshake_msg & nat)`. The residual
gap is only that `parse_handshake` covers the seven `handshake_msg` constructors
while `parse_tls_message` is what recognises `TlsKeyUpdate`.

Phase 0 therefore adds **one** streaming parser over handshake-content plaintext
returning `(M.tls_message & nat)`, covering `handshake_msg` and post-handshake
messages, plus a lemma relating it to `parse_tls_message` on single-message
fragments. Where a whole-input parser sits in a length-sensitive position, add a
`consumed == B.length input` lemma — zero call-site churn.

---

## 4. ProtocolImplementation changes

All changes are confined to `common/Common.ProtocolImplementation.fst` and its
instances.

### 4.1 New class fields

```fstar
  (* syntactic classification; enabledness comes from sm_step, not from here *)
  pi_internal: local_event -> bool;

  (* the protocol still owes internal progress from its current state *)
  pi_internal_pending: state -> prop;

  pi_process_internal: ... (* see 4.3 *)
```

`pi_process_local` gains the precondition `~(pi_internal ev)`. This restores
the guarantee that a separate constructor would have given syntactically: a
driver cannot hand-supply an internal event.

### 4.2 Status

```fstar
type internal_status =
  | InternalProgress    (* one internal step was taken *)
  | InternalQuiescent   (* no internal step enabled, and nothing pending *)
  | InternalBlocked     (* no internal step enabled, but progress is pending *)
  | InternalFailed      (* reuse existing process_status error refinement *)
```

`InternalBlocked` is necessary, not cosmetic. `legal_tls_message` requires
`Received CertificateVerify` at control state `HsCertificateValidated`
(`TLS13.Spec.StateMachine.fst:728`), reached only via
`LocalValidateCertificate` (line 538). So after `Internal(Certificate)` the
client has non-empty pending plaintext and **no enabled internal step**. Without
`InternalBlocked`, a scheduler would classify that as quiescence and read the
socket mid-flight.

`InternalFailed` reuses the existing `process_status`
(`DecodeError | IllegalTransition | ConnectionFailed`) and
`local_error_refines_state_machine`. No parallel failure taxonomy.

### 4.3 Correctness predicate

`internal_process_correct` is a thin derivation over `local_process_correct`:

```fstar
match result.process_status_internal with
| InternalProgress ->
    exists ev. pi_internal ev /\
      local_process_correct system ev ... (* StepOk case *)

| InternalQuiescent ->
    no_internal_step_enabled system pi_internal st0 /\
    ~(pi_internal_pending st0) /\
    same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
    wire_outputs == [] /\ local_outputs == []

| InternalBlocked ->
    no_internal_step_enabled system pi_internal st0 /\
    pi_internal_pending st0 /\
    same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
    wire_outputs == [] /\ local_outputs == []

| InternalFailed ->
    local_error_refines_state_machine system st0 st1 wire_outputs local_outputs
```

where

```fstar
let no_internal_step_enabled system is_internal st0 : prop =
  forall ev st1 out.
    is_internal ev ==>
    ~(system.wfsm_state_machine.sm_step st0 (SM.LocalEvent ev) st1 out)
```

Quiescence and blockedness must be **proven**, never defaulted to on
implementation failure.

### 4.4 Compatibility

Protocols with no internal events set:

```fstar
  pi_internal = (fun _ -> false);
  pi_internal_pending = (fun _ -> False);
```

Both `no_internal_step_enabled` and the `~(pi_internal ev)` precondition then
discharge trivially. Provide one reusable helper so the five sample instances
add a few lines each and no proof obligations of substance.

---

## 5. Scheduling

Inside the TLS `bse_process` (or a thin TLS-side wrapper), not in a new generic
abstraction:

```text
1. Attempt internal progress.
2. InternalProgress -> account for outputs, repeat (fuel-bounded).
3. InternalFailed   -> terminate with the explicit failure.
4. InternalBlocked  -> return to the TLS workflow for the required local action.
                       Do NOT read the socket.
5. InternalQuiescent + complete frame buffered -> process one frame.
6. InternalQuiescent + incomplete frame        -> read more bytes.
```

`TLS13.Impl.Client.Types.next_local_action` (line 139, with `next_local_ready`
and `next_local_kind`) already exists and supplies step 4's required action.

Byte ownership is unchanged:

```text
transport_received = committed_ciphertext ++ pending_ciphertext
```

Retained plaintext is protocol state and is **not** part of
`pending_ciphertext`.

Termination: explicit fuel in the loop, plus a TLS-specific measure — the
unprocessed pending-plaintext byte count strictly decreases on every
`InternalProgress` (guaranteed by §3.3 step 5, since `0 < consumed`).

---

## 6. System and temporal proof

`Common.SystemProduct` and `Common.MachineProduct`: **no change**. Internal
endpoint moves are already `mp_client_local` / `mp_server_local`.

`TLS13.System`: no new move families. The work is in the TLS-specific delivery,
projection and invariant proofs:

- record delivery consumes the in-flight payload and establishes the pending
  plaintext witness, instead of immediately appending a semantic received
  message;
- internal moves discharge that witness one message at a time, leaving the
  channel quiet;
- the sent/received pairing argument must survive intermediate pending states.

`TLS13.System.Temporal`: the theorem keeps its current statement and scope. The
ready/quiescent payoff gains one clause: at application readiness, required
pending handshake input has been exhausted (`~(pi_internal_pending st)`).
"Delivery completes next" remains a channel-quiescence property; pending
plaintext in an endpoint does not make the channel non-quiet.

No `runtime_refines_system` relation, no separation-logic `MachineProduct`, no
concrete-to-system simulation. The two halves of the development continue to
meet by sharing the endpoint transition relations.

---

## 7. Phases

Each phase must leave the tree verifying and must be committed separately.

The temporal proof (Phase 7) precedes the driver/Chromium refactor (Phase 8)
deliberately. Only the temporal proof can invalidate the event design; if
internal moves cannot preserve `tls_system_inv`, Phases 2–5 need rework, and
discovering that after rewriting the Engine, the runtime C and the Chromium
shim would waste all of it. Interop is not deferred by this: the root gate runs
`test-openssl-echo` and `test-client-engine-openssl-echo` on every phase, and
Phase 3 keeps the Engine alive through semantics-free aliases, so live interop
is exercised at every phase boundary. Phase 8 defers the *Engine refactor*, not
interop validation.

Cleartext uniformity (Phase 6) precedes the temporal proof for the same reason
in miniature: migrating `ServerHello` changes `client_step`'s `WireEvent`
shape, which is exactly what `tls_system_inv` and `mp_deliver_to_client` reason
over. Settling it first means the temporal proof is done once.

### Phase 0 — Baseline, characterisation, streaming parser
- Confirm `make -j128 verify test` is green; record wall-clock time.
- Record the current public API and extraction symbols, in particular
  `TLS13.Impl.Client.Engine.fsti` (`new_engine`, `poll`, `feed_network`,
  `copy_certificate_chain`, `copy_certificate_verify_request`,
  `complete_certificate_verification`,
  `complete_certificate_signature_verification`, `send_application_data`,
  `send_close_notify`, `free_engine`).
- Record the unverified C baseline: 2718 lines total, `runtime/tls13_client_engine.c`
  443 lines forwarding into `TLS13_Impl_Client_Engine_poll` / `_feed_network`,
  no C-side sequencing. This is the Phase 8 comparison point.
- Add verified lemmas (not C tests) characterising today's behaviour on: a
  protected record with multiple handshake messages; one-record raw accounting;
  interleaved certificate validation; `Finished` with application-key install.
- Add the streaming handshake-plaintext parser of §3.6.

### Phase 1 — ProtocolImplementation
Files: `common/Common.ProtocolImplementation.fst` and TLS instances.
- Add `pi_internal`, `pi_internal_pending`, `pi_process_internal`.
- Add `internal_status`, `no_internal_step_enabled`, `internal_process_correct`.
- Add `~(pi_internal ev)` to `pi_process_local`.
- Add the no-internal-events compatibility helper; apply to TLS instances.
- No TLS behaviour change.

Exit: root gate. Sample protocols are deferred to Phase 9 (§9, **S5**); record
which ones break.

### Phase 2 — TLS receive semantics
Files: `src/spec/core/TLS13.Spec.StateMachine.fst`,
`TLS13.Spec.StateMachine.Canonical.fst`, replay/log/correspondence modules,
`TLS13.Spec.Endpoint.Client.fst`, `TLS13.Impl.Client.Types.fst`,
`TLS13.Impl.CanonicalTypes.fst`.
- Split record receipt from message processing; remove the head/tail bool.
- Introduce the explicit pending-plaintext structure.
- Define the pipeline over *any* client-received handshake record: its legality
  relation must not mention "protected".
- Add the internal local-event constructor and its legality.
- Prove the record and message projections and the §3.5 composition lemma.
- Deliver the total, shape-agnostic received-message projection (§3.5).
- Update replay and canonical-shape proofs.

Exit: one record induces a finite legal sequence of internal steps; raw bytes
and record sequence accounted exactly once; full gate.

#### 7.2.1 Status and the ordering constraint discovered while attempting it

A first implementation of Phase 2 is parked on branch
`internal-events-phase2-wip`. The following is verified there and should be
reused verbatim:

- `TLS13.Spec.StateMachine`: the event type gains
  `ConnReceiveHandshakeRecord of receive_handshake_record_step`
  (`{ receive_record_plaintext : B.bytes }`), whose step advances
  `record_read` once, retains the plaintext at parse offset `0`, and performs
  **no** handshake transition. `protected_handshake_head` is deleted, and
  `step_protected_handshake` becomes uniformly the former tail formula.
  `event_raw_delta_legal` charges exactly one `Application_data` record to the
  record event and nothing to the internal event.
- `legal_receive_handshake_record` carries a well-formedness *guard* (the
  plaintext prefix parses to a supported, currently-legal handshake message).
  A guard is not a transition, so it does not re-create the fork; it keeps a
  garbage record unreceivable, exactly as today.
- `TLS13.Impl.ConnectionState.Model`: `receive_handshake_record_state`,
  `protected_handshake_head_state` (defined *as* the two-event composition),
  `protected_handshake_head_legal`, plus
  `lemma_protected_handshake_head_legal_intro` and
  `lemma_protected_handshake_head_state_evolves`. These make the head path a
  definitional composition rather than a restructuring of Pulse control flow.
- The behaviour-preservation argument, checked by hand and re-derivable as a
  lemma: for `EncryptedExtensions` / `Certificate` / `CertificateVerify` the
  record event's `next_seq` followed by the internal step's restore yields
  exactly today's head result; for `Finished`, `R.install_keys` ignores the
  state it is given, so the order is irrelevant. The refactor is therefore
  semantics-preserving on the client receive path.

**The obstacle, precisely.** The peer-pairing argument replays the sender's
and the receiver's event lists in lock step against a shared byte stream.
Internal events break lock step by construction: one sent record event
corresponds to one received *record* event plus N received *internal* events.

The machinery for this already exists and is already used. The
`lemma_*_replay_skip_*_head_preserves_peer_stream` family in
`TLS13.ConnectionState.ProtectedWireHead` skips exactly those head events that
consume no bytes on the relevant side. Today its received-side guard is

```fstar
| CS.ConnProtectedHandshake step -> not step.CS.protected_handshake_head
```

which in the new event type becomes the strictly simpler

```fstar
| CS.ConnProtectedHandshake _        -> True    (* always a stutter *)
| CS.ConnReceiveHandshakeRecord _    -> False   (* consumes one record *)
```

That is the whole of the structural change: internal events are received-side
stutters, and the record event takes over the pairing role that the head step
used to play. Every one of the ~117 `ConnNetworkEvent` occurrences in that
module is either this guard, or a *representative* event inside a projection
predicate (`received_event_decode_projection m (ConnNetworkEvent {Received;
TlsHandshake msg}) raw` is by definition `received_single_protected_message_decode
m msg raw`, which is shape-independent and needs no change).

Two genuine edits remain:

1. **`lemma_single_message_sender_normalizes_received_handshake_head`**
   (`ProtectedWireHead.fsti:329`, 4 external call sites: 3 in
   `ProtectedWireServerFlightInversion`, 1 in `ProtectedWireServerFlight`).
   Its conclusion `receiver_head == ConnNetworkEvent { Received; TlsHandshake
   msg }` must become `receiver_head == ConnReceiveHandshakeRecord { plaintext }`
   for protected handshake messages. Callers then pair the record event with
   the sender's network event and let the existing skip machinery absorb the
   internal step that follows.

2. **`lemma_single_protected_message_seal_excludes_protected_head`**
   (`ProtectedWireProjection`) should be **deleted**, not repaired. It currently
   derives its contradiction from the head step's strict
   `consumed < B.length fragment`, which no longer exists. The correct
   argument is already written two branches below its only call site
   (`ProtectedWireHead.fst:1188`): at a head the receiver's pending buffer is
   empty, so `step.protected_handshake_fragment` would have to be empty, which
   contradicts the parse. That argument survives the refactor verbatim and
   subsumes the deleted lemma.

3. **The receiver's event list grows.** This is the one genuinely
   non-mechanical consequence. Where the sender's list has one
   `ConnNetworkEvent`, the receiver's now has `ConnReceiveHandshakeRecord`
   followed by one `ConnProtectedHandshake` per message. The inversion
   argument in `ProtectedWireServerFlightInversion` (3520 lines) currently
   destructures the two lists at equal length — e.g. `stageA_result`'s
   existential packages a receiver list `cEE :: cCert :: cCV :: cFin :: tail`
   in bijection with the server's. Each receiver element becomes two, and the
   internal one is discharged by the skip machinery. Budget this file, plus
   `ProtectedWireServerFlight` (6067 lines), as the bulk of Phase 2a: the edits
   are individually routine but there are many, and each changes an
   existential's arity.

#### Resolving the lock-step breakage

The lock step is **not** in the replay relations.
`conn_events_sent_seal_replay` and `conn_events_received_decode_replay`
(`TLS13.Spec.StateMachine.Replay`) each range over *one* side's own event list
and *its own* byte streams; the two sides are coupled only by
`Seq.equal sender_raw_sent receiver_raw_received`. Nothing in either relation
requires the lists to have equal length. The lock step lives in exactly one
place: `raw_flight_spine`
(`TLS13.ConnectionState.ClientCanonicalShape.fsti:121`), which asserts

```fstar
raw_suffix == raw_ee :: raw_cert :: ConnLocalEvent cv_validate ::
              raw_cv :: ConnLocalEvent cv_verify :: raw_sf :: raw_tail
```

one raw client event per received message. That single equality is what makes
the receiver's list grow relative to the sender's, and it is reached from
exactly one junction: `ProtectedWireServerFlightInversion` calls
`lemma_client_canonical_appdata_exact_spine` to obtain the message-level shape
and then `lemma_client_raw_suffix_flight_spine` to descend to raw events.

Three mechanisms resolve it.

**M1 — `canonical_log` erases record events.**

```fstar
let rec canonical_log (events:list CS.conn_event) : list CS.conn_event =
  match events with
  | [] -> []
  | CS.ConnReceiveHandshakeRecord _ :: rest -> canonical_log rest
  | ev :: rest -> canonical_event ev :: canonical_log rest
```

This is sound because `canonical_log` is a **message-level** normalizer and was
never byte-preserving: today a *tail* `ConnProtectedHandshake` consumes zero
received bytes, yet `canonical_event` maps it to a `ConnNetworkEvent` worth a
whole record. Erasing an event that delivers no message is the same kind of
step. The payoff is large: `lemma_client_canonical_appdata_exact_spine` and
every message-level consumer downstream — including the Pairing theorem — keep
their statements **verbatim**. Blast radius is 4 files (`ClientCanonicalShape`
`.fst`/`.fsti`, `ServerCanonicalShape`, `ProtectedWireServerFlightInversion`).

**M2 — slots become delivery groups.** A first attempt at M2 used a
`skip_records` function that drops leading record events. That is wrong: the
record event is the *byte-consuming* member of the group, so dropping it is not
replay-preserving on the receiver side. The correct primitive keeps the group
intact. In `ClientCanonicalShape`:

```fstar
(* The events by which the client takes delivery of one handshake message.
   Today always a singleton; after the split, a record event followed by the
   internal event that consumes it. *)
let delivers_handshake (grp:list CS.conn_event) (msg:M.handshake_msg) : prop =
  match grp with
  | [ev] -> canonical_event ev == recv_ev msg
  | _    -> False
```

and `raw_flight_spine` replaces its single list equality by an append of groups:

```fstar
raw_suffix ==
  L.append g_ee (L.append g_cert (ConnLocalEvent cv_validate ::
    L.append g_cv (ConnLocalEvent cv_verify :: L.append g_sf raw_tail)))
/\ delivers_handshake g_ee   (M.EncryptedExtensions ee)
/\ delivers_handshake g_cert (M.Certificate cert)
/\ ...
```

With singleton groups `L.append [x] l` reduces to `x :: l`, so today's statement
is recovered definitionally and the step is behaviour-preserving. In Phase 2b
`delivers_handshake` gains one case:

```fstar
  | [CS.ConnReceiveHandshakeRecord _; ev] -> canonical_event ev == recv_ev msg
```

and nothing else in the spine changes.

**M3 — peeling a group.** The byte-level pairing peels a whole group against
the sender's single `ConnNetworkEvent`. In a pair
`protected_record_count Sent msg == 1` for every handshake message
(`TLS13.Spec.StateMachine.fst:1577`), so the sender emits exactly one record per
message and the group has fixed length two — never variable-length stuttering.
The record event carries the bytes and pairs with the sender's event; the
internal event is a zero-byte stutter absorbed by the existing
`lemma_received_replay_skip_empty_head_preserves_peer_stream`, whose guard
*simplifies* to `ConnProtectedHandshake _ -> True` /
`ConnReceiveHandshakeRecord _ -> False`.

Coalesced records (a peer packing several messages into one record) produce a
longer group. That case is already outside the pairing theorem's scope — it
concerns interop with third-party servers, not this implementation paired with
itself — so M3 does not need the general form to close Phase 2.

**Revised ordering.** Phase 2 now splits into three gated steps, the first two
behaviour-preserving on today's event type:

- **Phase 2a-i — delivery groups in the spine.** Introduce
  `delivers_handshake` with only the singleton case and restate
  `raw_flight_spine`, `lemma_client_raw_suffix_flight_spine` and its single
  caller in `ProtectedWireServerFlightInversion` through group appends.
  Behaviour-preserving; gates alone.
- **Phase 2a-ii — group-based pairing.** Restate the ~9 normalization
  and pairing lemmas over groups, replace
  `lemma_single_protected_message_seal_excludes_protected_head` with the
  buffer-emptiness argument already written at its only call site
  (`ProtectedWireHead.fst:1188`). Gates alone.
- **Phase 2b — the event split.** *Landed, by a different route than
  planned.* See "Phase 2b as built" below.

#### Phase 2b as built — permissive spec plus transport

Two designs were attempted and abandoned before the one that landed.

1. **A new `ConnReceiveHandshakeRecord` constructor** (branch
   `internal-events-phase2-wip`). Abandoned: it forces the `canonical_log`
   erasure M1, which breaks the pure, list-shaped
   `lemma_canonical_flight_raw_spine` that the whole pairing stack rests on.
2. **Banning the network route** for client-received protected handshake
   messages, via a guard in `legal_tls_message`. Abandoned: with the network
   route illegal there is no transport lemma, so every pairing proof would have
   to be rewritten onto head-step shapes.

**What landed instead.** The spec is made *permissive* and the two descriptions
are proved equal:

- `legal_protected_handshake_step` no longer requires
  `consumed < B.length fragment` in its head case, so a single-message record
  is describable as a *saturating head step* as well as a `ConnNetworkEvent`.
  Both routes stay legal.
- `TLS13.Spec.StateMachine.Replay` gains a family of **transport lemmas**
  proving the two descriptions denote the same transition: same legality
  (`lemma_single_message_head_step_legal`), same successor model (`_model`),
  same raw accounting (`_raw_delta`, and its converse), same decode projection
  (`_decode`), and therefore the same replay in both the received-decode and
  the sent-seal directions (`_replay_normalizes`,
  `_seal_replay_normalizes`).
- A new module `TLS13.ConnectionState.ProtectedWireNormalize` lifts that to a
  whole server flight, in both replay directions.
- The pairing stack is made **shape-agnostic**: `ProtectedWireHead`,
  `ProtectedWireServerFlight`, `ProtectedWireServerFlightInversion` and
  `ProtectedWireClientFinishedInversion` now carry the client's *raw* events
  together with `received_handshake_head_normal_form`, and normalise their own
  replays where they need the network-event spine.
  `client_normalized_appdata_exact_spine` is stated over raw events in normal
  form rather than over literal `ConnNetworkEvent`s.

**What did not land, and why.** `TLS13.Impl.ConnectionState.Model` still emits
`ConnNetworkEvent` for a single-message record. Emitting the head step instead
requires `protected_handshake_buffer_empty` at the four
`mark_received_*` call sites in `TLS13.Impl.ConnectionState.Network`, and that
fact is only available once the pending-plaintext structure is threaded through
the Pulse receive path — which is Phase 3 work. The proof stack is already
prepared for it: because every pairing lemma now accepts either shape, flipping
the emission is a local change with no further proof obligations in the
properties layer.

`TLS13.Spec.InternalEvent.Baseline` records the new invariant as B5:
`lemma_single_message_record_is_a_head_step` and
`lemma_single_message_routes_agree`.

## Phase 3 as built — implementation fork removed; exit criterion re-scoped

**What landed.** The implementation-level fork is gone. It turned out to be a
single guard in `process_coalesced_network_bytes`:

```
let coalesced = SZ.lt consumed fragment_len;
if coalesced { try_process_protected_handshake_head ... }
else         { process_legacy_coalesced_fallback ... }
```

— the implementation branched on exactly the condition Phase 2b deleted from
the head branch of `legal_protected_handshake_step`. Relaxing it to `SZ.lte`
sends every protected handshake record down the head route. The same strict
bound had been threaded through five further layers
(`lemma_legal_protected_handshake_head`,
`try_process_protected_handshake_head`, `mark_received_protected_{ee,cert,cv}`,
`finish_protected_handshake_head`, `store_pending_protected_handshake`) and was
relaxed at each; Phase 2b's spec change carries them all.

The one place needing real work was `store_pending_protected_handshake`: when
the head message saturates the fragment, `set_pending_protected_handshake`
resets the pending buffer to `{empty; 0}` rather than retaining the
fully-consumed fragment, and the implementation now mirrors that. The collapse
is factored into `collapse_sized_bytes_to_empty` because unfolding
`sized_bytes_exactly` inside a conditional branch leaves the frame with uvars.

This is verified end to end: the extracted-C OpenSSL echo interop and the
Chromium async HTTPS demo both pass, so single-message records really do take
the new route at runtime.

**What did not land: the exit criterion, and why it belongs to Phase 5.** The
stated exit — "`process_network_bytes` is the only network receive primitive" —
cannot be met at this point in the sequence. `process_coalesced_network_bytes`
requires `CT.client_end_to_end_invariant`, and `process_network_bytes` does
not. Reducing either to an alias of the other therefore forces that invariant
into `process_network_bytes`'s precondition, and its callers cannot supply it:
`TLS13.Impl.Client.Driver.BufferedNetwork` deliberately propagates the
invariant *conditionally* (`invariant before ==> invariant after`) rather than
carrying it.

`client_end_to_end_invariant` is `client_state_correct /\
connection_state_raw_to_message_replay_consistent` — genuine log-consistency
facts, not derivable from `connection_exactly`. It *is* an inductive invariant
(established by `lemma_initial_client_state_correct`, preserved by
`lemma_network_bytes_end_to_end_correct_client_end_to_end_invariant`); the
driver simply does not carry it in `buffered_driver_indexed`. Adding it there
ripples across ~180 occurrences in 20 client and server driver modules — which
is precisely the surface Phase 5 (BufferedStream and Channel) already owns.

**Recommendation for the next session.** Before accepting that ripple, evaluate
the cheaper idiom the codebase already uses: give `process_network_bytes` a
*conditional* postcondition,

```
(client_end_to_end_invariant 'st0 ==>
   coalesced_network_bytes_end_to_end_correct 'st0 st1 buffer_resp ...)
```

mirroring `BufferedNetwork`'s existing `invariant before ==> invariant after`
shape. The obstacle to check first is that Pulse needs the invariant as a
*precondition* to call `try_process_protected_handshake_head` at all, so this
only works if that fn's dependence can be narrowed to facts derivable from
`connection_state_consistent`. If it cannot, defer the merge to Phase 5 and
re-order the plan accordingly.

## Phase 3 (internal primitive) as built

**The internal event.** `TLS13.Spec.Endpoint.Client.local_event` gained
`ClientProcessPendingHandshake`, mapped by `client_local_event_matches` to
`CS.ConnProtectedHandshake step` with `protected_handshake_head == false`; the
implementation mirror is `CT.LocalProcessPendingHandshake`, appended last in
`local_event_kind` so the extracted C enum stays ABI-compatible.

`client_step` needed **no change**. Its `LocalEvent` case already passes
`B.empty` as the raw-*received* delta, and `event_raw_delta_legal` for a tail
`ConnProtectedHandshake` demands exactly `Seq.equal raw_received B.empty` with
`received_event_decode_projection` trivially `True`. §2.3 likewise needed no
generalisation: `ClientSendClientHello` was already a local event emitting wire
output.

Two facts made the drain wiring cheap and are worth recording:

- **A head step cannot consume empty raw input.** `head == true` requires
  `raw_records_exactly raw Application_data 1`; chaining
  `lemma_raw_records_exactly_one_parse_record`,
  `lemma_parse_record_implies_parse_record_wire` and
  `lemma_parse_record_wire_some_consumed_positive` (consumed `>= 5`) contradicts
  `raw == B.empty`. So the internal event is *necessarily* a tail step and
  `pending_protected_handshake_result_correct` needed no `head == false`
  conjunct.
- **`copy_pending_protected_handshake` returns `None` exactly when exhausted.**
  Propagating that through `process_pending_protected_handshake`'s `None` case
  gives `parsed >= B.length bytes` for free, which is precisely
  `~ client_internal_pending`. Hence `client_internal_pending st` is *defined*
  as `parsed < B.length bytes`, and `no_internal_step_enabled` follows from the
  tail branch of `legal_protected_handshake_step` pinning `offset` to `parsed`
  and requiring `offset < B.length fragment`.

**Deferred to Phase 5: `InternalBlocked`.** `client_process_internal` currently
produces only `InternalQuiescent`, `InternalProgress` and `InternalFailed`. When
the client sits after `Certificate` awaiting `LocalValidateCertificate`, the
drain returns `IllegalTransition`, which is mapped to `InternalFailed`. This is
*sound* — `local_error_refines_state_machine` permits the `st1 == st0` "no move"
disjunct — but weaker than intended. Producing `InternalBlocked` requires
inverting `legal_handshake_message` to show no tail step is legal in that
control state. Phase 5 is where `InternalBlocked`'s payoff is consumed (it must
never authorise a socket read) and where `next_local_action` is wired in, so the
obligation is discharged there.

**Temporary wart.** `client_process_internal` allocates and frees a 0-length
`Vec` per call to supply the empty payload. The Engine already keeps a
persistent `engine_empty_payload`; Phase 8 folds the Engine into the driver and
this allocation goes away.

### Phase 3 — Pulse implementation
Files: `src/impl/TLS13.Impl.Client.fst/.fsti`, client Types/Repr/ConnectionState.
- `process_network_bytes` stops after the record transition.
- Implement one-message internal processing; prove `internal_process_correct`.
- Prove the pending-byte decrease and invariant preservation.
- Migrate the four protected messages (`EncryptedExtensions`, `Certificate`,
  `CertificateVerify`, `Finished`) onto the pipeline.
- Reduce `process_coalesced_network_bytes` and
  `process_pending_protected_handshake` to aliases with no independent
  semantics.

Exit: `process_network_bytes` is the only network receive primitive;
`process_internal` is the only retained-message primitive; full gate.

### Phase 4 — Single ProtocolImplementation
Files: `TLS13.Impl.Client.CanonicalProtocol.fst`,
`TLS13.Impl.Server.CanonicalProtocol.fst`, driver progress modules.
- Package network, local and internal processors.
- Extend `client_progress_preorder`, `state_ahead` and `valid_byte_trace`
  through internal steps.

Exit: the coalesced public-site execution establishes `valid_byte_trace`; full
gate.

### Phase 5 — BufferedStream and Channel
Files: TLS buffered driver modules, client/server ChannelImplementation.
- Implement the §5 schedule inside the TLS instance; `InternalBlocked` must
  never authorise a socket read.
- Wire in the existing `next_local_action` for the blocked case.
- Point both channel instances at the unified ProtocolImplementation.
- Prove handshake internal steps are application-invisible.

Exit: no production code calls an alternate TLS receive function; no
zero-length reads; no unbounded loops; full gate.

### Phase 6 — Cleartext uniformity (revertable)
Files: `TLS13.Spec.StateMachine.fst` (cleartext raw shapes),
`TLS13.Spec.Endpoint.Client.fst`, Pairing modules.
- Migrate `ServerHello` onto the pipeline.
- Migrate `HelloRetryRequest`, or record the documented exception of §9 **S4**
  if its `raw_records_exactly` record-stream shape proves disproportionate.
- Add the mechanical new-constructor branches in
  `PairingNoTailServerHelloWindowRank` and `PairingNoTailInversion`.

Exit: `client_step`'s `WireEvent` case is record-only for all client-received
handshake records, or the exception is documented with a rationale; full gate.
Keep-or-revert is decided here, before Phase 7 depends on it.

### Phase 7 — System and temporal
Files: `src/impl/TLS13.System.fst`, `TLS13.System.WireStep.fst`,
`TLS13.System.Ordering.fst`, `TLS13.System.ProgressCount.fst`,
`TLS13.System.Temporal.fst` and supporting invariants.
- No new move families; `mp_client_local` / `mp_server_local` already supply
  quiet-gated internal moves.
- Refactor delivery so it establishes the pending witness.
- Carry that witness in `tls_system_inv` between delivery and the internal
  steps that discharge it.
- Re-prove invariant preservation and the temporal theorem at unchanged scope,
  with the added ready/quiescent clause `~(pi_internal_pending st)`.

Exit: a delivered multi-message record is followed by internal steps with the
channel quiet; full gate.

### Phase 8 — Drivers, Engine and Chromium
Files: client/server Driver modules, `TLS13.Impl.Client.Engine.fst/.fsti`,
`runtime/`, `c_stubs/`, Chromium extraction/API modules.
- Reduce `Client.Engine` to a facade over the production driver; its interface
  may change (§9 **S6**).
- Update `runtime/tls13_client_engine.c` and the Chromium socket shim in step.
- Remove duplicate engine ownership and scheduling logic.
- **Gate:** unverified C must not grow in responsibility against the Phase 0
  baseline — no C loop over handshake messages, no C-side record parsing, no
  C-side scheduling decision, no direct C call into inner endpoint APIs.
  Verify by extracted call-graph inspection and a C line-count diff.
- Re-check cross-record handshake fragmentation against public sites (§10).

Exit: one client driver state and scheduler; Chromium, localhost and generic
channel users share it; `test-client-engine-openssl-echo`,
`test-chromium-client-demo` and `test-openssl-http-preconnect` pass; full gate.

### Phase 9 — Cleanup, samples and audit
- Delete the coalesced/pending aliases and obsolete head/tail predicates.
- Migrate the five sample protocols (`calc`, `ftp`, `http`, `tftp`, `ymodem`)
  with the compatibility helper; extend the root gate to cover their gates.
- Audit `noextract` and the extraction surface.
- Regenerate and inspect extracted C; confirm the call graph is
  `Chromium ABI -> exported driver -> scheduler -> ProtocolImplementation ->
  canonical state machine`, with no C-level handshake sequencing.
- Update `ARCH_AUDIT.md`, `BUFFERING_DESIGN.md`, `PAIRING_THEOREM.md`.

---

## 8. Proof obligations

**ProtocolImplementation**
- [ ] `InternalProgress` corresponds to one canonical `LocalEvent` step whose
      event satisfies `pi_internal`.
- [ ] `InternalQuiescent` proves no enabled internal step and nothing pending.
- [ ] `InternalBlocked` proves no enabled internal step and something pending.
- [ ] `InternalFailed` refines the existing error semantics.
- [ ] Received history unchanged by internal steps.
- [ ] Sent history extended by exactly the serialized internal wire outputs.
- [ ] `pi_process_local` rejects internal events.
- [ ] No-internal protocols discharge all of the above trivially.

**TLS record transition**
- [ ] One physical record parsed and consumed.
- [ ] One authenticated decryption, correct epoch and sequence number.
- [ ] Record read sequence advances exactly once.
- [ ] `raw_received` appends the record exactly once.
- [ ] Recovered plaintext stored exactly; offset starts at zero.
- [ ] No semantic handshake transition occurs.

**TLS internal transition**
- [ ] Exactly one message parsed at the current offset.
- [ ] Parsed bytes equal the corresponding plaintext slice.
- [ ] Message legal in the current control state.
- [ ] Transcript and control advance exactly once.
- [ ] `raw_received`, `raw_sent` and record sequence unchanged.
- [ ] Offset strictly advances; pending cleared exactly at exhaustion.
- [ ] Required local validation can interleave.
- [ ] §3.5 composition lemma holds and is exposed in `.fsti`.

**Buffering**
- [ ] `transport_received = committed ++ pending_ciphertext`.
- [ ] Complete records committed exactly once.
- [ ] Retained plaintext not counted as unread transport input.
- [ ] Internal progress requires no socket read.
- [ ] `InternalBlocked` never authorises a read.
- [ ] Fuel bounds every loop.

**Channel**
- [ ] Application log is exactly the canonical projection.
- [ ] Handshake internal steps are application-invisible.
- [ ] Channel snapshots imply canonical reachability.

**System and temporal**
- [ ] Internal moves preserve the system invariant and leave the channel quiet.
- [ ] Existing send/delivery byte pairing remains valid.
- [ ] Delivery establishes the exact pending witness.
- [ ] Internal steps discharge it without changing wire accounting.
- [ ] Application readiness implies `~(pi_internal_pending st)`.
- [ ] Delivery-completes-next still holds as channel quiescence.
- [ ] The temporal theorem is re-established at unchanged scope.

---

## 9. Settled decisions

**S1 — Classifier shape.** Internal events are a distinguished class of
`LocalEvent`, identified by a *syntactic* `pi_internal : local_event -> bool`
together with a *state* predicate `pi_internal_pending : state -> prop`.
Enabledness is derived from `sm_step`, so the classifier itself need not be
state-dependent. No new `event` constructor and no fifth type parameter.

**S2 — `InternalBlocked`.** Adopted, and kept generic: the four-way
`internal_status` lives in `Common.ProtocolImplementation`, not in TLS, so any
protocol can use it and no-internal protocols discharge it trivially. §4.2 gives
the concrete `CertificateVerify` case that forces the distinction. The rejected
alternative — three statuses with the TLS driver disambiguating via
`next_local_action` — leaves the generic scheduler unsound for other protocols.

**S3 — Pending plaintext at record receipt.** The pending structure must be
empty as a precondition of the record `WireEvent`. A single pending fragment, no
queue. This is what `protected_handshake_buffer_empty` already enforces and what
the §5 schedule guarantees.

**S4 — Cleartext uniformity: staged, revertable.** The scope is smaller than it
appears. `TLS13.Messages.handshake_msg` has exactly seven constructors —
`ClientHello`, `ServerHello`, `EncryptedExtensions`, `Certificate`,
`CertificateVerify`, `Finished`, `HelloRetryRequest`. There is no
`NewSessionTicket`, and `KeyUpdate` is a `tls_message` variant handled at
`ControlApplicationData`. So client-received handshake messages are exactly the
four protected ones — precisely `protected_handshake_message_supported`, so the
internal path needs no extension — plus cleartext `ServerHello` and
`HelloRetryRequest`. Those two are the whole of the question; CCS, application
data and alerts are not handshake messages and keep direct wire→semantic steps
regardless, so total uniformity across content types was never available.

Uniformity is cheaper than it looks: `TLS13.Impl.Driver.Pairing.fsti:238`
already projects both shapes to a message, so the pairing machinery is shape-
agnostic, and `PairingNoTailServerHelloWindowRank`'s `ConnProtectedHandshake`
branches discharge via `assert False` on server-role models — a new constructor
needs the same mechanical branch. The one sharp edge is
`received_cleartext_tls_message_raw`, which binds `HelloRetryRequest` to
`raw_records_exactly raw T.Handshake 1` — a record *stream* of one, not a single
physical record.

Decision: target uniformity, do it in Phase 6, and keep it revertable. If it
overruns, stop with a documented bounded exception — `client_step`'s `WireEvent`
retains an `exists msg` disjunct for exactly two cleartext messages. There is
still one receive implementation and no competing semantics.

**S5 — Sample protocols.** TLS first. The five sample protocols sharing
`../common` are migrated in Phase 9, and the root gate is extended to cover
their gates then. They are not in the root gate today and their churn is
limited to the compatibility helper.

**S6 — Engine interface.** `TLS13.Impl.Client.Engine.fsti`, `runtime/` and
`c_stubs/` may all change together. The binding constraint is not ABI stability
but that **unverified C must not grow in responsibility**: no C loop over
handshake messages, no C-side record parsing, no C-side scheduling decision, no
direct C call into inner endpoint APIs. Measured in Phase 8 against the Phase 0
baseline.

---

## 10. Non-goals

- No new TLS features, versions or cipher suites.
- No decryption in the pure wire parser.
- No treating decrypted handshake messages as independently received records.
- No outbound handshake-record coalescing in the server.
- No new generic buffering abstraction.
- No new move families in `Common.SystemProduct` or `Common.MachineProduct`.
- No restriction that internal steps be wire-silent (see §2.3).
- No `runtime_refines_system` relation or concrete-to-system simulation.
- No restructuring of `TLS13.Impl.Driver.Pairing` beyond what the new event
  cases force.
- No global change to parser signatures (see §3.6).
- **No support for cross-record handshake fragmentation.** TLS 1.3 permits one
  handshake message to span several records, but
  `legal_protected_handshake_step` already requires a message to lie wholly
  within one record's plaintext, and **S3** preserves that. This is a
  pre-existing limitation, not one introduced here, and public-site browsing
  already works against it. Phase 8 re-checks it in interop; if a public site
  does fragment, the fix is a multi-record pending buffer — a contained change
  to the pending structure, not to the event design.

---

## 11. Completion criteria

- [ ] A record with multiple handshake messages is one wire transition followed
      by sequential internal transitions.
- [ ] Record sequence and raw history advance once per physical record; the
      transcript advances once per semantic message.
- [ ] Single-message and coalesced protected input use the same implementation.
- [ ] Production client, Chromium facade and generic channel share one
      `ProtocolImplementation`; likewise the server.
- [ ] `valid_byte_trace` covers the public-site coalesced execution.
- [ ] `TLS13.System` uses the same endpoint transition relations, with no new
      product move families.
- [ ] The temporal theorem is re-established at unchanged scope.
- [ ] Coalesced/Engine semantic forks are deleted.
- [ ] Extracted C contains only allocation, socket, callback, ABI and platform
      shims.
- [ ] `make -j128 verify test` passes.
