# Main pairing theorem: end-to-end key-material agreement

This note explains the audit-facing theorem
`TLS13.Impl.Driver.Pairing.lemma_client_server_driver_end_to_end_key_material_agrees`.
It is grounded in the current code in
`src/impl/TLS13.Impl.Driver.Pairing.{fsti,fst}` and the supporting pure
state-machine definitions in `src/spec/core/TLS13.Spec.StateMachine.fst` and
supporting lemmas in `src/spec/properties/TLS13.ConnectionState.Lemmas.{fsti,fst}`.

The short version: the theorem is a compositional bridge. Given two
application-ready client/server model states, matching external transport byte
histories, no unread retained transport suffix, and several semantic pairing
facts about X25519 shares, transcript/key-derivation checkpoints, and current
application traffic material, it proves that the supported-profile derived
key material agrees and that the current application record read/write key/IV
material agrees. It is not, by itself, a theorem that derives those semantic
pairing facts from only two live driver resources and the network.

## Where the theorem lives

Interface statement:

```fstar
val lemma_client_server_driver_end_to_end_key_material_agrees
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : Lemma
      (requires
        client_server_driver_end_to_end_agreement_inputs
          client server client_received client_sent server_received server_sent)
      (ensures
        client_server_driver_supported_profile_derived_state_inputs client server /\
        CS.supported_profile_all_derived_key_material_agrees client server /\
        CS.supported_profile_client_server_key_material_inputs_agree client server /\
        paired_driver_transport_logs_exact
          client server client_received client_sent server_received server_sent /\
        CS.paired_wire_logs client server /\
        CS.supported_profile_client_server_key_material_agrees client server)
```

See `src/impl/TLS13.Impl.Driver.Pairing.fsti:999-1031`.

Implementation:

```fstar
let lemma_client_server_driver_end_to_end_key_material_agrees ... =
  lemma_client_server_driver_key_material_agrees_from_public_success_components
    client server client_received client_sent server_received server_sent
```

See `src/impl/TLS13.Impl.Driver.Pairing.fst:1046-1086`. The proof body is
therefore intentionally small; most of the proof is in the helper theorem it
calls and in pure connection-state lemmas.

## Internal events and the settled form of the theorem

The client receive path processes a protected handshake record in two stages:
the record transition installs a pending plaintext, and a sequence of *internal
events* — ordinary `LocalEvent`s classified by `pi_internal`, emitting no wire
output — consume it one handshake message at a time. See `INTERNAL_EVENT_PLAN.md`
for the design and `TLS13.Impl.Client.Drain` for the drain theory.

This does not change the statement above. The pairing argument is over wire
logs, and an internal step by construction appends nothing to them
(`internal_step_output` is `step_output [] []`). What it does change is *when*
the hypotheses hold: immediately after a record is delivered, the client's
semantic state has not yet absorbed the messages that record carried, so
`client_received` and the connection state can disagree until the pending
plaintext is drained.

`TLS13.System.Internal` therefore states the theorem in a **settled** form:

```fstar
val lemma_flagship_settled_record_material_agreement : ...
  (requires ... /\ ~(tls_internal_pending s) /\ ...)
```

`tls_settled` says no internal step is enabled. `lemma_drain_to_settled` shows
every reachable state reaches a settled one by a finite chain of internal steps
that preserves `combined_inv` (via `RTC.stable_on_closure`), so the settled form
is not a weakening in practice — it is a scheduling side condition that the
drivers discharge.

The original `lemma_flagship_record_material_agreement` is retained unchanged
alongside it: adding `~(tls_internal_pending s)` to the antecedent weakens the
lemma, so keeping both costs nothing and preserves every existing caller.

At the C boundary the side condition is observable: `TLS13.Impl.Client.Engine.poll`
returns `EngineReady` only when `~(D.internal_pending st1)`, which is literally
the settled antecedent. A caller that has been told the connection is ready is
entitled to the agreement conclusion.

## Main statement, fully expanded

### Parameters

The theorem relates:

- `client` and `server`: pure `CS.connection_state` snapshots for the two
  endpoints.
- `client_received` and `client_sent`: the external byte histories associated
  with the client driver.
- `server_received` and `server_sent`: the analogous histories for the server
  driver.

The byte-history parameters are not reconstructed by the theorem; they are
explicit evidence supplied by the caller.

### Preconditions

The theorem's single precondition is
`client_server_driver_end_to_end_agreement_inputs`, which is just an alias for
`client_server_driver_key_material_no_read_ahead_component_inputs` in the current
interface (`src/impl/TLS13.Impl.Driver.Pairing.fsti:983-997`).

That component predicate expands as follows
(`src/impl/TLS13.Impl.Driver.Pairing.fsti:532-554`):

| Component | Meaning |
| --- | --- |
| `CD.client_driver_application_ready client` | The client state satisfies the client end-to-end invariant, is in `ControlApplicationData`, has client application record keys installed, and has a stable client X25519 projection (`src/impl/TLS13.Impl.Client.Driver.fsti:62-68`). |
| `SD.server_driver_application_ready server` | The server state satisfies the server end-to-end invariant, is in `ControlApplicationData`, has server application record keys installed, and has a stable server X25519 projection (`src/impl/TLS13.Impl.Server.Driver.fsti:193-199`). |
| `CD.client_driver_sent_log_exact client client_sent` and `SD.server_driver_sent_log_exact server server_sent` | The supplied sent histories are exactly the protocol `raw_sent` logs (`Client.Driver.fsti:71-75`, `Server.Driver.fsti:202-206`). |
| `CD.client_driver_received_log_exact_prefix client client_received` and `SD.server_driver_received_log_exact_prefix server server_received` | The supplied receive histories are the protocol `raw_received` logs followed by some retained suffix (`Client.Driver.fsti:88-94`, `Server.Driver.fsti:219-225`). |
| `CD.client_driver_received_no_read_ahead client client_received` and `SD.server_driver_received_no_read_ahead server server_received` | The supplied receive histories have the same length as the protocol `raw_received` logs, so the retained suffix is empty (`Client.Driver.fsti:97-101`, `Server.Driver.fsti:228-232`). |
| `paired_transport_histories client_received client_sent server_received server_sent` | The environment paired the byte streams: `client_sent == server_received` and `server_sent == client_received` (`Pairing.fsti:33-40`). |
| `client_server_driver_supported_profile_state_inputs client server` | The remaining semantic state assumptions needed for key-material agreement (`Pairing.fsti:482-490`). |

The last row is the important non-transport part. It expands to:

```fstar
client_server_driver_supported_profile_derived_state_inputs client server /\
client_server_driver_supported_profile_application_record_state_inputs client server
```

where:

- `client_server_driver_supported_profile_derived_state_inputs` means
  `CS.paired_x25519_key_shares client server` and
  `CS.paired_key_derivation_checkpoints client server`
  (`Pairing.fsti:251-257`).
- `client_server_driver_supported_profile_application_record_state_inputs` means
  both endpoints' current application traffic material matches the expected
  derived application traffic key/IV material
  (`Pairing.fsti:402-408`,
  `TLS13.Spec.StateMachine.KeyMaterial.peer_record_material_agrees`).

So the theorem assumes, rather than proves from raw bytes, that:

1. The client and server X25519 private/public/key-share facts line up.
2. The two key derivation checkpoints needed for handshake and application
   traffic line up.
3. The currently installed application traffic material on each endpoint is the
   first-epoch material predicted by the key schedule.

### Postcondition

The theorem returns six facts (`Pairing.fsti:1015-1031`):

| Ensured fact | Meaning |
| --- | --- |
| `client_server_driver_supported_profile_derived_state_inputs client server` | Restates the paired X25519/key-derivation-checkpoint inputs as a useful output. |
| `CS.supported_profile_all_derived_key_material_agrees client server` | All supported first-milestone derived key material agrees: early/handshake/master secrets, handshake/application traffic secrets, handshake/application traffic keys and IVs, and client/server Finished keys (`ConnectionState.fst:2175-2207`). |
| `CS.supported_profile_client_server_key_material_inputs_agree client server` | Packages the inputs needed by the aggregate pure key-material agreement lemma: paired X25519 shares, supported-profile key-schedule lineage for both endpoints, paired checkpoints, and application record-material inputs (`ConnectionState.fst:2253-2261`). |
| `paired_driver_transport_logs_exact ...` | Each supplied sent/received byte history exactly equals the corresponding endpoint's protocol log, and the two transport histories are paired (`Pairing.fsti:43-57`). |
| `CS.paired_wire_logs client server` | The protocol logs themselves are paired: client's raw sent log equals server's raw received log, and vice versa (`ConnectionState.fst:488-493`). |
| `CS.supported_profile_client_server_key_material_agrees client server` | The aggregate final agreement fact: all supported derived key material agrees and the current application record material agrees (`ConnectionState.fst:2263-2268`). |

`CS.supported_profile_client_server_key_material_agrees` is application-record
focused: it includes `supported_profile_application_record_material_agrees`, not
`supported_profile_all_record_material_agrees`. The all-derived part still covers
handshake traffic keys/IVs historically, but the current record-layer agreement
conclusion is about the application epoch (`ConnectionState.fst:2231-2251`,
`2263-2268`).

## Stronger validation theorem we actually want

The current theorem is a bridge from already-packaged semantic pairing facts to
key-material agreement. The stronger state-machine validation goal is to prove
that those semantic facts follow from paired client/server executions.

A precise first target is a paired event-trace theorem:

```text
Given a legal client event trace and a legal server event trace, if:
  * the client reaches application-data state;
  * the server reaches application-data state;
  * the handshake messages/events in the two traces are paired
    (client-sent messages are server-received messages and vice versa);
  * the run is in the supported profile and no-KeyUpdate/first-epoch slice;
then:
  * the client write application record key/IV equals the server read key/IV;
  * the server write application record key/IV equals the client read key/IV.
```

In terms of current predicates, the conclusion is already represented by:

```fstar
CS.supported_profile_application_record_material_agrees client server
```

which contains:

```fstar
CS.peer_record_material_agrees
  (CS.traffic_id CS.TrafficApplication CS.ClientTraffic) client server

CS.peer_record_material_agrees
  (CS.traffic_id CS.TrafficApplication CS.ServerTraffic) client server
```

Those are the two directions of the desired `k` agreement: client-write/server-read
and server-write/client-read. It is better to state this over record key/IV
material rather than only over a key byte string, because the TLS record layer
uses both the AEAD key and static IV.

There is also a byte-trace version:

```text
If the final client/server states have paired raw byte logs
  client.raw_sent     == server.raw_received
  server.raw_sent     == client.raw_received
and the endpoint replay invariants connect those raw logs to parsed TLS events,
then the event-trace theorem applies and gives application record key/IV
agreement.
```

The cleanest verified normalized bridge now lives in
`TLS13.Impl.Driver.PairingNormalizedShape`.  Its key predicate,
`paired_successful_handshake_normalized_replay_shape client server`, deliberately
does **not** require exact `ClientHello` or `ServerHello` record equality across
the two endpoints.  Instead, it keeps separate values for:

- the locally generated client `ClientHello` and the parser-produced server
  `ClientHello`;
- the locally generated server `ServerHello` and the parser-produced client
  `ServerHello`;
- the corresponding raw cleartext fragments.

It then relates those values by paired raw bytes, cleartext raw legality,
supported ServerHello parsing, and the protected event-projection witness package.
From that normalized/raw-backed shape, the proof calls
`Pairing.lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projection_witnesses`,
which derives normalized hello wire equivalence, protected serialized-handshake
equivalence, paired handshake events, and finally application record key/IV
agreement.  The normalized bridge theorem is:

```fstar
val lemma_client_server_application_record_material_agrees_from_normalized_replay_shape
  (client server:CS.connection_state)
  : Lemma
      (requires
        paired_successful_handshake_normalized_replay_shape client server)
      (ensures
        WFL.paired_cleartext_hello_wire_equivalent client server /\
        WFL.paired_cleartext_hello_key_shares client server /\
        WFL.paired_protected_handshake_wire_equivalent client server /\
        Pairing.paired_handshake_events client server /\
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic) client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic) client server)
```

There are two no-tail valid-byte-trace wrappers:

- `PairingNormalizedShape.lemma_client_server_application_record_material_agrees_from_no_tail_valid_byte_traces_with_normalized_replay_shape`
  includes valid client/server `WFSM.valid_byte_trace` facts, paired byte streams,
  and the no-tail application-ready boundary, but still assumes the compact
  normalized replay shape above.
- `PairingNoTail.lemma_client_server_application_record_material_agrees_from_no_tail_valid_byte_traces`
  has the desired theorem name and conclusion.  Its predicate
  `paired_supported_no_tail_valid_byte_traces` **no longer** includes
  `PairingNormalizedBoundary.paired_supported_normalized_replay_boundary` (the
  ~30-step `CS.step_model` witness described above), but that is not the clean
  win it looks like: it now includes
  `PairingTraceShape.paired_successful_handshake_complete_event_log_shape`
  instead, i.e. exactly the "older `TLS13.Impl.Driver.PairingTraceShape`
  theorem" exact-record-equality hypothesis discussed just below, with the same
  `body`-field defect (see that discussion, and the status note on
  `paired_supported_no_tail_valid_byte_traces` in
  `TLS13.Impl.Driver.PairingNoTail.fsti`).  So this is a swap of one
  not-yet-derived heavy hypothesis for a different, differently-shaped,
  not-yet-derived (and likely unsatisfiable-as-written for parser-produced
  traces) heavy hypothesis, not a removal of one.  It should be read the same
  way as the `PairingTraceShape` byte-trace wrapper below: a type-checked
  internal milestone, not a "key material agreement from valid byte traces
  alone" result.

The missing audit-surface bridge is therefore still open in both directions:
neither the normalized replay boundary/shape nor the exact trace-shape
predicate has been derived from no-tail valid byte traces plus the light
per-endpoint state facts (`paired_no_tail_application_ready_boundary` and
`Pairing.client_server_driver_first_epoch_no_key_update_state_inputs`) alone.

Several important pieces of that bridge are now verified:
`TLS13.Impl.Driver.PairingNoTailWireLogs` proves that canonical
`WFSM.valid_byte_trace` input/output bytes are exactly the final
`cs_wire_log.raw_received/raw_sent` logs, for traces that start from
`CS.initial`.  `TLS13.Impl.Driver.PairingNoTailNormalized` uses this to derive
`CS.paired_wire_logs client server` from the clean paired byte-stream premises.
So raw transport pairing no longer has to be an exposed top-level assumption.
The raw cleartext hello bridge is also now verified:
`TLS13.Impl.Driver.PairingNoTailRawBridge` derives the paired raw ClientHello and
ServerHello record slices from role-local prefixes, replay consistency, supported
ClientHello wire profile, and `CS.paired_wire_logs`, while keeping generated and
parser-produced hello records distinct.  It also now exposes record-head
disjointness lemmas showing that a supported ClientHello raw record, a received
ServerHello raw record, or a single protected `ApplicationData` raw record cannot
be the same stream head as a cleartext ChangeCipherSpec.  These are used by
`PairingNoTailNormalized` to derive the corrected clean16 server second-event
fact under paired byte traces: the server's post-start event is not an unmatched
CCS, and therefore the length-16 server trace begins by receiving the client's
ClientHello.  Separately,
`TLS13.Impl.Driver.PairingNoTailClientSentRawShape` proves that the completed
client no-tail raw-sent stream is exactly a cleartext ClientHello followed by the
single protected `ApplicationData` record carrying Client Finished.  The new
`TLS13.Impl.Driver.PairingNoTailClientReceivedRawShape` proves the dual
client-received raw shape for the completed client no-tail log: a cleartext
ServerHello followed by four protected `ApplicationData` records for
EncryptedExtensions, Certificate, CertificateVerify, and Server Finished.  This
is an important byte-level segmentation milestone, but it is deliberately weaker
than the staged replay boundary: it counts and slices protected records in the
client's `raw_received` log; it does not yet prove the matching server
`sent_seal_replay` events or the client's `received_decode_replay` witnesses.  The
next paired cleartext milestone is now also verified:
`TLS13.Impl.Driver.PairingNoTailServerCleartextShape` proves a length-16 server
third-event inversion lemma under a non-CCS premise, and
`PairingNoTailNormalized` derives that premise from paired bytes.  The derivation
uses the explicit client `ClientHello ++ ClientFinished` raw-sent slice to rule
out a server-received CCS immediately after ClientHello, and the client
received-ServerHello raw head to rule out a server-sent CCS at that same point.
Consequently, clean16 paired byte traces now imply the server prefix
`LocalStartServer; Received ClientHello; LocalSelectServerParameters`, paired
with the client prefix through `LocalDeriveSharedSecret`.  The
remaining hard part is the rest of the role-local event-shape and protected
projection inversion.  The role-local inversion is now past the first
nontrivial CCS/no-op cases:
`PairingNoTailInversion` proves that a no-tail length-16 client log begins
`LocalStartHandshake; Sent ClientHello; Received ServerHello;
LocalDeriveSharedSecret` and that the following client event is some handshake
traffic-key install, and `PairingNoTailServerShape` proves that a no-tail
server log under the earlier length-15 milestone begins
`LocalStartServer; Received ClientHello; LocalSelectServerParameters;
LocalDeriveSharedSecret; Sent ServerHello`.  That server length-15 milestone is
now known to be stale for the final theorem: the satisfiable no-tail server
boundary must include the server's client-handshake read-key install before
receiving ClientFinished.  The current final target is a length-16 clean
predicate that either derives the relevant no-CCS/canonical scheduling facts
from paired bytes, or assumes them explicitly, then proves the
order-insensitive server handshake installs and protected-flight segmentation.
`PairingNoTailNormalized` packages these into derived paired milestones from the
clean paired no-tail valid-byte-trace predicate.

The client install-order proof exposed a real audit distinction.  The exact
write-before-read order used by `client_no_tail_normalized_shape` is not a
consequence of the abstract `WFSM.valid_byte_trace (ClientCP.client_system ...)`
predicate alone: `client_step` accepts any legal local API event, while the
concrete `TLS13.Impl.Client.next_local_action` priority is outside that predicate.
Consequently, the clean theorem should not rely on proving that exact order from
bare byte traces.  The protected projection/replay bridge either has to be
insensitive to the commuting client handshake write/read installs, or the public
trace predicate must be strengthened to include canonical local scheduling.  The
audit-preferred route is the former.

This is not just a presentation issue.  The current normalized/protected backend
still contains a pre-install alignment premise of the form
`PWL.write_read_record_material_aligned client_model4 server_model5`.  At those
cleartext-prefix models neither endpoint has installed the relevant handshake
traffic record keys, so the premise requires `record_direction_material` to be
`Some` where it is still `None`.  A corrected backend should derive alignment
after the explicit server-handshake-write/client-handshake-read and
client-handshake-write/server-handshake-read installs, then produce
`paired_protected_handshake_event_projection_pair_witnesses` directly instead of
routing through the stale contiguous replay view.

One intermediate backend milestone is verified:
`TLS13.ConnectionState.ProtectedWireStaged.lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_replays_v2`
constructs the five protected projection pairs without any pre-install
client-write/server-read alignment premise.  It still requires caller-supplied
staged replay facts: the server encrypted flight starts from explicit
server-handshake-write/client-handshake-read installs, and the ClientFinished
pair starts from explicit client-handshake-write/server-handshake-read installs
whose record key/IV material agrees.  This was a useful way to remove the stale
pre-install alignment assumption, but it is **not** the final clean16 target: in
the real state machine those ClientFinished-side handshake installs cannot be
delayed until immediately before ClientFinished.  The client handshake write key
and server handshake read key are legal only before the server encrypted flight.
The corrected final bridge must therefore construct protected projection
witnesses directly from the real post-server-flight states, where those
handshake directions are already installed.
The server-flight side has also been made less scheduler-sensitive:
`TLS13.ConnectionState.ProtectedWireServerFlight` now has two verified
one-local-commute helpers for the first protected server-flight record.  They
cover both client post-shared orders:

```text
server write install; client read install; client local read-preserving event; receive record
server write install; client local read-preserving event; client read install; receive record
```

The intended `receiver_skip` is the commuting client-handshake write install,
whose event preserves the client's record-read state.  These helpers are not yet
the full staged replay inversion theorem: they prove the one-record projection
pair and preserve replay tails once the relevant suffixes and handshake
server/client traffic materials are supplied, but they do not by themselves
extract those suffixes from `paired_supported_no_tail_valid_byte_traces_clean16`.
The clean16 raw-slice lemmas now supply both paired protected byte segmentations:
the client-received stream is `ServerHello` followed by four protected
`ApplicationData` records for the server flight, the server-sent stream has the
same shape, and the server-received stream is `ClientHello` followed by one
protected `ApplicationData` record for ClientFinished.  A separate
`PairingNoTailServerPostHelloShape` milestone proves that the corrected
length-16 server trace splits after the cleartext `ServerHello` prefix into two
named post-ServerHello slots plus a nine-event residual suffix.  These facts
narrow the remaining inversion problem: lift the raw-record slices and
post-cleartext log split to the paired `sent_seal_replay` and
`received_decode_replay` staged suffixes required by
`paired_supported_normalized_staged_replay_boundary`.
The schedule-insensitive proof target is now explicit in
`TLS13.Impl.Driver.PairingStagedNormalizedBoundary`:
`paired_supported_normalized_projection_boundary_inputs` packages normalized
cleartext/raw agreement plus
`Pairing.paired_protected_handshake_event_projection_pair_witnesses`, and
`lemma_client_server_application_record_material_agrees_from_normalized_projection_boundary`
routes directly through
`Pairing.lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projection_witnesses`.
`TLS13.Impl.Driver.PairingNoTailStagedBoundaryDerivation` mirrors this with
`clean16_projection_boundary_completion` and
`lemma_client_server_application_record_material_agrees_from_clean16_no_tail_valid_byte_traces_and_projection_boundary_completion`.
That is the current audit-facing remaining obligation: derive the protected
projection witnesses from clean16 paired byte traces, not satisfy the staged-v2
delayed-install premises.
The client side now also exposes a model-source fact at the natural
ClientFinished boundary:
`PairingNoTailClientFinishedShape.lemma_client_after_server_finished_model_facts`
unpacks the model immediately after receiving the server Finished, showing that
both handshake traffic directions are installed and application traffic is still
absent.  This is the right audit point for proving the final protected
ClientFinished send/receive slice.
The older staged-v2 wrapper remains in the tree as a checked compatibility
milestone, but the clean theorem should now flow through the projection boundary.
This keeps the public audit surface independent of local scheduling choices for
the commuting handshake installs.

Current WIP status: the tree verifies with `make -j128`, but this checkpoint
intentionally contains narrowly scoped proof admits.  In
`TLS13.Wire.Spec.Reveal.ServerHello.Parseback`, the admits are limited to
ServerHello parser/serializer byte-shape equalities (LowParse generated
serialization versus the hand-written `TLS13.Wire.Spec` serializer).  In
`PairingNoTailProtectedProjectionDerivation`, one admit is limited to unpacking
the large installed protected-projection witness package and passing its named
witnesses to the already-verified input-level projection constructor.  These
admits should be removed before treating the final byte-trace theorem as fully
audited; they do not introduce new intended cryptographic assumptions, but they
are part of the current trusted proof surface.

The older `TLS13.Impl.Driver.PairingTraceShape` theorem is still verified, but it
is not the right final target for parser-backed traces.  It avoids the
protected-replay backend and goes through
`Pairing.paired_handshake_event_trace`, but its shape predicate names the
ClientHello and ServerHello once and requires both endpoints' final handshake
state slots and event logs to contain those exact same records.  That is too
strong for real byte traces, because locally generated hellos have `body = empty`
while received/parser-produced hellos retain the full handshake wire bytes in
`body`.  Its theorem is:

```fstar
val lemma_client_server_application_record_material_agrees_from_successful_handshake_complete_state_trace
  (client server:CS.connection_state)
  : Lemma
      (requires paired_successful_handshake_complete_state_trace client server)
      (ensures
        CS.supported_profile_client_server_key_material_agrees client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ClientTraffic) client server /\
        CS.peer_record_material_agrees
          (CS.traffic_id CS.TrafficApplication CS.ServerTraffic) client server)
```

There is also a byte-trace wrapper,
`lemma_client_server_application_record_material_agrees_from_valid_paired_byte_traces_with_successful_handshake_complete_state_trace`,
whose precondition adds client/server `WFSM.valid_byte_trace` facts and paired
sent/received byte streams.  Because its trace-shape predicate uses exact hello
record equality, it should be read as a useful internal milestone and a warning
about representation sensitivity, not as the final audit surface.

The newest no-tail wrapper layer is `TLS13.Impl.Driver.PairingNoTail`.  It
separates the first-application-ready boundary fact from the concrete successful
event-log shape:

- `client_no_tail_application_ready_boundary client` is client application-ready
  plus final client event-log length `16`;
- `server_no_tail_application_ready_boundary server` was previously written as
  server application-ready plus final server event-log length `15`, but this is
  missing the server handshake read-key install needed before the protected
  ClientFinished receive.  The satisfiable no-tail target is therefore server
  length `16`;
- `lemma_paired_successful_handshake_complete_state_trace_no_tail` proves that
  the existing successful trace-shape predicate implies those no-tail lengths and
  no-KeyUpdate traces;
- `lemma_client_server_application_record_material_agrees_from_valid_byte_traces_at_no_tail_boundary_with_successful_event_log_shape`
  gives the current no-tail byte-trace wrapper.

This is useful, but it is not yet the fully desired inversion theorem; the
checked length-`15` server wrappers should now be treated as stale until they are
updated to include the handshake read install.  The
remaining bridge should go to the normalized replay shape, not to the exact
`paired_successful_handshake_complete_event_log_shape`:

```text
paired no-tail valid byte traces
  ==> normalized cleartext ClientHello/ServerHello replay facts
  ==> five protected event-projection pairs
  ==> paired_successful_handshake_normalized_replay_shape
  ==> application record key/IV agreement
```

The old `15`-event client shape had to be treated skeptically.  The
abstract legality condition for sending the client Finished requires
`ks_client_handshake_traffic` as well as both application traffic secrets
(`TLS13.Spec.StateMachine.legal_handshake_message`, the
`CL.Sent, M.Finished, HsServerFinishedVerified` case).  The legacy
client suffix installs the server handshake read traffic keys but does not
include a separate client handshake write-key install before sending Finished.
The no-tail exact-shape target has therefore been corrected to include that
same-stage handshake write install, giving a 16-event client no-tail boundary.

The lower-level byte/replay proof stack remains useful for deriving trace-shape
facts from raw bytes.  Its currently verified replay progress starts with
cleartext-handshake facts.  `TLS13.Spec.WireFormatLemmas` now exposes lemmas
that derive:

- ClientHello serialized-handshake equality from raw cleartext replay and
  supported-profile ClientHello parsing;
- ServerHello key-share equality when both equal ServerHello fragments are
  accepted by `W.parse_supported_server_hello`;
- `TH_CH`, `TH_SH`, and `DeriveHandshakeTraffic` checkpoint agreement from
  cleartext raw replay;
- `paired_protected_handshake_wire_equivalent`, a deliberately weaker predicate
  than exact structured equality for the encrypted handshake flight, together
  with
  `lemma_paired_handshake_events_from_cleartext_raw_and_protected_wire`, which
  proves all `CS.paired_handshake_events` checkpoints from cleartext raw replay
  plus protected-handshake serialized-byte equality;
- `TLS13.ConnectionState.ProtectedWireProjection.lemma_protected_handshake_wire_equal_from_sent_seal_peer`,
  which proves a single protected handshake message's serialized-byte equality
  from sender seal replay, receiver decode replay, peer key/IV agreement, and
  aligned record sequence numbers.  The follow-up
  `lemma_protected_handshake_wire_equal_from_event_projections_peer` lifts this
  to the event-projection predicates used by the replay invariants.  A small
  negative helper,
  `lemma_protected_finished_not_certificate_verify_from_event_projections_peer`,
  now makes explicit one crucial disjointness fact needed by the protected-byte
  inversion: under equal ciphertext, aligned peer record state, and seal/decode
  projections, a server `Finished` cannot be the record decoded by the client as
  `CertificateVerify`.  This supports the protected-byte inversion by ensuring
  that CertificateVerify and Finished records cannot be conflated once the
  corresponding raw segments are isolated.  The
  packaged theorem
  `lemma_paired_protected_handshake_wire_equivalent_from_event_projection_pairs`
  applies that bridge to the five encrypted handshake records and derives the
  `paired_protected_handshake_wire_equivalent` predicate consumed by the
  transcript-checkpoint theorem.  Finished
  needed an extra reveal-layer parseback lemma,
  `TLS13.Wire.Spec.Reveal.FinishedRoundTrip.lemma_parse_finished_handshake_round_trip`,
  because the generic `Wire.Spec` parser round-trip lemma intentionally covers
  only wire-body-carrying handshake messages.

`TLS13.Impl.Driver.Pairing` then uses these facts in
`lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_handshake_events`:
from cleartext ClientHello/ServerHello raw replay, explicit supported
ServerHello parse assumptions, paired encrypted-handshake events, and the usual
first-epoch/no-key-update state invariant, it proves both application record
material directions.  The encrypted-handshake side no longer needs exact
`M.encrypted_extensions`, `M.certificate_msg`, or `M.certificate_verify` record
equality; serialized handshake equality is enough for the transcript.  The
new
`lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projections`
goes one step further: it replaces the assumed `paired_handshake_events` premise
with the five protected event-projection pairs, derives
`paired_protected_handshake_wire_equivalent`, derives `paired_handshake_events`,
and then proves both application record-material directions.  The remaining
byte-trace lift is therefore focused on extracting those five protected
event-projection-pair witnesses from the recursive raw/seal/decode replay
invariants.

The most ambitious client-only existential statement:

```text
if the client reaches an application key k, then there exists a server run over
the opposite bytes that reaches the same k
```

is not the best first theorem. A server run needs local witnesses that are not
recoverable from the client bytes alone: server private X25519 key, server
credential/configuration, server randomness, signing result, and validation of
local choices. The robust theorem should therefore quantify over or assume a
legal paired server run, then prove the key-agreement consequence. An existential
server-run theorem can be a later corollary once the required local witnesses are
made explicit.

## Underlying assumptions and trusted boundaries

### Driver and state-machine assumptions

`client_driver_application_ready` and `server_driver_application_ready` are
strong predicates. They include the client/server end-to-end invariants, control
state `ControlApplicationData`, installed application record keys, and stable
X25519 projections (`Client.Driver.fsti:62-68`, `Server.Driver.fsti:193-199`).

The client end-to-end invariant includes connection-state consistency, full log
consistency, sent-seal replay consistency, received-decode replay consistency,
and raw-to-message replay consistency
(`src/impl/TLS13.Impl.Client.Types.fst:35-53`). The server analogue includes
server state correctness plus raw-to-message replay consistency
(`src/impl/TLS13.Impl.Server.Types.fst:641-645`). At the pure level,
`CS.connection_state_consistent st` means `st` is reachable from
`CS.initial st.cs_model.model_config` by the reflexive-transitive closure of
legal connection deltas (`ConnectionState.fst:3759-3767`).

A legal connection delta requires a legal event, a successful `step_model`,
legal raw sent/received deltas, exact append updates to the raw wire log, and
exact event-log extension (`ConnectionState.fst:3490-3507`). The key-schedule
state machine itself is deterministic: deriving a shared secret installs
`early`, `handshake`, and `master` secrets from the shared secret
(`ConnectionState.fst:1276-1294`), and traffic-key installation is required to
match the expected traffic secret for the relevant epoch/direction
(`ConnectionState.fst:1899-1920`).

These reachability facts are used indirectly to obtain supported-profile
key-schedule lineage. In particular,
`lemma_connection_application_keys_supported_profile_key_schedule_lineage`
requires `connection_state_consistent st` and installed application record keys,
then proves `connection_supported_profile_key_schedule_lineage st`
(`ConnectionState.Lemmas.fsti:95-102`,
`ConnectionState.Lemmas.fst:1176-1189`).

### Transport assumptions

The theorem assumes `paired_transport_histories`: the external environment
delivered exactly each side's sent byte stream to the other side
(`Pairing.fsti:33-40`). It also assumes exact sent logs, received-prefix logs,
and no read-ahead. The proof upgrades prefix-plus-equal-length to exact equality
via `lemma_endpoint_transport_received_exact_from_prefix_no_read_ahead`, then
uses that to prove `paired_driver_transport_logs_exact` and `CS.paired_wire_logs`
(`Pairing.fst:98-176`, `614-648`).

This is a reliable/in-order byte-history assumption. The theorem does not prove
that a TCP channel, scheduler, or adversarial network produced those histories.

### Semantic pairing assumptions

The theorem assumes `client_server_driver_supported_profile_state_inputs`.
The most security-significant part is `CS.paired_x25519_key_shares`. That
predicate requires the client and server states to contain:

- the client's private key and advertised public key;
- the server's private key and advertised public key;
- the ClientHello and ServerHello key shares;
- each endpoint's computed shared secret;
- equations connecting each private key to its public key and each endpoint's
  X25519 computation to its stored shared secret.

See `ConnectionState.fst:545-572`. The theorem does not itself derive this
predicate from the wire logs.

The theorem also assumes `CS.paired_key_derivation_checkpoints`, i.e. equality of
the `DeriveHandshakeTraffic` and `DeriveApplicationTraffic` checkpoints
(`ConnectionState.fst:506-511`). These are the transcript-derived checkpoints
used by the traffic secret computations.

Finally, it assumes that each endpoint's current application traffic material
matches the expected derived material (`Pairing.fsti:402-408`,
`ConnectionState.fst:2066-2090`). This is the state-machine bridge from the
historical key schedule to the current record-layer slots.

### Cryptographic assumptions

The cryptographic API is specified in `TLS13.Crypto.Spec.fsti`; there is no
corresponding `TLS13.Crypto.Spec.fst` implementation in `src/spec`. The theorem
therefore treats the following as the cryptographic specification/TCB boundary:

- `sha256`, `hmac_sha256`, `hkdf_extract`, `hkdf_expand_label`;
- `x25519_public_from_private` and `x25519_shared`;
- `lemma_x25519_shared_agreement`;
- AEAD seal/open and signature verification functions.

See `src/spec/assumptions/TLS13.Crypto.Spec.fsti:18-77`.

For this theorem, the crucial crypto assumption is
`lemma_x25519_shared_agreement`:

```fstar
x25519_public_from_private client_sk == client_pub /\
x25519_public_from_private server_sk == server_pub
==>
x25519_shared client_sk server_pub ==
x25519_shared server_sk client_pub
```

See `TLS13.Crypto.Spec.fsti:40-51`. The proof uses it in
`lemma_paired_x25519_key_shares_shared_secret_agree`
(`ConnectionState.Lemmas.fst:3084-3121`).

For protected-byte trace lifting, `TLS13.Crypto.Spec.fsti` now explicitly adds
the following trusted AEAD decrypt-after-encrypt correctness assumption:

```fstar
chacha20_poly1305_open key nonce aad
  (chacha20_poly1305_seal key nonce aad plaintext)
== Some plaintext
```

The record spec defines sealing and opening in terms of these abstract crypto
functions (`TLS13.Record.Spec.fst:35-59`). This assumption is intentionally part
of the cryptographic TCB: it is not a theorem about the implementation. With it,
`TLS13.Record.Spec.lemma_open_record_after_seal` and
`lemma_open_record_after_seal_peer` prove that a receiver with matching key/IV
material and sequence number opens the sender's sealed record to the sender's
plaintext. `TLS13.ConnectionState.Lemmas` exposes the corresponding
`received_single_protected_message_decode_from_sent_single_protected_message_seal`
bridge, and `TLS13.Impl.Driver.Pairing` exposes client-to-server and
server-to-client wrappers from `CS.peer_record_material_agrees`.

The theorem proves equality of specified byte strings. It does not prove
computational secrecy, resistance to active attacks, AEAD authenticity, signature
unforgeability, side-channel freedom, or that the cryptographic implementations
meet these specs.

The implementation-facing crypto interface promises that concrete operations
write the corresponding `TLS13.Crypto.Spec` results into buffers, but some
security properties remain outside the postconditions. For example,
`random_bytes` only proves ownership and output length, not entropy, while the
runtime X25519 path is connected to `C.x25519_shared` through
`x25519_shared_call` and `lemma_x25519_shared_call_success`
(`src/impl/extern/TLS13.Crypto.fsti:16-20`, `119-173`). The default client/server
configuration fixes the implementation profile to
`TLS_CHACHA20_POLY1305_SHA256`, `RsaPssRsaeSha256`, and server group `X25519`
(`src/impl/TLS13.Impl.ConnectionState.Repr.fsti:1183-1247`).

### Key-schedule assumptions

The supported-profile key-schedule lineage is the pure TLS 1.3 key derivation
chain for this profile:

```fstar
early     = K.early_secret B.empty
handshake = K.handshake_secret early shared
master    = K.master_secret handshake
```

See `ConnectionState.fst:525-538`. `TLS13.Keys.fst` defines these functions in
terms of HKDF extract/expand-label over SHA-256 labels
(`TLS13.Keys.fst:73-118`, `120-130`). In particular, the early secret is derived
from an empty PSK input (`K.early_secret B.empty`), so PSK/0-RTT/resumption are
outside this theorem's supported-profile derivation chain.

`supported_profile_all_derived_key_material_agrees` only covers
`first_milestone_derived_key_id`s. `TrafficUpdateSecret`, `ExporterMasterSecret`,
and `ResumptionMasterSecret` are explicitly outside that set
(`ConnectionState.fst:1954-1968`, `2175-2207`).

### Wire-format assumptions

The main theorem does not call the wire-format lemmas directly. It starts from
semantic state inputs such as `paired_x25519_key_shares` and paired derivation
checkpoints. If a caller wants to derive those facts from raw replay and parsed
messages, the relevant boundary is `TLS13.Spec.WireFormatLemmas`.

That module records important supported-profile wire constraints:

- ClientHello wire support is the singleton supported cipher suite
  `TLS_CHACHA20_POLY1305_SHA256` and signature scheme `RsaPssRsaeSha256`, with
  bounded server name and empty body (`WireFormatLemmas.fsti:21-60`).
- ClientHello equality from raw bytes is weakened around absent versus empty SNI
  (`WireFormatLemmas.fsti:63-79`).
- The module explicitly warns that ServerHello raw replay does not by itself
  imply equality of all `M.server_hello` fields because received ServerHello
  values may carry raw `body` bytes while sent values use canonical fields
  (`WireFormatLemmas.fsti:81-100`).

This matters skeptically: the pairing theorem avoids these wire-format subtleties
by assuming semantic pairing facts directly.

## Guide to reading the proof

Read the proof from the bottom up: the top-level proof is only a wrapper, and the
substantive reasoning lives in helper lemmas.

### 1. Top-level theorem: a one-call wrapper

`lemma_client_server_driver_end_to_end_key_material_agrees` calls
`lemma_client_server_driver_key_material_agrees_from_public_success_components`
directly (`Pairing.fst:1046-1086`).

The called lemma has the same component precondition and proves:

- all supported-profile derived key material agrees;
- aggregate key-material inputs agree;
- exact paired transport logs;
- `CS.paired_wire_logs`;
- final aggregate key-material agreement.

See `Pairing.fsti:719-748` and implementation `Pairing.fst:691-731`.

### 2. Component theorem: split into semantic and transport subproofs

`lemma_client_server_driver_key_material_agrees_from_public_success_components`
does two things (`Pairing.fst:691-731`):

1. Calls `lemma_client_server_driver_supported_profile_derived_key_material_agrees`
   to get key-schedule lineage for both endpoints and
   `CS.supported_profile_all_derived_key_material_agrees`.
2. Calls
   `lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components`
   to obtain the aggregate input predicate, exact paired logs, paired wire logs,
   and final aggregate agreement.

`lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components`
first packages semantic key-material inputs by calling
`lemma_client_server_driver_supported_profile_key_material_inputs_agree`, then
uses `lemma_client_server_driver_key_material_agrees_from_no_read_ahead` for the
transport exactness and aggregate pure key-material theorem
(`Pairing.fst:650-690`).

### 3. Transport exactness: prefix plus no-read-ahead

The transport subproof is:

1. `lemma_endpoint_transport_received_exact_from_prefix_no_read_ahead`:
   an exact-prefix witness plus equal length implies the retained suffix is
   empty, so the external receive history equals `raw_received`
   (`Pairing.fst:98-129`).
2. `lemma_paired_wire_logs_from_exact_prefix_no_read_ahead`:
   apply the previous lemma to both endpoints, combine exact sent logs and
   `paired_transport_histories`, and conclude both `paired_driver_transport_logs_exact`
   and `CS.paired_wire_logs` (`Pairing.fst:130-176`).
3. `lemma_client_server_driver_key_material_agrees_from_no_read_ahead`:
   call the wire-log lemma and the pure aggregate key-material lemma
   (`Pairing.fst:614-648`).

The proof here is about byte-history accounting. It does not inspect TLS
handshake messages.

### 4. Deriving supported-profile key-schedule lineage

`lemma_client_server_driver_supported_profile_derived_key_material_agrees`
starts from application-ready states and
`client_server_driver_supported_profile_derived_state_inputs`:

```fstar
CS.paired_x25519_key_shares client server /\
CS.paired_key_derivation_checkpoints client server
```

It uses application readiness to assert each endpoint is consistent, has the
right role, and has application record keys installed. Then it calls
`CSL.lemma_connection_application_keys_supported_profile_key_schedule_lineage`
for the client and server. Finally it calls
`CSL.lemma_paired_supported_profile_all_derived_key_material_agrees`
(`Pairing.fst:389-420`).

The lineage lemma itself is a reachability invariant: from
`connection_state_consistent` and installed application record keys it obtains
the supported-profile base-secret chain (`ConnectionState.Lemmas.fst:713-803`,
`1126-1189`).

### 5. Bootstrapping derived-key agreement

The pure derived-key proof is the heart of the theorem family.

1. `lemma_paired_x25519_key_shares_shared_secret_agree` unfolds
   `paired_x25519_key_shares`, uses
   `C.lemma_x25519_shared_agreement`, and proves the stored client/server shared
   secrets are equal (`ConnectionState.Lemmas.fst:3084-3121`).
2. `lemma_shared_secret_lineage_base_secret_agree` combines equal shared secrets
   with supported-profile key-schedule lineage:
   - early secrets agree because both are `K.early_secret B.empty`;
   - handshake secrets agree because both are `K.handshake_secret early shared`;
   - master secrets agree because both are `K.master_secret handshake`.
   See `ConnectionState.Lemmas.fst:3124-3175`.
3. `lemma_paired_x25519_key_shares_base_secret_agree` packages the previous two
   steps for any base secret (`ConnectionState.Lemmas.fst:3176-3188`).
4. For traffic secrets, keys, IVs, and Finished keys,
   `lemma_paired_x25519_key_shares_derived_key_agrees` first proves the relevant
   base secret agrees, then uses `derivation_checkpoint_inputs_agree` to obtain
   the required transcript/key checkpoint agreement, then calls
   `lemma_paired_endpoints_derived_key_agrees`
   (`ConnectionState.Lemmas.fst:3190-3228`).
5. `lemma_expected_traffic_secret_for_state_agrees` is the deterministic
   traffic-secret step: equal base secret plus equal transcript checkpoint bytes
   means the expected traffic secret is equal
   (`ConnectionState.Lemmas.fst:2992-3025`).
6. `lemma_paired_endpoints_derived_key_agrees` lifts traffic-secret equality to
   traffic key, traffic IV, and Finished key equality by unfolding
   `expected_derived_key_material` and using deterministic key derivation
   (`ConnectionState.Lemmas.fst:3027-3082`,
   `ConnectionState.fst:2033-2065`).
7. `lemma_paired_supported_profile_all_derived_key_material_agrees` enumerates
   the supported first-milestone keys and invokes
   `lemma_paired_x25519_key_shares_derived_key_agrees` for each one
   (`ConnectionState.Lemmas.fst:3265-3312`).

This is the inductive bootstrapping pattern: X25519 agreement gives shared-secret
agreement; lineage turns that into base-secret agreement; transcript-checkpoint
agreement turns base-secret agreement into traffic-secret agreement; and
deterministic key expansion turns traffic-secret agreement into key/IV/Finished
agreement. The code implements the induction mostly by case analysis and explicit
enumeration rather than by a generic recursive proof over the key graph.

### 6. Bootstrapping current record-key agreement

The final aggregate theorem also needs the current record-layer material to
agree. The bridge is:

1. `supported_profile_application_traffic_material_matches_expected` states that
   each endpoint's stored client/server application traffic material has key/IV
   fields equal to `expected_derived_key_material (TrafficKey ...)` and
   `expected_derived_key_material (TrafficIV ...)`
   (`ConnectionState.fst:2066-2090`).
2. `lemma_supported_profile_application_record_material_inputs_agree_from_expected`
   uses the already-proved application `TrafficKey` and `TrafficIV` agreement,
   plus each endpoint's material-matches-expected facts and installed application
   record epochs, to prove
   `supported_profile_application_record_material_inputs_agree`
   (`ConnectionState.Lemmas.fst:3566-3624`).
3. `lemma_paired_supported_profile_application_record_material_agrees` converts
   those inputs into actual current read/write record key/IV equality for
   application traffic (`ConnectionState.Lemmas.fst:3552-3564`).
4. `lemma_supported_profile_client_server_key_material_agrees` combines all
   derived-key agreement and application-record agreement into the aggregate
   `CS.supported_profile_client_server_key_material_agrees`
   (`ConnectionState.Lemmas.fst:3649-3659`).

At the driver-pair level,
`lemma_client_server_driver_supported_profile_key_material_inputs_agree` performs
this packaging after obtaining derived-key agreement and application record epoch
facts (`Pairing.fst:570-612`).

## Detailed plan to reach the stronger theorem

### Phase 1: expose direct application key/IV projections

Add small projection predicates/lemmas, probably in
`TLS13.Impl.Driver.Pairing`, that turn the aggregate conclusion into the two
directional statements reviewers want to read:

```fstar
CS.peer_record_material_agrees
  (CS.traffic_id CS.TrafficApplication CS.ClientTraffic) client server

CS.peer_record_material_agrees
  (CS.traffic_id CS.TrafficApplication CS.ServerTraffic) client server
```

This phase should be easy: it only destructs
`CS.supported_profile_client_server_key_material_agrees` and
`CS.supported_profile_application_record_material_agrees`. It gives named lemmas
for "client's application write key/IV equals server's application read key/IV"
and the dual server-write/client-read theorem.

### Phase 2: prove a state/event-level theorem over paired handshake facts

Add a theorem whose precondition is closer to state-machine validation and does
not mention transport bytes:

```text
client/server application-ready states
+ paired handshake message states, or equivalently:
    paired cleartext Hello messages
    paired handshake events / checkpoints
+ first-epoch no-KeyUpdate application traffic material invariant
==>
supported-profile client/server key-material agreement
```

The proof should mostly reuse existing lemmas:

1. Use
   `lemma_client_server_driver_supported_profile_application_record_state_inputs_from_first_epoch_no_key_update`
   to turn the first-epoch/no-KeyUpdate invariant into
   `client_server_driver_supported_profile_application_record_state_inputs`
   (`Pairing.fsti:410-431`, `Pairing.fst:456-486`).
2. If using `paired_handshake_message_states`, call
   `lemma_client_server_driver_remaining_semantic_projection_inputs_from_paired_handshake_message_states`
   to obtain cleartext Hello equality plus the application derivation checkpoint
   (`Pairing.fsti:492-504`, `Pairing.fst:532-552`).
3. Alternatively, if using explicit `paired_cleartext_hello_messages` and
   `paired_handshake_events`, call
   `lemma_client_server_driver_remaining_semantic_projection_inputs_from_cleartext_and_handshake_events`
   (`Pairing.fsti:467-480`, `Pairing.fst:510-530`).
4. Use `lemma_client_server_driver_supported_profile_state_inputs_from_projection_inputs`
   to get `client_server_driver_supported_profile_state_inputs`
   (`Pairing.fsti:506-517`, `Pairing.fst:553-568`).
5. Use `lemma_client_server_driver_supported_profile_key_material_inputs_agree`
   plus `CSL.lemma_supported_profile_client_server_key_material_agrees` to get
   `CS.supported_profile_client_server_key_material_agrees`
   without any transport premise (`Pairing.fst:570-612`,
   `ConnectionState.Lemmas.fst:3649-3659`).
6. Apply the Phase 1 projection lemmas for the client-to-server and
   server-to-client application key/IV statements.

This is the minimum theorem that validates the pure state-machine pairing story:
paired handshake states/events imply the same application record material. It
avoids the byte parser/serializer layer while still testing whether the client
and server state-machine specs compose.

### Phase 3: derive the event-level preconditions from event traces

The Phase 2 theorem can initially take `CS.paired_handshake_message_states` or
`paired_cleartext_hello_messages /\ paired_handshake_events` directly. The next
step is to define and prove a trace-level predicate over `cs_event_log`, such as:

```text
paired_handshake_event_trace client server
```

intended to state that:

- the client-sent ClientHello is the server-received ClientHello;
- the server-sent ServerHello, EncryptedExtensions, Certificate,
  CertificateVerify, and Finished are the corresponding client-received
  messages;
- the client-sent Finished is the corresponding server-received Finished;
- local verification events append the expected Finished bytes to the transcript.

The useful existing hooks are:

- `sent_tls_messages`, `received_tls_messages`, and `state_machine_events`
  summarize event logs (`ConnectionState.fst:2606-2628`);
- `conn_event_transcript_delta` and `transcript_bytes_of_conn_events` describe
  transcript bytes contributed by network and local events
  (`ConnectionState.fst:2630-2670`);
- `connection_state_event_log_consistent` ties the event log to the final model
  (`ConnectionState.fst:2922-2931`);
- `paired_handshake_events` is the desired checkpoint-level state predicate
  (`ConnectionState.fst:495-504`).

The theorem for this phase should prove:

```text
paired_handshake_event_trace client server
==>
CS.paired_handshake_events client server
```

and, if the trace predicate carries structured messages, also:

```text
paired_handshake_event_trace client server
==>
CS.paired_handshake_message_states client server
```

Once these lemmas exist, Phase 2's theorem can be restated with an event-trace
precondition instead of final-state paired handshake predicates.

### Phase 4: lift from byte traces to event traces

The byte-trace theorem should reuse the existing replay invariants in the
client/server end-to-end predicates:

- raw sent/received event replay;
- sent-seal replay;
- received-decode replay;
- layered/full log consistency.

The intended proof shape, after the verified cleartext-byte progress, is:

1. Start from `CS.paired_wire_logs client server` or from exact external
   `paired_driver_transport_logs_exact`.
2. Use replay consistency to identify the raw TLS record slices corresponding to
   the cleartext handshake messages.
3. Use the new cleartext raw replay lemmas to prove ClientHello serialized
   equality, ServerHello wire equivalence, ServerHello key-share equality under
   explicit supported parse assumptions, and the `DeriveHandshakeTraffic`
   checkpoint.
4. Use protected-record decode/open replay for encrypted handshake messages to
   prove `paired_protected_handshake_wire_equivalent`, i.e., equality of the
   serialized EncryptedExtensions, Certificate, CertificateVerify, server
   Finished, and client Finished handshake bytes.  This is intentionally weaker
   than exact `M` record equality, but it is exactly what the transcript
   checkpoints use.
5. Apply
   `TLS13.Spec.WireFormatLemmas.lemma_paired_handshake_events_from_cleartext_raw_and_protected_wire`
   to obtain `paired_handshake_events`, then apply
   `lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projections`,
   which packages this route to application record-material agreement (or apply
   the Phase 3 event-trace theorem if a full paired event trace is obtained).

The remaining hard part is now step 4's replay threading: identify the matching
protected record slices and prove the sender/receiver record sequence numbers are
aligned at each slice. Once a slice and its pre-event record states are
identified, the event-projection bridge gives the needed serialized handshake
equality, and the five-record wrapper assembles those facts into
`paired_protected_handshake_wire_equivalent`.
The helper module also exposes replay-head destructors,
`lemma_conn_events_sent_seal_replay_head` and
`lemma_conn_events_received_decode_replay_head`, which make the first event's
raw deltas and seal/decode projections available from the recursive replay
predicates.  It now also includes `lemma_append_heads_equal_same_len`,
`lemma_raw_delta_heads_equal_same_len`,
`lemma_equal_stream_record_head_lengths`,
`lemma_protected_handshake_event_projection_pair_from_aligned_heads`, and
`lemma_protected_handshake_event_projection_pair_from_equal_stream_heads`.
Together these remove the previous equal-length assumption: if two paired raw
streams are equal, the sender head delta is a full parsed protected record, and
the receiver head delta is a full parsed protected record, then the parser-prefix
facts imply the two head lengths are equal, the head bytes are equal, and the
`protected_handshake_event_projection_pair` witness follows.  The remaining
`lemma_sent_event_nonempty_seal_projection_protected` and
`lemma_received_event_nonempty_decode_projection_protected` turn the replay
predicates' "empty-or-projection" facts into real projections for protected
single-record network events.  Finally,
`lemma_protected_handshake_event_projection_pair_from_head_replays` combines the
head destructors, nonempty-projection lemmas, parser-prefix length equality, and
equal-stream-head constructor to extract one `protected_message_replay` witness
when the matching sender and receiver protected events are both at the head of
their remaining event logs and their remaining raw streams are equal.

The helper module now also proves the continuation fact needed to iterate this
extractor.  `lemma_append_tails_equal_same_len` and
`lemma_protected_handshake_event_tails_equal_from_equal_stream_heads` show that,
after equal protected-record heads have been consumed from equal raw streams, the
remaining sender-sent and receiver-received byte tails are still equal.
`lemma_protected_handshake_event_projection_pair_from_head_replays_with_tails`
packages this with the head extractor: it returns the protected-message witness,
the sender/receiver post-step models, the continuation replay predicates, and the
equal remaining byte streams.  Its `...with_next_alignment_and_tails` variant
also carries write/read record-material alignment across ordinary protected
handshake heads whose steps are exactly `R.next_seq` on the relevant write/read
directions.

The remaining proof obligation is to use these head-replay extractors
inductively at the five protected handshake event positions: after consuming the
cleartext prefix and any local/zero-byte events, bring each matching protected
send/receive event pair to the head of the sender/receiver replay predicates and
show the remaining raw streams are equal.  The first synchronization step is now
available in the helper module: `lemma_equal_streams_skip_empty_left/right/both`
handle the byte-stream algebra, while
`lemma_sent_replay_skip_empty_head_preserves_peer_stream` and
`lemma_received_replay_skip_empty_head_preserves_peer_stream` destruct the
recursive replay predicate, advance through a local or opposite-direction
zero-byte head, and preserve equality with the peer stream.  These lemmas do not
yet find the five protected handshake events by themselves; they are the
verified one-step machinery needed for that induction/search.  A second wrapper
layer,
`lemma_protected_handshake_event_projection_pair_after_sender_skip_empty_head`
and
`lemma_protected_handshake_event_projection_pair_after_receiver_skip_empty_head`,
composes one such skip with the existing head extractor, provided the caller
supplies the post-skip record sequence/material alignment.  This makes explicit
that synchronization and record-state alignment are separate obligations.  The
module also includes the symmetric two-sided wrapper
`lemma_protected_handshake_event_projection_pair_after_both_skip_empty_heads`,
which advances one empty/local head on each endpoint before applying the
head-replay extractor.  Each of these generic skip wrappers now has a
`...with_tails` variant, so a proof can skip a local/opposite-direction head,
extract the next protected pair, and continue from the returned replay tails
without re-proving byte-tail equality.  For the narrower but common case of skipping only
opposite-direction network events, the module now exposes preservation lemmas
showing that a sender-side received network event preserves the sender write
record state, a receiver-side sent network event preserves the receiver read
record state, and therefore write/read sequence-and-key/IV alignment is
preserved through one or both such skips.  The network-specific wrappers
`lemma_protected_handshake_event_projection_pair_after_sender_received_network_head`,
`lemma_protected_handshake_event_projection_pair_after_receiver_sent_network_head`,
and `lemma_protected_handshake_event_projection_pair_after_opposite_network_heads`
combine these preservation facts with stream skipping and head extraction, so
their callers only need the initial write/read alignment rather than an explicit
post-skip alignment witness.  These network-specific wrappers also now have
`...with_tails` forms for one-sided and two-sided network skips.  Local
traffic-key installation remains outside
those preservation lemmas because it can legitimately change record material;
for the initial handshake keys, the module now has concrete install-alignment
lemmas for server-write/client-read and client-write/server-read installs when
both sides install the same `traffic_key_material`, plus generalized variants
that require only agreement of the installed AEAD key/IV material.  The latter
are closer to the protected-record obligation, since AEAD replay needs matching
keys and nonces but not syntactic equality of the erased traffic-secret lineage.
These facts expose the remaining proof shape: derive equality of the installed
handshake traffic keys/IVs from the transcript/key-schedule pairing, then use
these install lemmas to seed the protected-record head extractors.  A related projection from
`peer_record_material_agrees` to the extractor's model-level alignment is only
valid with an explicit sequence-number premise: `peer_record_material_agrees`
talks about epoch/key/IV agreement, not current record sequence counters.  This
is an important boundary in the state-machine spec, since the protected AEAD
bridge needs nonce equality and therefore sequence equality in addition to
key/IV agreement.  The helper module also proves that alignment is preserved
when both sides advance the relevant record direction with `R.next_seq`, and it
offers a head-replay extractor that returns the protected pair and post-head
alignment when the caller supplies the exact post-step models and the fact that
those steps are `next_seq` advances.  This premise is deliberately explicit:
client Finished is a protected handshake message whose send step may install
application write keys after advancing, so not every protected handshake head has
the simple `next_seq` shape needed to chain to another handshake protected
record.  The helper module further distinguishes local events that do not
install record keys: sign/validate/verify and other non-install local steps
preserve the record layer, and therefore preserve write/read alignment.  Local
traffic-key installation remains the only local skip class that must be handled
via key-schedule-specific install lemmas.  There are now local-specific
projection wrappers for a single non-install local head on either endpoint; they
compose the zero-byte skip, local record-alignment preservation, and protected
head extraction in one step, and their `...with_tails` variants return the
post-head replay tails for subsequent encrypted handshake records.  The newer
`...with_next_alignment_and_tails` wrappers additionally carry alignment through
the protected record following a one-sided or two-sided skip, which is the form
needed for an inductive replay proof.

There is now a verified staged skeleton for the server encrypted flight.
The generic helpers chain two consecutive protected heads, then paired
non-install local heads, then a third protected head.  The server-specialized
wrappers seed this chain from the server-handshake-write/client-handshake-read
traffic-key installs and then extend it through the client-side
CertificateVerify verification local step and the server Finished record:

- `lemma_protected_handshake_event_projection_pairs_after_server_write_client_read_install_server_encrypted_flight_with_tails`
  returns the four server-to-client protected-message witnesses
  (EncryptedExtensions, Certificate, CertificateVerify, server Finished), final
  replay tails, and post-Finished write/read alignment.
- `lemma_server_encrypted_flight_preserves_client_to_server_stream_with_tails`
  proves the dual byte-continuity fact needed for the following client Finished:
  while the server encrypted flight consumes server-sent/client-received bytes,
  the opposite client-to-server raw stream is only threaded through zero-byte
  local events and opposite-direction network events.  The lemma advances through
  the same staged server-flight replay shape and returns tails satisfying
  `Seq.equal client_tail_sent server_tail_received`.  This removes one important
  explicit premise from the eventual byte-trace theorem: the client Finished raw
  equality can be inherited from the original paired byte streams once the full
  log segmentation exposes these tails.
- `lemma_server_encrypted_flight_preserves_client_to_server_replay_tails_with_tails`
  is the version with the replay predicates in the form required by the client
  Finished extractor: it skips through the server flight in the client's
  `conn_events_sent_seal_replay` and the server's
  `conn_events_received_decode_replay`, returning a client sent-seal tail and a
  server received-decode tail with equal client-sent/server-received raw streams.
  This is the precise bridge from a full paired byte stream to the client
  Finished protected-message replay.
- `lemma_server_encrypted_flight_produces_client_finished_replay_inputs_with_tails`
  packages the preceding tail bridge with the record-alignment bridge.  From
  initial client-write/server-read alignment plus the client-sent/server-received
  replay of the server-flight prefix, it returns existential raw tails that
  simultaneously satisfy the client Finished extractor's alignment, raw equality,
  client sent-seal replay, and server received-decode replay preconditions.
- `lemma_paired_protected_handshake_event_projection_pair_witnesses_from_contiguous_staged_replays`
  is now the main staged protected replay theorem for a contiguous server-flight
  plus client-Finished segment.  It assumes both replay views of each endpoint
  over that segment: server sent-seal/client received-decode for the server
  encrypted flight, and client sent-seal/server received-decode to derive the
  client Finished replay tails.  It then derives the client Finished raw/alignment
  inputs internally and calls the earlier five-witness composition theorem.
- `lemma_server_encrypted_flight_preserves_client_write_server_read_alignment`
  proves the matching record-state continuity fact.  If the client handshake
  write direction and server handshake read direction are aligned before the
  server encrypted flight, then the server's handshake-write install/sent
  records and the client's handshake-read install/received records do not disturb
  that opposite direction; the lemma returns
  `write_read_record_material_aligned client_after3 server_after3`, exactly the
  alignment needed at the start of the client Finished extractor.

The client-Finished side now has its own verified staged extractor:

- `lemma_protected_handshake_event_projection_pair_after_client_finished_local_skips_with_tails`
  accounts for the actual driver ordering after server Finished: the client
  verifies server Finished, installs client application write keys, installs
  server application read keys, and then sends client Finished; the server
  installs server application write keys before receiving that client Finished.
  The helper skips those zero-byte local events, preserves the existing
  client-handshake-write/server-handshake-read alignment through the local
  application installs that do not affect those record directions, and extracts
  the client Finished protected-message witness with replay tails preserved.

The five-record packaging boundary is also explicit:

- `lemma_paired_protected_handshake_event_projection_pairs_intro` turns the four
  server-flight witnesses plus the client Finished witness into
  `paired_protected_handshake_event_projection_pairs`, provided they match the
  final client/server handshake-state fields.  This is the predicate consumed by
  the high-level bridge
  `lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projections`.
- `lemma_paired_protected_handshake_event_projection_pairs_intro_from_messages`
  is the same bridge in the form used by staged replay extractors: it accepts the
  five protected-message pairs for explicit `sent_msg`/`received_msg` variables
  and packages them after proving those variables are exactly the messages stored
  in the final client/server handshake states.
- `lemma_paired_protected_handshake_event_projection_pair_witnesses_intro_from_messages`
  additionally exposes that package existentially, matching the protected
  premise of the Pairing-level wrapper.
- `lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_pair_outputs`
  composes the staged extractor outputs in the shape they naturally produce: an
  existential package of the four server-flight pairs plus an existential client
  Finished pair, yielding the single five-witness existential package.

The AEAD open(seal(...)) step is available, but it remains an explicit trust
assumption in the crypto spec.

The concrete staged composition is available as
`lemma_paired_protected_handshake_event_projection_pair_witnesses_from_staged_replays`.
It calls the verified server encrypted-flight extractor and the verified
client-Finished extractor, then packages the resulting five protected witnesses
existentially.  Its premises are still deliberately explicit: the caller must
provide the staged replay shapes, the message-to-final-state correspondence, the
server-flight key-schedule/install alignment premises, and the separate
client-write/server-read alignment plus raw-stream equality needed for client
Finished.  The stronger
`lemma_paired_protected_handshake_event_projection_pair_witnesses_from_contiguous_staged_replays`
removes the separate client-Finished raw/alignment premises when the server
encrypted flight and client Finished are presented as one contiguous replay
segment.  The
`lemma_server_encrypted_flight_preserves_client_to_server_stream_with_tails`
derives the client-Finished raw-stream equality across the server-flight segment;
the replay-tail variant
`lemma_server_encrypted_flight_preserves_client_to_server_replay_tails_with_tails`
returns that equality with the exact `sent_seal`/`received_decode` tails consumed
by the client Finished extractor, and
`lemma_server_encrypted_flight_produces_client_finished_replay_inputs_with_tails`
packages those tails with the corresponding alignment fact.  Its companion
`lemma_server_encrypted_flight_preserves_client_write_server_read_alignment`
threads the opposite client-write/server-read record alignment to the same
post-server-Finished models.

The remaining gap to a true byte-trace theorem is now whole-log segmentation:
derive the contiguous staged segment from complete endpoint logs and paired byte
streams.  The first generic split lemmas for that are now present:
`lemma_conn_events_sent_seal_replay_append_split` and
`lemma_conn_events_received_decode_replay_append_split` split replay predicates
over `prefix ++ suffix` into prefix and suffix replays with corresponding byte
decompositions.  `lemma_sent_received_replay_append_split_equal_tails` composes a
sent-seal split with the peer received-decode split, exposing a conditional
suffix-byte equality from full-stream equality; the condition is precisely that
the paired prefixes consume the same number of bytes.  The wrapper
`lemma_sent_received_replay_append_split_equal_tails_from_aligned_prefixes`
turns that into unconditional suffix equality when supplied with a proof of the
prefix-length alignment.  `lemma_conn_events_raw_replay_append_split` now also
provides a common segmentation point for the endpoint's raw log itself.  The
same-endpoint alignment problem has been narrowed further by
`lemma_conn_events_sent_received_replays_same_events_final_model_equal`,
`lemma_conn_events_raw_sent_seal_replays_same_events_final_model_equal`,
`lemma_conn_events_raw_received_decode_replays_same_events_final_model_equal`,
and
`lemma_same_endpoint_sent_received_replay_append_split_equal_suffixes_from_equal_prefixes`.
Together, these show that sent-seal and received-decode views over the same
endpoint prefix end at the same post-prefix model, and—if the concrete prefix
bytes are shown equal—can be made to share the same raw suffix.  The
cross-endpoint byte-tail step is factored as
`lemma_paired_replay_suffixes_equal_from_equal_prefixes`: from paired full
streams and equal paired prefixes, it proves equality of the remaining
server-sent/client-received and client-sent/server-received suffixes.  The
internal combinator
`lemma_paired_replay_suffix_views_from_full_replays_with_equal_prefixes` composes
these facts: from full replay predicates for both endpoints over
`prefix ++ suffix`, paired full byte streams, same-endpoint prefix-equality
callbacks, and a cross-endpoint prefix-equality callback, it returns aligned
suffix replay views plus both cross-direction suffix equalities.  The same bridge
is now exposed in the small module
`TLS13.ConnectionState.ProtectedWireSegmentation`, with named callback
obligations
`same_endpoint_replay_split_prefixes_equal` and
`paired_replay_split_prefixes_equal`.  This now sits on top of a modular split of
the former protected-wire proof monolith:
`ProtectedWireBase` contains the replay/pairing predicates and named event-list
shapes, `ProtectedWireStream` contains byte-stream sequence lemmas,
`ProtectedWireReplay` contains replay append/suffix splitting, and
`ProtectedWireStaged` packages the contiguous protected-handshake replay witnesses.
This gives downstream proofs a public, verified way to use full endpoint replay
logs once the concrete prefix callbacks are proved without rechecking a single
17K-line proof file.  A second verified specialization,
`lemma_paired_protected_handshake_contiguous_replay_views_from_full_replays_with_equal_prefixes`,
fixes the suffixes to the named contiguous protected-handshake shapes.  It
returns the compact `paired_protected_handshake_contiguous_replay_views`
predicate plus both protected suffix byte equalities, ready to feed the staged
protected replay theorem.

That callback instantiation is now verified for the concrete TLS 1.3 cleartext
prefix.  The named prefix shapes are:

- `server_cleartext_handshake_prefix_events`: server start, received
  ClientHello, parameter selection, shared-secret derivation, sent ServerHello.
- `client_cleartext_handshake_prefix_events`: client start, sent ClientHello,
  received ServerHello, shared-secret derivation.

The module proves the base cases
`lemma_same_endpoint_replay_split_prefixes_equal_empty` and
`lemma_paired_replay_split_prefixes_equal_empty`, the one-local-event variants
`lemma_same_endpoint_replay_split_prefixes_equal_single_local` and
`lemma_paired_replay_split_prefixes_equal_single_local`, and the network-message
building blocks.  The same-endpoint prefix side has
`lemma_same_endpoint_replay_split_prefixes_equal_single_sent_cleartext`, which
discharges one deterministic sent cleartext network event (the pattern needed
for client-sent ClientHello and server-sent ServerHello on the endpoint's own
sent log).  It also has
`lemma_same_endpoint_replay_split_prefixes_equal_single_received_server_hello`
and `lemma_paired_replay_split_prefixes_equal_single_server_hello`, covering the
deterministic ServerHello received side and the paired server-sent/client-received
ServerHello prefix when both sides already name the same structured
`M.server_hello`.  The harder ClientHello receive/cross-endpoint case is now
also covered: `TLS13.Spec.WireFormatLemmas.lemma_received_client_hello_raw_length`
uses record/message parseback to show that a received ClientHello raw record has
the same length as the model's serialized ClientHello, and
`TLS13.ConnectionState.ProtectedWireSegmentation` uses that fact in
`lemma_same_endpoint_replay_split_prefixes_equal_single_received_client_hello`
and `lemma_paired_replay_split_prefixes_equal_single_client_hello`.  The module
also exposes uniform callback combinators for empty prefixes and one-sided local
events, plus singleton raw-byte helpers for sent ClientHello, sent ServerHello,
and received ServerHello replay heads.  These are composed by
`lemma_paired_replay_split_prefixes_equal_uniform_cleartext_handshake_prefix`
for the cross-endpoint cleartext prefix and by the same-endpoint cleartext prefix
wrappers for each endpoint's own sent/received replay views.  Finally,
`lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_full_replays`
combines the concrete cleartext prefix with full sent-seal/received-decode replay
predicates for both endpoints and the paired full byte streams.  Its conclusion
is the protected contiguous replay view package plus equality of the protected
suffix byte streams in both directions, but it hides the post-cleartext models
existentially.

That existential midpoint has now been tightened in
`TLS13.ConnectionState.ProtectedWireConcreteSegmentation`.  Its
`lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_full_replays_known_start`
splits the same full replays, uses the named cleartext prefix step chain to prove
that the server protected suffix starts at `server_model5` and the client suffix
starts at `client_model4`, and returns the same contiguous protected replay-view
package at those concrete models.  The same module now also exposes
`lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_state_logs_known_start`,
which starts one layer higher: instead of asking callers for four full replay
predicates directly, it consumes final `connection_state`s whose `cs_event_log`s
are exactly the named cleartext prefix followed by the named protected suffix,
paired `cs_wire_log` byte streams, and the existing sent-seal/received-decode
replay-consistency predicates.

The Pairing-level packaging step is now factored into
`TLS13.Impl.Driver.PairingProtectedReplay`.  Its
`lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_contiguous_replay_views`
composes the protected contiguous replay-view theorem with the existing
cleartext-raw Pairing bridge: once the protected suffix is already exposed as
`paired_protected_handshake_contiguous_replay_views`, the theorem derives the
protected event-projection witnesses and then proves supported-profile
client/server key-material agreement and both application record-material
directions.  The newer
`lemma_client_server_application_record_material_agrees_from_cleartext_prefix_full_replays`
adds one more layer: from full endpoint replays over
`cleartext_prefix ++ protected_contiguous_suffix`, with the exact named
cleartext prefix and paired full byte streams, it invokes the concrete
segmentation lemma and then the contiguous-view Pairing bridge.

The current handshake-complete boundary theorem is
`lemma_client_server_application_record_material_agrees_from_handshake_complete_boundary`
(`PairingProtectedReplay.fsti:830-954`, implementation
`PairingProtectedReplay.fst:967-1479`).  Its new predicate
`paired_handshake_complete_boundary_state_logs`
(`PairingProtectedReplay.fsti:23-101`) is the exact no-tail state-log boundary:
the server log is
`server_cleartext_handshake_prefix_events ++
server_protected_handshake_contiguous_replay_events ... []`, the client log is
the analogous client prefix plus protected suffix with `[]`, the two raw wire
logs are paired in both directions, and both endpoints satisfy the sent-seal and
received-decode replay-consistency predicates.  The theorem still requires the
same explicit cleartext raw replay/profile assumptions, first-epoch/no-KeyUpdate
state assumptions, cleartext step chain, staged protected step/key-install facts,
and final protected-message correspondence that the lower bridges need.  Given
those assumptions, it proves:

```fstar
CS.supported_profile_client_server_key_material_agrees client server /\
CS.peer_record_material_agrees
  (CS.traffic_id CS.TrafficApplication CS.ClientTraffic) client server /\
CS.peer_record_material_agrees
  (CS.traffic_id CS.TrafficApplication CS.ServerTraffic) client server
```

The proof skeleton is deliberately small.  First it calls
`TLS13.ConnectionState.ProtectedWireConcreteSegmentation.lemma_paired_protected_handshake_contiguous_replay_views_from_cleartext_prefix_state_logs_known_start`
with empty server/client suffix rests, thereby extracting the contiguous
protected replay-view package from the exact final `cs_event_log`s.  Then it
eliminates the existential raw protected suffix witnesses and calls
`lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_contiguous_replay_views`.
So the new theorem is the first verified Pairing-level statement at the exact
handshake-complete state-log boundary: callers no longer have to provide the full
protected replay predicates directly, only the boundary-shaped final states and
the staged semantic witnesses.

The reviewer-facing wrapper layer is now separated into two small modules rather
than adding more proof code to `PairingProtectedReplay`:

- `TLS13.Impl.Driver.PairingCleanBoundary` defines the compact public predicate
  `paired_supported_handshake_complete_boundary client server` and proves
  `lemma_client_server_application_record_material_agrees_from_clean_boundary`.
  The theorem's public precondition is just that predicate; internally, the
  predicate packages the backend witness bundle needed by
  the rest-aware full-replay backend.  The rest parameters are important: on the
  server side, a satisfiable application-ready boundary must include the local
  `LocalVerifyClientFinished` step after receiving the client's Finished, since
  receiving that Finished moves only to `HsClientFinishedReceived`.
- `TLS13.Impl.Driver.PairingValidByteTrace` defines
  `paired_valid_byte_traces_at_handshake_complete_boundary`, adding client/server
  `WFSM.valid_byte_trace` facts and paired sent/received byte streams around the
  clean boundary predicate.  Its top-level theorem
  `lemma_client_server_application_record_material_agrees_from_valid_paired_byte_traces_at_handshake_complete_boundary`
  proves the same application record-material agreement conclusion from this
  compact valid-byte-trace-at-boundary package.
- `TLS13.Impl.Driver.PairingNoTail` defines no-tail application-ready boundary
  predicates.  The legacy server boundary uses length `15`, but the corrected
  satisfiable server no-tail boundary is length `16`, matching the extra
  server handshake-read install before receiving protected ClientFinished.  The
  module also proves small generic and endpoint-specific lemmas extracting
  `SM.trace_reaches`/connection consistency from `WFSM.valid_byte_trace`.
- `TLS13.Impl.Driver.PairingNoTailWireLogs` proves the canonical byte/log bridge:
  valid byte traces from `CS.initial` have external sent/received byte streams
  equal to the final `cs_wire_log.raw_sent/raw_received` fields.  The normalized
  no-tail wrapper uses this to derive `CS.paired_wire_logs` from the external
  paired byte-stream premises.
- `TLS13.Impl.Driver.PairingNoTailClientShape` and
  `TLS13.Impl.Driver.PairingNoTailServerShape` record verified role-local
  intermediate inversion facts: the client no-tail log starts
  `LocalStartHandshake; Sent ClientHello; Received ServerHello`; the server
  no-tail log starts `LocalStartServer; Received ClientHello`; both modules also
  expose final-model witnesses and intended normalized shapes.  They deliberately
  do not claim the full event-log inversion.

These wrappers are intentionally thin.  They make the auditable theorem statement
small and keep the large witness package in one internal predicate, but they do
not yet prove that an arbitrary valid byte trace ending in `ControlApplicationData`
must itself have the handshake-complete shape or the protected-record alignment
witnesses hidden in the clean predicate.  `PairingNoTail` verifies the no-tail
boundary wrapper and valid-byte-trace-to-consistency pieces, but it does not prove
the full event-log inversion from no-tail valid traces.  That remaining result is a separate
endpoint trace-shape/backend-witness theorem: valid byte trace plus a
first-application-ready boundary condition should derive the clean boundary
package, including the server's final local Finished verification step and the
record-material/sequence alignment needed by protected replay.  Without that
first-boundary condition, only a prefix theorem is true, because application data,
post-handshake messages, KeyUpdate, and close-notify events are legal after
entering application data.

So the byte-segmentation boundary has moved again: given final endpoint states
whose event logs are exactly `cleartext_prefix ++ protected_contiguous_suffix`
and whose logs satisfy the sent-seal/received-decode replay-consistency
predicates, the proof derives the protected suffix views and reaches
Pairing-level application record-material agreement.  The remaining skeptical
point is no longer the cleartext prefix byte alignment, the concrete protected
suffix start model, or the Pairing-level composition from final boundary states;
it is the stronger question of where the exact prefix/suffix decomposition comes
from in final endpoint logs.  Raw replay alone is also still too weak for
protected records: protected equality must come from the stronger seal/decode
projections and AEAD open-after-seal assumption, not from
`event_raw_delta_legal` alone.

One important caveat is that this full-replay bridge currently assumes the
cleartext prefix names the same structured `ClientHello` and `ServerHello` on
both sides.  This is appropriate for the paired event-trace theorem, but it is
stronger than the eventual byte-trace theorem should need: raw ClientHello bytes
can validate the weaker key-share/transcript facts without exact
`M.client_hello` record equality.

There is also an event-log shape gap, distinct from byte equality.  The existing
high-level `paired_handshake_message_states` predicate records that the expected
handshake messages occur in the event logs (`event_trace_has_tls_message`), but
occurrence is not a contiguity theorem: it does not by itself split
`cs_event_log` as `pre_protected_prefix ++ protected_handshake_suffix`.  The new
handshake-complete boundary theorem assumes and uses exactly such a split with no
tail.  A final byte-trace theorem therefore needs either a driver/state-machine
invariant exposing that exact first-application-ready boundary shape, or an
additional trace-normalization theorem proving that application-ready,
first-epoch/no-KeyUpdate runs have the named handshake segment as a prefix and no
interleaved events between the protected handshake records beyond the local skips
already modeled in the suffix.

There is a stronger skeptical caveat: plain `client_driver_application_ready` and
`server_driver_application_ready` are probably too weak to imply this exact shape
on their own.  They say the endpoint is in application-data control state with
application record keys installed, and their end-to-end invariants include the
seal/decode replay-consistency predicates consumed by the new state-log wrapper.
But they do not say the endpoint is at the *first* application-ready boundary or
that no application data, alerts, or post-handshake traffic has already been
appended to `cs_event_log`.  A theorem stated for arbitrary application-ready
states should therefore be prefix-based ("there exists a handshake prefix/suffix
inside the log") rather than exact-log-based, or it should strengthen the state
predicate to a handshake-complete boundary state.

There is a second, more concrete state-machine caveat.  `TlsChangeCipherSpec` is
legal and a no-op in any handshaking stage.  Therefore a proof that the second
client no-tail event is the sent ClientHello cannot be obtained from
`legal_event` and the final length alone; it needs the progress-rank/no-room
argument used by the current no-tail inversion lemmas, or a stronger driver
boundary predicate that excludes no-op compatibility records.  Same-stage key
installs can also commute in the abstract state machine, and
`WFSM.valid_byte_trace (ClientCP.client_system ...)` / `WFSM.valid_byte_trace
(ServerCP.server_system ...)` do not encode the concrete endpoints'
`next_local_action` priorities.  So the final normalized theorem should avoid
over-specifying the order of byte-neutral installs unless it is really deriving
that order from a concrete driver-scheduling predicate.

The current verified role-local inversion now discharges the first few instances
of this obligation:
`PairingNoTailInversion.lemma_client_no_tail_second_event_client_hello_clean`
and `lemma_client_no_tail_third_event_server_hello_clean`, together with
`lemma_client_no_tail_fourth_event_derive_shared_secret_clean` and
`lemma_client_no_tail_fifth_event_handshake_traffic_install_clean`, prove that a
16-event application-ready client log starts with
`LocalStartHandshake; Sent ClientHello; Received ServerHello;
LocalDeriveSharedSecret` followed by a handshake traffic-key install.
`PairingNoTailClientPostSharedShape.
lemma_client_no_tail_fifth_and_sixth_events_handshake_traffic_install_clean`
extends this client result one step further: both post-shared-secret events
`e4` and `e5` are handshake-traffic installs, without committing to
write-before-read or read-before-write order.
For the staged-v2 protected replay bridge, the necessary direction-sensitive
strengthening is now also verified:
`PairingNoTailClientPostSharedShape.
lemma_client_no_tail_fifth_and_sixth_events_handshake_install_cover_clean`
shows that the two post-shared events are one client-handshake write install and
one server-handshake read install, order-insensitively.  `PairingNoTailNormalized`
wraps this from the clean16 byte-trace predicate as
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_handshake_install_cover_server_start_spine16`.
This is still client-local: it establishes the receiver-side install facts needed
for protected server-flight decoding, but not the matching server protected
server-flight send events.
The server-side length-15 milestone is now known to be stale.  The useful part of
`PairingNoTailServerShape.lemma_server_no_tail_second_event_client_hello_clean`
through `lemma_server_no_tail_fifth_event_server_hello_clean` is the cleartext
prefix they established for the older boundary:
`LocalStartServer; Received ClientHello; LocalSelectServerParameters;
LocalDeriveSharedSecret; Sent ServerHello`.
But a satisfiable server no-tail trace must be length 16, not 15, because the
server must install client-handshake read keys before receiving the protected
ClientFinished.  At the corrected length, bare
`server_driver_application_ready server /\ length server.cs_event_log == 16`
currently gives only the generic start spine.  The stronger server fact needed by
the semantic theorem is the post-ServerHello package:
the two following slots cover the server handshake write/read installs and the
remaining nine-event suffix is the canonical protected server-flight and
application-ready tail.

The remaining role-local ambiguity is CCS/no-op scheduling.  `TlsChangeCipherSpec`
is legal during handshaking and steps to the same model, so a bare
application-ready/length premise does not by itself expose a canonical no-wasted
event schedule.  The current clean path is therefore either:

- derive the post-ServerHello split and no-CCS facts from paired clean16
  byte/replay inputs; or
- add an explicit canonical `trace_no_ccs server.cs_event_log` premise and prove
  the server semantic shape from application-ready, length 16, and no-CCS.

**Status update (server no-tail boundary correction pass).** Two of
`PairingNoTailServerShape.fst`'s existing length-15 role-local lemmas
(`lemma_server_no_tail_fourth_event_derive_shared_secret_clean` and
`lemma_server_no_tail_fifth_event_server_hello_clean`) failed to verify --
not because of a logic gap, but because their final numeric
`server_application_progress_rank ... == N` facts were being combined, in one
SMT query, with an increasingly large nested "eliminate exists" nesting of
role-local case splits.  Query-stats/split-queries diagnosis showed every
individual fact was cheap in isolation; the fix was to factor the two
recurring rank computations into standalone lemmas
(`lemma_server_application_progress_rank_client_hello_received_selected` and
`_selected_shared`) so they get their own small queries regardless of
invocation depth, plus a local `--z3rlimit 10` bump (matching the existing
`--split_queries always --z3rlimit 10` convention already used elsewhere in
this file and in `PairingNoTailInversion.fst`) on the fifth-event lemma's
final nested step. Both files now verify with no admits.

This pass also adds the corrected length-16 server boundary scaffolding:
`PairingNoTailInversion.lemma_server_no_tail_log_spine16` and
`.lemma_server_no_tail_first_event_start16`,
`PairingNoTailInversion.server_no_tail_handshake_traffic_install_event`, and
`PairingNoTailServerShape.server_no_tail_start_spine16` plus its proof
`lemma_server_no_tail_start_spine16`.  The composition layer now has the
corrected public input predicate
`PairingNoTailNormalized.paired_supported_no_tail_valid_byte_traces_clean16`,
using `PairingNoTail.paired_no_tail_application_ready_boundary16`, and verified
byte/log infrastructure: connection-state consistency, supported-hello profile,
serialized trace pairing, paired wire logs, and the normalized raw-wire
ClientHello/ServerHello bridge.

For paired clean16 inputs, the server post-ServerHello facts are now packaged by
`PairingNoTailServerPostHelloShape`: it derives
`server_no_tail_post_server_hello_suffix_shape`, proves the next two events are
server handshake-traffic installs, refines them to a write/read cover, and then
derives `server_no_tail_post_two_handshake_installs_tail_order`.  Internally this
uses the `server_hello_window_rank` tight-budget argument: after the cleartext
ServerHello prefix the rank is exactly the number of remaining events, so a CCS
no-op would consume a slot without decreasing the rank and cannot occur in the
canonical suffix.

The new simplification target for the trace-level semantic theorem is therefore
to expose a weaker canonical server boundary, e.g.
`server_driver_application_ready server /\ length server.cs_event_log == 16 /\
trace_no_ccs server.cs_event_log`, and derive the same server semantic package
from that boundary rather than requiring the full event-log shape as a premise.

Verified milestones now isolate the client-side half of this asymmetry:
`TLS13.ConnectionState.ClientCertificateVerifyReachability` proves that any
consistent client model in `ControlApplicationData` must have recorded an
`hs_certificate_verify` witness, and
`TLS13.ConnectionState.ClientCertificateVerifyEvent` strengthens this to an
actual network `Received CertificateVerify` occurrence in `cs_event_log`.
`PairingNoTailNormalized.lemma_clean16_no_tail_valid_byte_traces_client_certificate_verify_witness`
and
`PairingNoTailNormalized.lemma_clean16_no_tail_valid_byte_traces_client_received_certificate_verify_event`
lift those facts from the corrected clean16 paired inputs.  This is useful audit
evidence, but it is deliberately not the whole paired inversion theorem: the
remaining paired-byte step is to connect the client's received
`CertificateVerify` event to the server's corresponding protected sent event and
wire segment.  For convenience
there is also a combined corollary,
`PairingNoTailNormalized.lemma_clean16_no_tail_valid_byte_traces_role_local_client_two_handshake_installs_server_start_spine16_and_client_certificate_verify_witness`,
that packages this witness fact together with the existing
client-two-handshake-installs/server-start-spine16 milestone from a single
clean16 premise; it is a bundling convenience, not additional proof content.

The client protected-flight prefix has also started to become a concrete
role-local theorem rather than just an existential occurrence fact.  The new
module `TLS13.Impl.Driver.PairingNoTailClientProtectedShape` proves, from the
bare client no-tail length-16/application-ready hypotheses plus the verified
commuting install cover, that the next protected events are:

```text
Received EncryptedExtensions; Received Certificate
```

More precisely, `lemma_client_no_tail_seventh_event_encrypted_extensions_clean`,
`lemma_client_no_tail_eighth_event_certificate_clean`, and
`lemma_client_no_tail_ninth_event_validate_certificate_clean` rule out CCS/no-op
and duplicate-install alternatives by replaying the client progress-rank
argument after the two handshake installs and after the protected server-flight
receives.  A second split module,
`TLS13.Impl.Driver.PairingNoTailClientVerifyShape`, extends the same role-local
prefix through the protected `Received CertificateVerify` and the local
`LocalVerifyCertificateSignature` step.  A third split module,
`TLS13.Impl.Driver.PairingNoTailClientFinishedShape`, then extends it through the
protected `Received Finished` and local `LocalVerifyFinished` steps.  Finally,
`TLS13.Impl.Driver.PairingNoTailClientAppShape` proves the order-insensitive
application-key-install pair and the terminal protected client `Sent Finished`.
These modules keep the client-side inversion proof factored by state-machine
phase rather than growing the older monolithic inversion files.

`PairingNoTailNormalized` exposes these under the clean16 paired predicate as
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_first_protected_receive_server_start_spine16`
and
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_second_protected_receive_server_start_spine16`,
plus
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_certificate_validated_server_start_spine16`,
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_certificate_verify_received_server_start_spine16`,
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_certificate_signature_verified_server_start_spine16`,
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_server_finished_received_server_start_spine16`,
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_server_finished_verified_server_start_spine16`,
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_application_installs_server_start_spine16`,
and
`lemma_clean16_no_tail_valid_byte_traces_role_local_client_finished_sent_server_start_spine16`.
The client role-local no-tail prefix is now complete through the 16th event.  The
paired proof still has to match the client receive slices with actual server
sent-seal slices and construct the staged protected replay boundary.

At the driver-pairing level there is also now an existential wrapper,
`lemma_client_server_application_record_material_agrees_from_cleartext_raw_and_protected_event_projection_witnesses`.
It has the same cleartext ClientHello/ServerHello and first-epoch/no-KeyUpdate
requirements as the explicit five-witness theorem, but its protected premise is
only that the five protected projection witnesses exist.  This is the theorem
shape the eventual replay/byte theorem should target: prove existence of the
five protected witnesses from replay, then obtain `paired_handshake_events`, both
key-derivation checkpoints, and both application record-material directions
without exposing witness records at the caller boundary.

### Phase 5: optional existential/server-run theorem

After the paired-run theorem is in place, an existential theorem can be attempted:

```text
given a client run plus explicit server local witnesses, there exists a legal
server run over the opposite bytes that reaches matching application key/IV
material.
```

This should not be the first target. The paired-run theorem validates the client
and server state-machine specs directly; the existential theorem additionally
requires a constructive account of server randomness, server key generation,
credential/signature choices, and local policy decisions.

## Critical and skeptical reading

### The theorem's name is stronger than its current precondition surface

The theorem is named "end-to-end", but its current input predicate is the
component predicate `client_server_driver_key_material_no_read_ahead_component_inputs`
(`Pairing.fsti:983-991`, `532-554`). That predicate already contains the main
semantic pairing facts: paired X25519 shares, paired derivation checkpoints, and
application traffic material matching expected derivations. The theorem is best
read as an end-to-end *bridge over already-supplied semantic components*, not as
a theorem that derives every component from the public client/server driver
resources.

### Paired X25519 shares and transcript checkpoints are assumed here

The theorem does not prove `CS.paired_x25519_key_shares` from `CS.paired_wire_logs`.
There are helper lemmas that can derive paired X25519 shares from per-endpoint
stable projections plus paired cleartext Hello messages
(`Pairing.fsti:300-349`, `Pairing.fst:302-354`), and helper lemmas that derive
application derivation checkpoints from paired handshake messages or paired
handshake events (`Pairing.fsti:315-333`, `Pairing.fst:242-300`). But the main
theorem does not require those weaker projection inputs; it takes the already
packaged `client_server_driver_supported_profile_state_inputs`.

That means a reviewer should separately ask where, for a concrete paired run,
`paired_cleartext_hello_messages`, `paired_handshake_events`, or the final
`paired_x25519_key_shares` and `paired_key_derivation_checkpoints` facts are
established.

### Current application record agreement is first-epoch/no-KeyUpdate shaped

The theorem assumes
`supported_profile_application_traffic_material_matches_expected` for both
endpoints. The expected material is computed from the original application
traffic secret, not from a post-handshake `TrafficUpdateSecret`
(`ConnectionState.fst:2033-2065`, `2084-2090`). The spec has a helper invariant
`first_epoch_application_traffic_material_no_key_update_invariant`, which combines
no KeyUpdate events with first-epoch slots matching expected material
(`ConnectionState.fst:2106-2110`), and a bridge lemma from that invariant to
`supported_profile_application_traffic_material_matches_expected`
(`Pairing.fsti:410-431`, `Pairing.fst:456-486`).

The main theorem, however, does not require the no-KeyUpdate invariant directly;
it requires the stronger material-matches-expected predicate. Practically, this
limits the theorem to first-epoch application traffic unless another proof
establishes the same expected-material facts after updates.

### The final aggregate excludes exporter, resumption, and update secrets

`supported_profile_all_derived_key_material_agrees` enumerates only first
milestone keys. `TrafficUpdateSecret`, `ExporterMasterSecret`, and
`ResumptionMasterSecret` are outside `first_milestone_derived_key_id`
(`ConnectionState.fst:1954-1968`, `2175-2207`). This matches the repository's
supported-profile scope, but it should not be mistaken for full TLS 1.3 key
schedule agreement.

### The proof is functional agreement, not cryptographic security

The theorem proves equality of specified bytes under deterministic spec
functions and the X25519 agreement lemma. It does not prove that keys are secret,
that an attacker cannot influence the transcript, that certificates authenticate
the intended peer, that AEAD encryption is secure, or that the concrete crypto C
code implements the spec. Those are outside this theorem and partly outside the
F* spec boundary (`TLS13.Crypto.Spec.fsti:18-77`).

### Wire-format caveats are deliberately outside the theorem

Because the original theorem assumes semantic pairing facts, it avoids hard
wire-format questions. The newer cleartext-byte lemmas make part of that bridge
explicit, but only with supported-profile restrictions: ClientHello parseback has
supported-profile and empty-SNI caveats, and ServerHello key-share equality is
proved only when both fragments are accepted by the supported ServerHello parser.
Raw ServerHello replay alone still implies only wire/body equivalence, not
unconditional structured record equality. A future theorem that derives all
semantic pairing facts from wire logs alone must keep those caveats explicit.

### Transport/environment reliability is assumed

`paired_transport_histories` is an explicit premise. It says the two supplied byte
histories are paired, not that the runtime necessarily created them. Likewise,
the no-read-ahead premises rule out retained unprocessed suffixes at the theorem
comparison point. This is the right shape for a bridge theorem, but a complete
live-run theorem still needs to connect concrete resources, TCP behavior,
scheduling, retained buffers, and these byte-history premises.

### Record-layer agreement is about current application directions

The final aggregate key-material agreement includes application record material,
not all historical record material. This avoids asking the current record layer
to be simultaneously at handshake and application epochs. Historical handshake
traffic key/IV agreement is still present in
`supported_profile_all_derived_key_material_agrees`, but current record-direction
agreement is application-only.

## Checklist for reviewing this theorem

When auditing a use of
`lemma_client_server_driver_end_to_end_key_material_agrees`, check that the caller
has genuinely established each premise:

1. The client and server states are application-ready under their respective
   driver predicates.
2. The supplied transport histories are the same byte streams in opposite
   directions.
3. Received-prefix witnesses have no retained suffix at this comparison point.
4. Paired X25519 share facts are derived from stable endpoint projections and
   paired Hello messages, not merely assumed without justification.
5. Paired derivation checkpoints are derived from paired transcript/checkpoint
   events or paired handshake message states.
6. Current application traffic material matches expected first-epoch derived
   material, or a stronger KeyUpdate-aware theorem is used instead.
7. The desired conclusion is equality of supported-profile key material, not a
   stronger security/authentication claim.
