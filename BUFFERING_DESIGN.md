# Verified TLS buffering design

## Purpose and assurance boundary

The client and server drivers use one fixed receive buffer per driver and retain
unconsumed TCP bytes across TLS processing steps. The design is intended to
establish three properties:

1. **No data loss or duplication.** Every byte returned by TCP is either in the
   exact prefix already delivered to the TLS processor or in the exact pending
   suffix. Processing commits only the prefix that TLS reports consuming.
2. **TCP history conforms to the TLS state machine.** For every live, reusable
   channel state, the consumed receive prefix and the sent history form a valid
   wire-format state-machine trace. Pending bytes are deliberately outside that
   trace until they are consumed.
3. **No needless blocking read-ahead.** A TCP read is authorized only after the
   verified TLS processor has inspected the exact current pending bytes and
   proved that they form an incomplete, otherwise valid TLS record prefix.

The top-level client and server workflows, including failure cleanup, are Pulse
code. The runtime C files marshal arguments, validate the C ABI, allocate small
wrapper objects, map statuses to errors, and call the extracted top-level API.
They do not schedule TLS protocol steps, inspect TLS endpoint internals, manage
pending bytes, or issue socket reads and writes.

This document first describes the shared design, then the role-specific parts,
and finally gives an audit procedure. Names such as `owns` and `read_auth` below
refer to definitions in the corresponding module, not to informal intentions.

## Architecture

```text
                       unverified application
                                |
             runtime/tls13_{client,server}_driver.c
             ABI checks, status mapping, wrapper lifetime
                                |
                  extracted verified top-level facade
          TLS13.Impl.{Client,Server}.Driver.{fsti,fst}
                                |
            verified role-specific workflows and cleanup
             connect/accept, handshake, send, receive,
                   close, abort, detach, release
                                |
        +-----------------------+-----------------------+
        |                                               |
 TLS endpoint processing                       buffering scheduler
 TLS13.Impl.Client/Server              Common.BufferedStream protocol
 Common.ProtocolImplementation         instantiated by Client/Server
        |                               Driver.BufferedNetwork
        +-----------------------+-----------------------+
                                |
                       Common.BufferedTCP
          abstract buffered channel, exact byte conservation,
             borrow/commit/read/write, attach/detach
                                |
                  Common.BufferedTCP.Internal
           fixed vector, dense prefix, in-place compaction
                                |
                         Common.TCP
                 trusted external transport contract
                                |
                  c_stubs/common_tcp_karamel.c
```

The abstraction boundary is intentional:

- TLS workflow modules see `Common.BufferedTCP.t` and its logical
  `phys_buffer`; they do not see the backing vector or boxed length.
- Only `Common.BufferedTCP` imports `Common.BufferedTCP.Internal` on the live
  buffering path.
- Only the role-specific `BufferedNetwork` endpoint read operation can obtain
  the ownership needed to call `Common.BufferedTCP.read_more`.
- The runtime C shims call only the public extracted driver facade.

Some older server proof modules remain in the source tree and may mention raw
buffering internals. Source presence is not evidence of runtime reachability:
the extraction roots and the top-level call graph determine the live audit
surface. Nevertheless, an audit should check that these legacy modules are not
reintroduced into a top-level workflow or exported facade.

## Shared low-level buffering: `Common.BufferedTCP`

### Abstract state

`common/Common.BufferedTCP.fsti` deliberately hides the representation of:

- `t`, an attached buffered TCP channel;
- `storage`, detached reusable receive storage;
- `phys_buffer`, the logical model of the pending receive buffer; and
- `pending_view`, a temporary read-only view of the pending prefix.

The useful public projections and relations are:

```text
pending model                         exact pending byte sequence
capacity_of model                     fixed receive capacity
buffer_wf model                       pending length <= capacity

received_split received delivered model
  <=> received = delivered ++ pending(model)
```

`is_buffered b model received delivered sent` owns all of the physical state:
the TCP channel, the fixed receive storage, its concrete pending length, and the
relation between those objects and the logical histories. Its key pure fact is
`received_split received delivered model`.

The names have the following meanings:

- `received`: every byte physically returned by TCP so far;
- `delivered`: the exact prefix committed after TLS processing; and
- `pending model`: received bytes not yet committed.

Thus the central conservation equation is:

```text
TCP received history = TLS-delivered prefix ++ pending bytes
```

This is equality of ordered byte sequences, not a length equation, multiset
relation, or subsequence relation.

The `sent` index is the exact sequence accepted by the TCP write abstraction.
It is updated only by `write`.

### Physical representation

`Common.BufferedTCP.Internal` implements the abstract model with:

- one fixed `Pulse.Lib.Vec` byte array;
- one boxed `SizeT.t` pending length;
- pending bytes stored densely in array indices `[0, pending_len)`; and
- free space in `[pending_len, capacity)`.

There is no allocation or pending-buffer copy in the processing/read hot path.
Borrowing splits out a masked prefix view. Releasing the view proves that the
bytes are unchanged and rejoins it with the backing array. Committing a prefix
uses verified in-place compaction (`memmove` in extracted C) to move the
remaining suffix to index zero.

The concrete representation should be audited only through
`Common.BufferedTCP.fst` and `Common.BufferedTCP.Internal.{fsti,fst}`. It should
not leak through the public `Common.BufferedTCP.fsti`.

### State transitions and conservation

The public operations preserve the following exact transitions:

| Operation | Logical transition |
|---|---|
| `borrow_pending` | Exposes a read-only view equal to all of `pending model`; histories and model do not change |
| `release_pending` | Requires the borrowed bytes to be unchanged; reconstructs the same `is_buffered` ownership |
| `commit_prefix n` | `delivered' = delivered ++ take n pending`; `pending' = drop n pending`; `received` and `sent` unchanged |
| `read_more` | Reads into the free suffix; for returned `chunk`, both `received'` and `pending'` append exactly `chunk` |
| `write` | For the requested prefix `chunk`, `sent' = sent ++ chunk`; receive state is unchanged |
| `close_detach` | Closes the TCP channel, clears the pending length, and returns detached storage with the same identity |

For `commit_prefix n`, associativity gives the preservation argument:

```text
received
  = delivered ++ pending
  = delivered ++ take(n, pending) ++ drop(n, pending)
  = delivered' ++ pending'
```

For `read_more`:

```text
received'
  = received ++ chunk
  = delivered ++ pending ++ chunk
  = delivered ++ pending'
```

The same `chunk` occurs in the TCP postcondition, the logical receive history,
and the physical buffer model. This is the critical fact to inspect; equality
of lengths would not rule out corruption.

### Borrowing and committing are separate

TLS receives a view of the entire exact pending prefix. Processing does not
mutate that view. The driver first releases the view and then, if processing was
conclusive, commits exactly the returned `consumed_len`.

This separation matters:

- the parser cannot consume bytes merely by reading them;
- a `NeedMoreInput` result commits zero bytes;
- an error result cannot accidentally compact the buffer; and
- any bytes after `consumed_len`, including a coalesced second record, remain
  pending in their original order.

The TLS processor's postcondition proves `consumed_len <= pending_len`.
Successful steps prove positive consumption. `NeedMoreInput` and hard decoding
or transition failures prove zero consumption.

### Reusable storage lifecycle

Storage is allocated once by the driver:

```text
detached storage --attach(raw TCP channel)--> buffered channel
buffered channel --close_detach------------> detached storage
```

`same_storage` and `lemma_same_storage_unique` prove that detaching returns the
same reusable object that was attached. The client reconnect and server
reaccept paths therefore do not allocate a receive vector per connection.

`close_detach` resets the pending length only after ownership has become
terminal or the caller has explicitly closed the connection. It is not a live
buffer transition: pending bytes may be discarded only while destroying the
associated transport/protocol session.

Audit attach/detach in:

- `TLS13.Impl.Client.Driver.Connect`;
- `TLS13.Impl.Client.Driver.Cleanup`; and
- `TLS13.Impl.Server.Driver.BufferedTransport`.

## Shared scheduling protocol: `Common.BufferedStream`

### Why byte conservation is not enough

The equation `received = delivered ++ pending` can hold even if an
implementation blocks on another socket read while a complete record is
already pending. Buffer safety therefore does not imply the desired scheduling
or liveness property.

`common/Common.BufferedStream.fsti` adds a linear ownership protocol around
processing and reads. Its `buffered_stream_endpoint` class abstracts a
relational, effectful protocol processor while retaining the exact buffering
indices.

The essential resources are:

```text
bse_owns
    exclusive ordinary endpoint ownership

bse_read_auth
    exclusive ownership produced only by a NeedMore process result
    and consumed by exactly one read

bse_terminal
    destructible terminal ownership
```

The state machine is:

```text
                          conclusive
                  +----------------------> Progress / Yield
                  |
bse_owns --process exact pending bytes
                  |
                  +-- NeedMore --> bse_read_auth --read--> bse_owns
                  |
                  +----------------------> Reject / terminal
```

A read returns ordinary `bse_owns`, not another authorization. Consequently,
even if a read returns only part of a record, the enlarged pending buffer must
be processed again before another read can be authorized.

### Processing classifications

`classification` distinguishes:

- `NeedMore`: consumes zero bytes and leaves endpoint state and output buffers
  unchanged;
- `Progress n`: consumes a positive, bounded prefix;
- `Yield n result`: consumes a positive, bounded prefix and returns a
  role-specific endpoint result; and
- `Reject error`: returns terminal ownership.

`process_post` ties each classification to the old and new committed histories,
buffer models, endpoint states, and outputs. In particular, it prevents a
nominal `NeedMore` from hiding a protocol transition or output mutation.

`ProcessBufferFull` is the generic defensive outcome when a processor requests
more data but the physical buffer has no free space. Both TLS instances prove
that this outcome is unreachable: their `bse_buffer_full` predicate is
`terminal ** pure False`.

### Drive loop and fuel

`drive_until_conclusive` captures the common algorithm:

1. Invoke `bse_process` on the exact current `pending model`.
2. Return on `Progress`, `Yield`, or `Reject`.
3. On `NeedMore`, check the caller-supplied fuel.
4. If fuel is zero, return `DriveExhausted` without reading.
5. Otherwise consume `bse_read_auth`, perform exactly one `bse_read`, decrement
   fuel, and return to step 1.

Fuel counts potentially blocking reads, not processing steps. It establishes
totality and bounds workflow blocking; it does not create an additional hidden
TLS limit. A single authorized TCP read may itself block if the peer stops
sending, so the proof is a no-needless-read property, not network fairness or a
wall-clock termination guarantee.

### Production specialization

The endpoint class and its logical dictionary are `noextract`. The generic
`Common.BufferedStream.drive_until_conclusive` is the specification and
reusable proof pattern. To avoid runtime dictionaries, indirect calls, and
unwanted generic representations in extracted C, production uses private
monomorphic loops:

- `client_drive` in
  `TLS13.Impl.Client.Driver.BufferedNetwork.fst`; and
- `server_drive` in
  `TLS13.Impl.Server.Driver.BufferedNetwork.fst`.

Each role proves an actual `buffered_stream_endpoint` instance and the
monomorphic loop is verified against the same `process_post`, transition,
read-authorization, and drive-outcome predicates. The loops call only that
role's verified `process` and `read`.

This specialization is an explicit audit point. Review the two short loops
against `drive_until_conclusive`: the only recursive edge must follow
`NeedMore -> read`, fuel must decrease only there, and the recursive call must
receive the post-read ordinary ownership. The extracted C should contain no
class dictionary or indirect scheduler dispatch.

## The TLS-specific read warrant

### Parser failure is too weak

`parse_record_wire pending == None` does not by itself justify a read. It also
holds for some complete but malformed record headers. Reading after such a
header could block even though more bytes cannot make the existing header
valid.

The TLS endpoint therefore uses
`TLS13.Wire.Spec.record_prefix_incomplete pending` as its semantic
`needs_more` predicate. It is true exactly when:

- fewer than the five record-header bytes are present; or
- a syntactically valid TLS record header with an accepted content type,
  version, and bounded fragment length is present, but fewer than
  `5 + fragment_len` bytes have arrived.

A malformed complete header does not satisfy this predicate and follows the
decode-error/terminal path without authorizing a read.

The contract is propagated through:

1. `TLS13.Impl.Parser.decode_network_buffer`;
2. `TLS13.Impl.Client.process_network_bytes` or
   `TLS13.Impl.Server.process_network_bytes`; and
3. the role's `BufferedNetwork.process`.

On `NeedMoreInput`, those contracts also prove:

- `consumed_len == 0`;
- the TLS connection state stutters;
- network output is unchanged; and
- application output is unchanged.

Those stuttering facts are what allow `process` to exchange ordinary ownership
for `read_auth` without silently losing a state or output transition.

### Why an authorized read always has space

`lemma_record_prefix_incomplete_bound` proves:

```text
record_prefix_incomplete pending ==> length pending < 5 + 16640
```

The buffering capacity is 65535 bytes. Therefore an incomplete accepted TLS
record prefix is strictly smaller than the buffer and `read_more` always has a
positive free suffix. A malicious header declaring an excessive record length
does not create an unfillable authorized state; it is malformed and rejected.

## TLS endpoint processing

Client and server `BufferedNetwork.process` follow the same logical sequence:

1. Open the role's `buffered_driver_indexed` ownership.
2. Borrow a view equal to the entire pending prefix.
3. Invoke the verified role-specific `process_network_bytes`.
4. Release the unchanged pending view.
5. Inspect the TLS response:
   - `NeedMoreInput`: prove stuttering and
     `record_prefix_incomplete pending`, then return `NeedMore` plus
     `read_auth`;
   - successful step: commit exactly `consumed_len`, write exactly
     `network_out_len`, update histories, and return a positive `Yield`;
   - fatal status: return terminal `Reject`.
6. Re-establish the canonical protocol progress and wire-log correspondence.

The endpoint's `read` operation:

1. opens `read_auth`, thereby recovering the unique buffered ownership;
2. invokes `BufferedTCP.read_more`;
3. appends the same returned chunk to the monotonic TCP-history reference; and
4. returns ordinary endpoint ownership over the enlarged pending model.

There is no second read authorization in the postcondition.

All TLS network successes are represented as `Yield`, rather than allowing the
generic scheduler to consume an arbitrary number of protocol records. The
surrounding verified role workflow gets a chance to perform any required local
action after each TLS transition. If a second coalesced record is still
pending, the next network drive processes that retained prefix before any read.

## TCP history and state-machine conformance

There are three related layers of history.

### 1. Physical TCP history

`src/impl/extern/Common.TCP.fsti` is the trusted transport boundary.
`Common.TCP.read` appends exactly the returned chunk to `tcp_received`;
`Common.TCP.write` appends exactly the written prefix to `tcp_sent`.

`BufferedTCP.is_buffered` carries those exact histories through buffering.

### 2. Driver monotonic history

Each driver owns a monotonic reference indexed by
`Common.ChannelImplementation.io_history_preorder`. Every physical read and
write updates it with the exact same chunk used in the `BufferedTCP`
transition. The preorder is proved to imply prefix extension of both receive
and send histories, so snapshots remain valid as the connection progresses.

The update helpers are `tcp_history_note_read` and
`tcp_history_note_write` in each role's `BufferedNetwork` module.

### 3. TLS wire log and canonical state

The role's `buffered_driver_indexed` combines:

- exact TLS connection ownership;
- canonical protocol progress;
- `BufferedTCP.is_buffered`;
- the monotonic TCP history; and
- `client_driver_wire_logs_match_witness` or
  `server_driver_wire_logs_match_witness`.

For a nonfailed TLS state, the witness establishes:

```text
TCP sent       = TLS state wire_log.raw_sent
TCP received   = consumed ++ pending
consumed       = TLS state wire_log.raw_received
```

Thus pending bytes are physically received but intentionally absent from the
TLS state until the processor commits them.

`Common.ChannelImplementation.channel_state_valid` supplies the top-level
semantic statement:

```text
exists tls_state consumed.
  TCP received = consumed ++ pending
  /\ valid_byte_trace TLS_system consumed tls_state TCP_sent []
  /\ application_log = project tls_state
```

`Common.ProtocolImplementation` is the bridge from imperative processing to
parsing, the pure state-machine transition, exact consumed input, and exact
generated output. The client and server instantiate
`Common.ChannelImplementation.channel_implementation` with their canonical TLS
protocol and application-log projection.

On a terminal failed TLS state, the driver still proves exact physical
conservation (`TCP received = committed ++ pending`) and exact sent history,
but its auxiliary relation between the TLS failure log and `committed` is
weaker (`logged_received_bytes_accounted`). This is deliberate because bytes
that cause a parse/transition failure do not form a valid state-machine trace.
Failed ownership is not reusable as a live channel: it must be closed and
released. An audit requiring an exact ordered failure-input log should examine
and potentially strengthen this terminal relation; the live channel guarantee
does not depend on it.

## Client-specific design

The client owns:

- a client TLS connection and canonical client progress;
- an authentication context used to validate the server identity;
- reusable buffered TCP storage;
- network and application output buffers; and
- exact TCP history.

`TLS13.Impl.Client.Driver.State.buffered_driver_indexed` combines the shared
buffer invariant with client connection ownership and client canonical
progress. `top_buffered_driver` additionally owns the authentication context.

The main lifecycle is:

```text
new client
  -> detached storage
  -> TCP connect
  -> attach storage
  -> verified handshake workflow
  -> verified send/receive
  -> close or abort
  -> close_detach
  -> free reusable storage and client state
```

Client processing uses
`TLS13.Impl.Client.process_network_bytes`. Its correctness is tied to
`TLS13.Impl.Client.Types.network_bytes_end_to_end_correct`, including
client-specific state transitions, output, and application-log projection.
Authentication ownership remains in the `BufferedNetwork.owns` predicate
across process/read cycles.

Client hard failures produce terminal ownership. Public send and receive
wrappers consume that ownership and invoke verified abort cleanup; C is not
responsible for reconstructing or disposing of a partially moved TLS
connection. The public `abort` entry point is itself verified and is used by
the runtime only for wrapper-level failure cleanup.

Primary client audit path:

1. `TLS13.Impl.Client.Driver.fsti`;
2. `TLS13.Impl.Client.Driver.State.fst`;
3. `TLS13.Impl.Client.Driver.BufferedNetwork.{fsti,fst}`;
4. `TLS13.Impl.Client.Driver.Connect.fst`;
5. client handshake/send/receive/close/cleanup modules reached from
   `TLS13.Impl.Client.Driver.fst`; and
6. `runtime/tls13_client_driver.c`.

## Server-specific design

The server has the same buffered transport and scheduling protocol, but owns
additional server resources:

- the certificate chain and credential identity;
- proof that credentials support the selected TLS profile;
- server credential handles;
- listener or accepted-channel ownership; and
- local-event resources needed to construct the server handshake flight.

Those resources are included in
`TLS13.Impl.Server.Driver.State.buffered_driver_indexed` and in the server
`BufferedNetwork.owns` predicate. They cannot be separated from a live
connection by unverified C.

### Accept and reusable transport

`TLS13.Impl.Server.Driver.BufferedTransport` owns listener creation, accept,
listener cleanup, attachment of reusable storage to the accepted channel, and
terminal detach. The runtime retains only abstract verified listener,
credential, and driver handles.

### Interleaving local and network actions

Unlike the simpler process/read loop, a server handshake often becomes ready
for a local action after consuming a client record. The verified
`BufferedWorkflow`:

1. performs a ready local action when the protocol state requires one;
2. otherwise invokes `BufferedNetwork.drive`;
3. handles the resulting TLS status; and
4. repeats under explicit local/network workflow fuel.

This ordering prevents an unnecessary read when the server must generate a
ServerHello or another local flight message before accepting more network
input. It also ensures that retained coalesced input is revisited only after
required local transitions have occurred.

`BufferedLocal` and `BufferedTopHandshake` perform credential selection, key
derivation, handshake serialization, and output writes under Pulse ownership.
No corresponding orchestration remains in `runtime/tls13_server_driver.c`.

### Exact-size server output views

Several server serializers require an array whose logical length is exactly the
encoded message length. Certificate and CertificateVerify lengths are
state-dependent. Passing the full 20,000-byte network buffer is not equivalent
to passing an exact-size output object, even if a separate length says only a
prefix will be used.

`BufferedLocal` therefore creates verified zero-copy prefix views of the
network buffer for EncryptedExtensions, Certificate, CertificateVerify, and
Finished. The serializers receive the exact logical array size, and the view is
then rejoined with the backing output buffer. This avoids both a copy and an
overly weak serializer call contract.

### Failure ownership

Accept, handshake, send, receive, and close failure paths terminate and clean up
inside verified Pulse. The C shim maps the returned status and disposes only of
the already-released opaque wrapper. A server terminal state cannot be reused
for another receive or send.

Primary server audit path:

1. `TLS13.Impl.Server.Driver.fsti`;
2. `TLS13.Impl.Server.Driver.State.{fsti,fst}`;
3. `TLS13.Impl.Server.Driver.BufferedTransport.fst`;
4. `TLS13.Impl.Server.Driver.BufferedNetwork.{fsti,fst}`;
5. `TLS13.Impl.Server.Driver.BufferedLocal.fst`;
6. `TLS13.Impl.Server.Driver.BufferedWorkflow.fst`;
7. `TLS13.Impl.Server.Driver.BufferedTopHandshake.fst`;
8. buffered send/receive/close modules reached from
   `TLS13.Impl.Server.Driver.fst`; and
9. `runtime/tls13_server_driver.c`.

## What is shared and what is role-specific

| Concern | Shared | Client-specific | Server-specific |
|---|---|---|---|
| Physical buffering | `Common.BufferedTCP` | Storage attached after connect | Storage attached after accept |
| Process-before-read protocol | `Common.BufferedStream` | Client endpoint instance and monomorphic loop | Server endpoint instance and monomorphic loop |
| Read warrant | `record_prefix_incomplete` | Propagated through client processor | Propagated through server processor |
| Byte conservation | `received_split` and exact transitions | Client wire-log witness | Server wire-log witness |
| State-machine validity | `ProtocolImplementation` and `ChannelImplementation` | Canonical client and authentication projection | Canonical server, credentials, and server application projection |
| Local actions | Generic protocol concept | Client handshake initiation and client local events | Credential selection and multi-message server flight |
| Output handling | Exact written prefix | Client network/app output ownership | Direct output plus exact-size serializer views |
| Cleanup | Terminal ownership and `close_detach` | Verified abort/connect failure cleanup | Verified accept/handshake/send/receive cleanup |

## Audit guide

### A. Audit no data loss or duplication

1. Start at `Common.BufferedTCP.fsti`, not the implementation. Confirm that
   `received_split` is exact ordered concatenation and is exposed in the
   postconditions of all state transitions.
2. In `Common.BufferedTCP.fst`, check that:
   - `read_more` uses the exact chunk returned by `Common.TCP.read` for both
     history and buffer-model updates;
   - `commit_prefix` uses `take` and `drop` at the same `n`;
   - `write` records exactly the prefix handed to TCP; and
   - `borrow_pending`/`release_pending` expose and restore unchanged bytes.
3. In `Common.BufferedTCP.Internal.fst`, inspect the dense-prefix invariant,
   append-read into the free suffix, and overlap-safe compaction.
4. In both `BufferedNetwork.process` implementations, confirm that the borrowed
   view covers all pending bytes and that only the reported `consumed_len` is
   committed.
5. Check that `NeedMoreInput` and failure statuses commit zero bytes.
6. Check that a coalesced suffix remains in `pending` after the first record.
7. Inspect attach/detach identity. Verify that pending storage is reset only
   after the channel becomes terminal or is explicitly closed.
8. Inspect direct application-output paths separately from network buffering;
   make sure returned lengths describe exactly the initialized caller-visible
   prefix.

The most important equations to trace through every operation are:

```text
received = committed ++ pending
sent'    = sent ++ exact_written_prefix
```

### B. Audit TCP/state-machine history conformance

1. Treat `Common.TCP.fsti` as a trusted assumption and verify that the C stub
   implements its exact append contracts, including partial writes and EOF/error
   behavior.
2. In each role's `buffered_driver_indexed`, locate all of:
   `BT.is_buffered`, the monotonic history reference, canonical progress, and
   the role's wire-log match predicate. Missing any one weakens the chain.
3. For every `read_more` or `write`, confirm a matching
   `tcp_history_note_read` or `tcp_history_note_write` uses the identical
   sequence.
4. Inspect `client_driver_wire_logs_match_witness` and
   `server_driver_wire_logs_match_witness`; on nonfailed states they must equate
   the consumed history with `raw_received` and sent history with `raw_sent`.
5. Inspect `Common.ProtocolImplementation` to check that an imperative
   processing success corresponds to the pure parser and state-machine
   transition with exact consumed/generated bytes.
6. Inspect `Common.ChannelImplementation.channel_state_valid`; confirm that the
   valid trace runs over `consumed`, while `pending` is only the exact suffix of
   physical receive history.
7. Check send/receive snapshots use `io_history_preorder`, and that its closure
   proves prefix extension rather than arbitrary reordering.
8. Audit terminal failure separately. Do not mistake
   `logged_received_bytes_accounted` for ordered equality; it is intentionally
   weaker and is not a reusable live-state invariant.

### C. Audit no needless read-ahead

1. In `Common.BufferedStream.fsti`, verify that only a `NeedMore`
   `process_post` can produce `bse_read_auth`.
2. Verify that `bse_read` requires and consumes `bse_read_auth` and returns only
   `bse_owns`.
3. Check `record_prefix_incomplete` in `TLS13.Wire.Spec.fsti`. In particular,
   malformed versions, content types, and excessive lengths must not satisfy
   it.
4. Follow that fact through `TLS13.Impl.Parser.fsti` and both role processor
   interfaces. Confirm that `NeedMoreInput` also proves zero consumption and
   complete state/output stuttering.
5. In client and server `BufferedNetwork.process`, make sure `read_auth`
   contains `needs_more st (BT.pending model)` for the exact current model.
6. Compare `client_drive` and `server_drive` with the generic loop:
   - processing is the first operation;
   - only `NeedMore` reaches `read`;
   - zero fuel returns without reading;
   - positive fuel decreases exactly once per read;
   - post-read ownership goes back to processing; and
   - all conclusive outcomes return without reading.
7. Search all live driver modules for other direct TCP reads or
   `BT.read_more` calls. There should be no bypass.
8. Inspect server `BufferedWorkflow` as an outer scheduler. A ready local action
   must run before the next network drive.
9. Confirm the incomplete-prefix bound and 65535-byte capacity proof make
   `ProcessBufferFull` unreachable rather than silently mapping it to another
   read.

Useful review searches include:

```sh
rg "BT\.read_more|Common\.TCP\.read|IO\.read" \
  src/impl/TLS13.Impl.Client.Driver* \
  src/impl/TLS13.Impl.Server.Driver*

rg "Common\.BufferedTCP\.Internal" \
  src/impl/TLS13.Impl.Client.Driver* \
  src/impl/TLS13.Impl.Server.Driver*

rg "client_drive|server_drive|drive_until_conclusive|bse_read_auth" \
  common src/impl

rg "record_prefix_incomplete" src/spec src/impl
```

Interpret matches using the extraction/call graph: legacy proof modules may
exist, but live top-level workflows must not call their raw read helpers.

### D. Audit the extracted and unverified boundary

1. Review `TLS13.Impl.Client.Driver.fsti` and
   `TLS13.Impl.Server.Driver.fsti`. Only opaque configuration/driver handles,
   workflow statuses, and top-level lifecycle/send/receive operations should be
   public.
2. Inspect generated headers in `_extract/tls13_bundle`. Proof witnesses,
   raw endpoint APIs, raw receive buffers, and `FStar_SizeT_v` wrappers should
   not appear in the public driver API.
3. Inspect `runtime/tls13_client_driver.c` and
   `runtime/tls13_server_driver.c`. They should not call:
   - `Common_TCP_read`, `Common_TCP_write`, connect/accept/close primitives;
   - client/server `process_network_bytes`;
   - endpoint local-action functions; or
   - buffering internals.
4. Confirm C-side branches only validate inputs, map verified statuses, update
   simple wrapper flags, and release opaque objects through verified facade
   operations.
5. Inspect the Makefile's KaRaMeL input closure and ordering. Interfaces should
   determine the public shape, and obsolete raw driver modules should not
   become extraction roots.
6. Inspect generated C for:
   - no allocation in process/read/commit loops;
   - direct reads into the free suffix;
   - `memmove` compaction only after positive consumption;
   - no copied pending buffer for a borrow/release;
   - no runtime class dictionary or indirect scheduler call; and
   - exact-size zero-copy views for server flight serializers.

## Trusted assumptions and residual risks

The proof does not eliminate every trust assumption:

- F*, Pulse, Z3, KaRaMeL, the C compiler, and their memory/extraction models are
  in the trusted toolchain.
- `Common.TCP.fsti` is an external contract. The socket C implementation must
  actually satisfy its exact history, partial-I/O, EOF, and error semantics.
- Cryptographic external implementations and randomness must satisfy their
  verified interfaces.
- Runtime C argument validation, opaque-handle lifetime, status mapping, and ABI
  layouts remain unverified and must be audited manually.
- The ownership proof assumes API calls are not made concurrently through
  aliased C handles unless a separate synchronization discipline establishes
  exclusive access.
- An authorized read may block forever if a peer sends a valid incomplete
  record and then stalls. The proven property is that the driver never performs
  such a potentially blocking read while current pending bytes can make TLS
  progress or already determine rejection.
- The failed-state receive-log relation is weaker than ordered equality, as
  described above. Failed states are terminal and cannot re-enter the channel
  API.
- Legacy source modules are harmless only while absent from the live facade and
  extraction call graph. This should be checked when the Makefile or top-level
  imports change.

## Challenges encountered and how they were resolved

### Exact accounting was initially too weak

An early relation admitted an ordered subsequence between histories. That could
prove that retained bytes came from TCP without proving that no TCP byte was
dropped. It was replaced with exact concatenation:
`received = committed ++ pending`.

### Exact accounting did not imply safe scheduling

The buffer equations alone said nothing about when a read was allowed. The
exclusive `bse_read_auth` resource and process-before-read state machine were
added so the production read path requires a proof from the immediately
preceding process result.

### Parser failure did not mean incomplete input

`parse_record_wire == None` conflated truncation and malformed complete input.
`record_prefix_incomplete` now captures only prefixes for which additional
bytes can complete the current record. Malformed complete headers reject
without reading.

### TLS processing is relational and effectful

The TLS processor owns mutable connection and output state; it is not a pure
function from bytes to a classification. `process_post` and
`buffered_stream_endpoint` therefore relate pre/post endpoint state, buffer
model, committed history, and output resources instead of wrapping a pure
classifier.

### Higher-order Pulse extraction was unsuitable for the hot path

An extracted generic class loop risked dictionaries, indirect dispatch, and
awkward representations. The reusable generic loop remains the protocol proof,
while small client/server monomorphic loops are verified against the same
predicates and extract to direct calls. This avoids runtime abstraction cost at
the price of one explicit structural-equivalence audit.

### Ghost values could not drive runtime operations

History and model witnesses erase during extraction. Runtime commit, write, and
view lengths therefore come from concrete boxed `SizeT.t` values and views,
with proofs connecting them back to the ghost sequences. No runtime branch or
memory access depends on an erased witness.

### Zero-copy abstract views required separation proofs

Hiding the backing vector while exposing the pending prefix required masked
array split/rejoin proofs. `pending_view` now exposes only read access and must
be released with unchanged contents before compaction or append-read.

### Reconnect/reaccept needed stable storage identity

Simply wrapping a fresh TCP channel would allocate a receive vector on every
connection. Abstract `storage`, `attach`, `close_detach`, `same_storage`, and
the uniqueness lemma preserve one fixed allocation across client reconnects
and server reaccepts.

### `NeedMoreInput` originally discarded too much information

The parser fact was lost before the physical read helper, and state/output
stuttering was not strong enough to construct exclusive read authorization.
Parser, client, and server postconditions were strengthened to carry the
incomplete-prefix witness and unchanged state/output facts to the endpoint
instance.

### Full-buffer behavior needed a semantic bound

The generic buffering protocol must handle `NeedMore` with no free space. TLS
proves this impossible using the maximum accepted record length and the larger
receive capacity. The branch is represented as false terminal ownership rather
than an unsafe zero-length read or an unproved assertion.

### Server serializers required exact output objects

The server initially passed a large-capacity network array to serializers whose
contracts and implementations require exact message-sized arrays. Extracted
interoperability exposed the mismatch. Verified zero-copy prefix views now give
each server flight serializer the exact required length.

### Extraction leaked proof-oriented representations

Proof witnesses and `nat`-shaped scheduler values initially appeared in
generated APIs, including unwanted `FStar_SizeT_v` representations. Proof-only
values were erased and concrete scheduler consumption was changed to
`FStar.SizeT.t`.

### KaRaMeL input ordering affected abstraction

KaRaMeL declaration deduplication made input closure and order significant:
concrete declarations could survive where an abstract interface was intended.
The extraction manifest was corrected so the restrictive interfaces and live
top-level facade determine generated declarations.

## Validation anchor

The implementation described here is the one gated by:

```sh
make -j128 verify test
```

That gate covers F*/Pulse verification, extraction/build, and the repository's
interop/regression tests. The latest full benchmark and interoperability report
for this design is:

```text
benchmark-results/20260724T004921Z/report.md
```

Performance and interoperability tests are evidence against extraction and ABI
mistakes, but they are not substitutes for auditing the exact sequence
equalities, state-machine correspondence, and linear read authorization
described above.
