# TLS server verification status

Status date: 2026-06-17.

## EverParse Merge Status (2026-06-17)

**Branch:** `tls_server_merge`  
**Status:** Phase 3 in progress (verification at 95%)

The `origin/main` branch has been merged, bringing EverParse/QuackyDucky integration for verified TLS message parsing. This eliminates client-side parser/serializer code from the TCB.

**Completed:**
- ✅ Phase 1: Merged origin/main with all conflicts resolved
- ✅ Phase 2: Built full EverParse toolchain (fstar.exe 77MB, krml 37MB, qd.exe 8.8MB)
- ✅ Generated 65+ TLS13.Wire.Generated.* modules from tls.qd.rfc
- ✅ Verified all generated modules
- ✅ Verified 140+ main codebase modules

**In Progress (Phase 3):**
- ⚠️ 2 temporary admits in TLS13.Impl.Parser.DecoderWF.fst (proofs broken by message type changes)
- 🔄 Full verification running
- ⏳ Interop tests pending

**Remaining:**
- Phase 4: Update documentation (TCB boundaries)
- Phase 5: Implement verified server parsers using generated combinators (8-16h estimated)

See MERGE_PHASE2_COMPLETE.md for detailed status.

## Goal

The end goal is a verified, interoperable TLS 1.3 client/server implementation for
the repository's first supported profile:

- TLS 1.3 only.
- X25519 key exchange.
- `TLS_CHACHA20_POLY1305_SHA256`.
- Certificate-based server authentication using `RsaPssRsaeSha256` or
  `EcdsaSecp256r1Sha256`, whichever the configured credential's key supports.
- No PSK, 0-RTT, HelloRetryRequest, client authentication, resumption, early
  data, or KeyUpdate in the first milestone.

## Parity with the client

The client has since moved past that first profile: it negotiates
`TLS_AES_128_GCM_SHA256` as well as ChaCha20-Poly1305, offers and completes
`secp256r1` as well as X25519, and reassembles a handshake message split across
several records.

The server now matches it on the first of the three: it selects
`TLS_AES_128_GCM_SHA256` when a peer does not offer ChaCha20-Poly1305, via the
deterministic policy `TLS13.Impl.ConnectionState.Model.server_selected_suite`
(prefer ChaCha20, fall back to AES-128-GCM), which is a function of the stored
ClientHello alone, so the ServerHello writer recovers the choice at runtime
rather than having it threaded through the driver.  `secp256r1` and cross-record
reassembly remain server-side gaps.

`secp256r1` is being closed in staged, capability-neutral steps against the
file-and-line plan in `docs/server-p256-plan.md`; the configured
`server_supported_groups` stays `[T.X25519]` until the last of them, so no stage
before that can move a matrix cell.  The first has landed: the server's
selection now carries a per-group keypair and its self-consistency invariant is
group-indexed rather than X25519-specific.  The second has landed too: the
concrete ClientHello mirror now carries a 65-byte secp256r1 key-share slot
alongside the X25519 one, so the remaining stages can fill it without further
structural churn.  Accepting a P-256-only ClientHello (widening the parser's
acceptance gate) was measured to be 169 `ch_extensions` occurrences of work
that buys no capability while the configured groups are X25519-only, so it was
deferred to the stage that actually turns the feature on.  The third has landed:
because an X25519 private key and a P-256 private key are both thirty-two bytes,
and a server runs exactly one ECDH, a single secret derives both publics -- so
the selection now carries a real secp256r1 keypair with no extra randomness and
no change to the driver's payload width.  The fourth and fifth landed together:
the *specification* is now fully group-parametric, recovering the group from the
ServerHello where one exists and from the selection where it does not, exactly
as the client already does.  The implementation still only ever selects X25519,
and now says so through a single named predicate,
`server_selection_group_pinned`, whose deletion is the switch that turns the
feature on in the final stage.

Four more capability-neutral halves have landed since.  The parser reads a
secp256r1 key share, as a *second pass* over the ClientHello's extensions rather
than a wider `scan_ch_extensions` -- the existing scan carries an eight-tuple
loop invariant over nine mutable references, and the specification defines
`clientHello_key_share_secp256r1` as an independent walk anyway, so the second
pass mirrors the specification's own structure.  The ServerHello writer now
builds its group tag and its share from the selection rather than from the
constants `X25519` and the 32-byte X25519 public.  The negotiated group became
observable at run time: it is genuinely *not* recoverable from what the server
already stores -- the mirror's group tag describes a ServerHello, which does not
exist yet, and an all-zero X25519 share is a legal share -- so it joins the
ClientHello metadata as a box, alongside the session-id width, carrying a
deterministic policy (prefer X25519 when offered, else secp256r1) that is a
function of the stored ClientHello alone.  And the peer's secp256r1 offer is now
observable end-to-end: the mirror's invariant states the stored bytes, an offer
at a length other than 65 is simply no offer rather than a parse failure
(RFC 8446 4.2.8), and the client's own mirror caught up with the fact that its
canonical ClientHello has always offered two key shares.

The elliptic-curve arithmetic itself is now group-parametric on the server:
it reads the negotiated group off that box and dispatches through `TLS13.KEX`,
so the secp256r1 arm is compiled, linked and reachable.  The server's mirror
needed its own entry point, because it stores the ClientHello's *offer* -- which
may carry both groups at once, in a 32-byte slot and a 65-byte slot side by side
-- rather than the single share the client's mirror keeps padded to a uniform
width.  Its *specification* has since caught up: what that routine derives is
now stated as the group-indexed ECDH at whichever group the selection names,
rather than as X25519's.  That cost nothing, because the body had been proving
the general statement all along and then specialising it back down; the
specialisation is simply gone.  Its *precondition* still pins X25519, and has to
(see below).

What is left is one indivisible commit, and the reason is precise: the
acceptance gate is exactly what makes the negotiated group a constant.  The
moment a ClientHello without an X25519 share is accepted, the ECDH, the
selection policy, the ServerHello length arithmetic and the configured group
list all face a group they cannot yet handle, with no runtime rejection path to
fall back on -- so they must move together.  The ServerHello's length arithmetic was
thought to resist pre-staging, on the grounds that the transparent canonical
builder the whole write path is defined against pins the group tag and the
thirty-two-byte share width in the same declaration.  That is true, and it is
also beside the point: the two have to move *together*, but moving them together
is still capability-neutral so long as every caller keeps passing X25519 and a
thirty-two-byte share.  So it has now been pre-staged.  The canonical builder
takes the group as a parameter, and the size lemma reads

    58 + |key_share| + |legacy_session_id_echo|

which is the familiar `90 + |sid|` at X25519's thirty-two-byte share and
`123 + |sid|` at secp256r1's sixty-five-byte one.  Nothing about that proof was
X25519-specific once it was written down properly: a `namedGroup` is a two-byte
enum at *every* group, which its parser kind already says, so the group tag
contributes a constant and drops out of the arithmetic entirely.

The Pulse write chain above that arithmetic has since been pre-staged too, and
it turned out to cost less than the plan predicted.  The plan assumed the writer
would need the share width threaded down to it as a new runtime argument from
the send path.  It does not: the concrete ServerHello mirror the writer already
holds has always recorded the negotiated group, beside a sixty-five-byte padded
share slot, so the writer recovers both the wire tag and the width from data in
its own hand.  All four levels of the chain therefore gained only an *erased*
group; not one concrete parameter list changed.  A second small win came with
it -- the record writer had been sizing its handshake-fragment buffer as
`90 + |sid|`, and now sizes it as `record_length - 5`, which is exact at any
share width and needs no lookup at all.  The one new obligation is that the
canonical ServerHello's key share round-trips through the wire semantics at a
variable group; as first written that claim was false, because the semantics
reject an unrecognised group outright, so it is stated for the two groups ATLAS
offers and proved by cases.

What is left for the final commit is the acceptance gate, the selection policy,
the configured group list, the ECDH's precondition, and the send path's own
`90`/`95` constants, which are pinned by the selection witness and move with it.

Two of those five have since shrunk sharply.  The acceptance gate had been
measured at a hundred and sixty-nine occurrences of work; it is now one
expression.  The scan that decides whether a ClientHello is representable kept
its key-share accumulator at the type "thirty-two bytes", which is the only
X25519-specific thing about it and which forced every statement made over the
scan to be X25519-specific too.  The obvious fix -- keep the bare share and
recover the group from its length -- is exactly what this codebase's own design
law forbids, so the accumulator instead became a *tagged* pair, the same shape
the ServerHello side already uses.  The body still calls the X25519 finder, so
acceptance is bit-identical and no cell moved; but the finder is now a single
replaceable expression rather than a type woven through five files.

The ECDH's precondition, by contrast, was tried and is genuinely part of the
flip.  Replacing its X25519 pin with the honest statement -- that the selected
group is the one the server's policy picks for this ClientHello -- verifies
cleanly through all five layers above it, including the canonical queries and
the scheduler.  It fails in exactly one place: the routines that *build* a
selection cannot prove the policy picks X25519, because that needs the fact that
the stored ClientHello offered an X25519 share, and that fact lives only in the
runtime mirror, not in any specification-level invariant.  The resolution is not
to surface the fact but to stop needing it: once a builder sets the selected
group *from* the policy instead of to the literal X25519, the agreement holds by
definition.  That is a behaviour change, so it belongs to the flip.

Two further capability-neutral halves have landed.  The abstract ServerHello the
whole send path is stated against -- the last thing in the write chain that was
still X25519-shaped -- now takes the group as an argument and accepts a share of
any offered width, and its size lemma reads `58 + |share| + |echo|`, the same
`90 + |echo|` as before whenever the share is X25519's thirty-two bytes.  And
the two runtime facilities the flip needs now exist: a group-agile derivation of
the server's *own* share, which is the build-direction mirror of the agile ECDH
and branches on the same explicit tag rather than on a length; and a query that
reads the negotiated group out of the ClientHello mirror.

The model-level size arithmetic has since followed the witness: the canonical
ServerHello's bytesize lemma now reads `58 + kex_public_len g + |sid|` too, and
that generalisation was *free* -- the proof already went through the
group-parametric accessors and merely asserted them back down to X25519
afterwards, so two lines were deleted and nothing was added.  Because
`kex_public_len` is a total match on a two-constructor type it still reduces to
thirty-two definitionally, and the lemma's two consumers in the whole tree kept
deriving `90 + |sid|` untouched.

That fixes the order the rest has to go in, which is worth stating because the
reverse is tempting and does not work: the length arithmetic must generalise
**before** the selection policy does.  The moment the selection stops naming a
literal group, the `90` is underivable at every site that states it, so a commit
that flipped the policy first would be repairing arithmetic under a broken tree.

Two further measurements then re-partitioned what is left, and both make it
smaller and better understood.  The first is that the concrete share buffer is
barely a concern: the driver calls the entry point that takes the server's
*private* key, and a private key is thirty-two bytes at both groups, so no
driver module is on that path at all -- only a stack-local in the send path and
one signature widen to sixty-five bytes.  The second is the corollary: the
buffer was never what made the rest indivisible.  The real coupling is the two
dozen statements of `95 + |session id|`, which are keyed on the *connection
state* rather than on the selection.  Their group is a function of the stored
ClientHello, and that is provably X25519 only from the acceptance gate's own
clause -- not from the pure part of any postcondition.  So unlike the
selection-keyed arithmetic just moved, they cannot be staged capability-neutrally
and have to travel with the gate.

What remains is therefore one more capability-neutral step -- widen that buffer
-- and then one behavioural commit: widen the acceptance gate, have the
selection builders take the group from the policy and the share from the new
derivation, generalise the state-keyed lengths, drop the ECDH's X25519
precondition and the named pin that records it, offer secp256r1 in the
configured group list, and flip the two ledger cells.  Every one of those is a
*deletion* or a substitution of an expression that already exists; none is a
restatement.  `docs/server-p256-plan.md` §7 carries the file-and-line
breakdown.

Cross-record reassembly -- one ClientHello arriving as two TLS records -- is
still refused, and the obstacle has now been located precisely rather than
estimated.  It is *not* the decoder, and it is not
`process_client_hello`: that routine takes the raw delta and the handshake
fragment as two separate arrays and constrains them independently, so it never
asks that the fragment be one record's worth of the raw.  The obstacle is one
layer above the record layer.  `TLS13.Spec.Endpoint.Wire.wire_message` carries a
proof field pinning its raw bytes to a single parsed record, a network step
consumes exactly one such message, and the server driver's whole correctness
statement is phrased against that class through
`TLS13.Impl.Server.CanonicalProtocol` -- a module on the driver's critical path,
not a standalone theorem.  **One protocol step consumes exactly one TLS record**
is therefore the invariant that has to give.

Widening the state machine's ClientHello arm to admit a split -- as a
disjunction, so that only proofs which *invert* the predicate can break -- was
built and put through a full verify: two failures, one benign and one at exactly
that boundary.  That measurement makes the choice of design clear.  The right
shape is the one the client uses on its protected path: a *buffering step* that
takes delivery of one record and sets its bytes aside without interpreting them,
so that one step is still one record and the message is emitted only once the
buffer holds a whole one.  It is the larger diff and the smaller blast radius,
because the wire class, the canonical protocol refinement and the cross-endpoint
pairing theorems all keep their present shape.

It is worth being exact about what "the client already does this" means, because
the obvious reading is wrong and it makes the work look like plumbing.  The
client's buffering is confined to the **protected** path and to the stages after
ServerHello; a ServerHello split across two records would be refused by the
*client* exactly as a ClientHello is by the server, and there is no cleartext
buffering anywhere in the tree for either role.  The reason the client's step
cannot simply be re-pointed is structural rather than a matter of its
role guard: the protected event carries *bytes* -- a fragment with an offset and
a consumed count -- so one-record-one-message was already broken there by
construction and reassembly cost a single extra field.  The cleartext event
carries an already-*parsed* message, and the message parser requires the record
to be consumed exactly, so a cleartext record simply *is* one whole message and
there is nowhere to put a partial one.  Giving the server reassembly means
introducing bytes into that event, which is a new event shape rather than a new
field.  There is also a security difference that the cap has to carry: the client
only ever buffers plaintext that has already been authenticated under the
handshake keys, whereas a server buffering a ClientHello is accumulating bytes
from an unauthenticated peer.  `docs/server-client-parity.md` carries the full
argument and both routes with their costs.

The server also echoes the offered `legacy_session_id` **verbatim**, as
RFC 8446 4.1.3 requires, rather than padding it to 32 bytes: the mirror carries
the id as a zero-padded 32-byte buffer plus an explicit width, and the
ServerHello is `90 + |sid|` bytes (its record `95 + |sid|`), sized at run time.
A peer with middlebox-compatibility mode off -- which sends an empty session id
-- therefore now connects.

Server credentials are no longer pinned to RSA-PSS.  The signature scheme the
server both *allows* and *signs under* is
`TLS13.Crypto.Spec.credential_signature_scheme` of the credential it was
configured with, so an ECDSA P-256 credential negotiates and signs
`ecdsa_secp256r1_sha256` while an RSA credential negotiates and signs
`rsa_pss_rsae_sha256` -- and either one correctly refuses an offer its own key
cannot satisfy.  The wire code written into CertificateVerify comes from the
same credential (`TLS13.OpenSSL.server_credential_signature_scheme`), so the
model-level scheme and the byte on the wire cannot drift.

`docs/server-client-parity.md` is the authoritative gap analysis and interop
test plan.  Two standing gates keep it honest:

- `make test-atlas-loopback` -- the verified client against the verified server.
  The only test in the tree whose ClientHello is the one ATLAS actually sends,
  so it is the gate that fails if the client's offer moves past what the server
  can select.
- `make test-server-matrix` -- the server's capability surface across cipher
  suites, key-exchange groups, signature schemes, the server's own credential
  (RSA or ECDSA P-256), middlebox-compatibility mode, record/TCP framing and
  protocol version.  Thirty-four cells with two-sided expectations: a cell
  recorded as a gap fails if it starts succeeding, so closing a gap must update
  the ledger.  Gaps claimed to be independent of an axis are recorded twice
  (`ecdsa-credential-p256-only`, `aes128-clienthello-across-two-records`) so
  that a fix which closes one only on one axis is visible as such.
- `make test-client-record-split` -- the mirror of that matrix's framing axis,
  run in the server->client direction.  Three cells with two-sided
  expectations: two controls (`passthrough`, `serverhello-tcp-dribble`) that
  keep the harness honest, and `serverhello-across-two-records`, recorded as
  refused.  It measures the client half of the cross-record handshake
  reassembly gap, which was previously only asserted in prose.

All three are part of `make test`, and therefore of CI.

The proof goal has two connected layers.

1. **Spec-level agreement**: the role-parametric TLS state-machine spec should
   prove that paired client/server endpoints derive equal peer read/write key
   material for each supported derived key, provided their ClientHello,
   ServerHello, X25519 shares, transcript checkpoints, and key-schedule lineage
   agree.
2. **Pulse implementation conformance**: the extracted implementation should
   refine the spec from concrete raw network bytes through parsing,
   serialization, transcript evolution, record protection, IO logs, and local
   TLS state-machine events. The top-level server should expose a practical
   buffer/driver-oriented API with external network IO, and the extracted C
   server/client should interoperate on the supported profile.

## Current authoritative plan

`TLS_SERVER_DESIGN_AND_IMPL.md` is the authoritative plan. It supersedes the
older server/transcript planning documents.

## Committed verified status

The latest committed verified server-driver, client-driver, and pairing-theorem
baseline is:

```text
85c7e47 Clarify public-success pairing theorem name
```

At that point the full gate had passed:

```text
git --no-pager diff --check
make check-admits
make verify
make test-extracted-client-driver-slice
make test-extracted-server-driver-slice
make test-openssl-echo
make test-openssl-sclient
```

That committed state includes:

- A role-parametric pure TLS state machine with server role/configuration,
  server handshake stages, server local/network event vocabulary, and server
  transitions through ServerHello, the encrypted server flight, Finished,
  application key installation, application data, alerts, and close_notify.
- Spec-level derived-key agreement vocabulary and theorems in
  `src/spec/TLS13.ConnectionState.Lemmas.fst`, including:
  - `lemma_paired_endpoints_derived_key_agrees`;
  - `lemma_paired_x25519_key_shares_shared_secret_agree`;
  - `lemma_paired_x25519_key_shares_derived_key_agrees`;
  - `lemma_supported_profile_client_server_key_material_agrees`, the aggregate
    supported-profile theorem for all first-milestone derived key material and
    installed peer record key/IV directions.
- Verified public server wrappers for the important local/network state
  mutations, including ClientHello receive, supported selection, shared-secret
  derivation, ServerHello send, handshake/application key installs,
  EncryptedExtensions, Certificate, CertificateVerify, ServerFinished,
  client-Finished verification, application data, and close_notify.
- A server driver with raw-byte IO-history preservation through:
  - TCP listen/accept/start;
  - retained-buffer read/process/compact;
  - `NeedMoreInput` network retry;
  - read until `ClientHello`;
  - driver-owned `server_random || server_private_key` generation;
  - supported-profile selection and X25519 shared-secret derivation;
  - exact cleartext ServerHello emission;
  - a fueled empty-action local drain.
- The composed driver entry
  `accept_start_read_client_hello_select_derive_send_server_hello_drain_empty_once`,
  which accepts TCP, starts the server, reads through ClientHello, selects and
  derives the shared secret, emits the matching cleartext ServerHello, and then
  drains scheduler-supported empty local actions. This advances the executable
  driver beyond ServerHello into scheduler-driven payload-free actions, while
  still stopping at credential-bearing actions.
- Since that baseline, the public server facade has been hardened: `accept`
  reaches application-data control on `ServerWorkflowOk` and now exposes
  `server_driver_application_ready`, including
  `ST.server_end_to_end_invariant` and
  `CS.application_record_keys_installed_for_role CS.ServerEndpoint`. The public
  `receive` spec is also tied to the concrete app-output buffer and returns
  `ServerWorkflowOk` exactly when the copied application bytes fit the caller
  and driver buffers. Public `close` now requires the same application-ready
  state exposed by successful `accept`, sends verified `LocalSendCloseNotify`
  via the local-write theorem, and then closes the transport.
- Concrete extracted client/server validation passes for the current facades:
  `make test-extracted-client-driver-slice`, `make test-openssl-echo`,
  `make test-extracted-server-driver-slice`, and `make test-openssl-sclient`
  all complete successfully, including real OpenSSL interop in both directions,
  application echo, and close paths.
- The client top-level driver facade is being hardened symmetrically: successful
  `TLS13.Impl.Client.Driver.connect` now exposes
  `client_driver_application_ready`, proving the connected client state is in
  `ControlApplicationData`, preserves `CT.client_end_to_end_invariant` through
  the recursive Pulse handshake orchestration, and has role-correct client
  application record read/write keys installed.

## What is not complete yet

We do **not** yet have the final verified interoperable server.

The main spec-level key-material agreement theorem is now packaged as an
aggregate supported-profile theorem, and `TLS13.Impl.Driver.Pairing` now provides
the audit-facing driver-pair bridge theorem:
`lemma_client_server_driver_key_material_agrees`. It also provides the explicit
no-read-ahead bridge
`lemma_paired_wire_logs_from_exact_prefix_no_read_ahead`, which upgrades the
public ordered received-prefix facts to full `CS.paired_wire_logs` when each
transport receive history has no retained suffix beyond the protocol
`raw_received` log. Successful public client `connect` and server `accept` now
also expose that no-read-ahead fact. The clearer wrapper
`lemma_client_server_driver_key_material_agrees_from_public_success_components`
takes those public success facts plus the remaining semantic state inputs and
returns historical derived-key agreement, the aggregate key-material input
predicate, exact paired transport/protocol wire logs, and final
`CS.supported_profile_client_server_key_material_agrees`.

What is still missing is the concrete paired-resource theorem that keeps
`paired_transport_histories` as an explicit environment precondition and
establishes the remaining semantic state inputs for live runs: paired X25519
shares, paired transcript checkpoints, and precise current application
record-state facts. The last category is intentionally still explicit:
successful application readiness proves role-correct application record keys are
installed, but it does not yet prove the record epoch/current application
traffic material facts needed by the aggregate record-material theorem,
especially in the presence of post-handshake KeyUpdate behavior.

On the Pulse implementation side, public server `accept` and client `connect`
now both expose application-data readiness on success, exact sent-log equality,
ordered received-prefix facts, and no-read-ahead success facts. Public
client/server `send` operations expose exact local-write sent-log append facts;
public client/server `receive` operations expose exact successful app-output
copyout facts; and public client/server `send`/`receive`/`close` operations
expose the pre-call wire-log projections hidden inside the connected driver
resource. Public client/server `close` operations expose verified
`close_notify` local-write facts before transport shutdown. The remaining
implementation-side gaps are:

- package a concrete paired-run theorem over successful client/server resources
  that takes `paired_transport_histories` as an environment precondition and
  supplies the semantic state inputs required by
  `lemma_client_server_driver_key_material_agrees_from_public_success_components`;
- continue splitting the remaining public driver orchestration into smaller
  `Driver.Handshake`/`Driver.App` modules with narrow `.fsti` boundaries;
- strengthen the private client receive workflow with a factored network-loop
  theorem, analogous to the server `Driver.Network` boundary, so public receive
  can expose the whole workflow theorem rather than only the exact status and
  copyout facts.

## Latest verified in-progress slice

The client facade readiness slice strengthens `connect`. It adds
`client_application_record_keys_installed_runtime` in
`TLS13.Impl.ConnectionState.Queries` and uses it in
`TLS13.Impl.Client.Driver.connect`, so `DriverWorkflowOk` is no longer merely a
connected transport result: it proves application-data control, the client
end-to-end invariant, and installed client application record keys. Focused
verification for
`TLS13.Impl.ConnectionState.Queries` and `TLS13.Impl.Client.Driver` passes, as
do the extracted client driver slice and OpenSSL echo interop tests.

The follow-on client facade slice strengthens public `send`: its postcondition
now exposes `client_driver_send_correct`, tying the returned status to the
verified `LocalSendApplicationData` theorem and proving the transport sent log
is exactly the old sent log appended with the emitted TLS record bytes.

The next client facade slice strengthens public `receive`: its postcondition now
exposes `client_driver_receive_correct`, tying the returned status to the actual
driver workflow status, response app length, and output-buffer capacity split;
on success the caller's output prefix is exactly `CT.response_app_out` from the
driver's concrete app-output buffer.

The latest client facade slice strengthens public `close`: its postcondition now
exposes `client_driver_close_correct`, tying the returned status to a verified
`LocalSendCloseNotify` theorem and exact close-notify sent-log append before the
TCP channel is closed.

The latest theorem-bridge slices add `TLS13.Impl.Driver.Pairing`, which packages
the public client/server application-readiness facts, exact/no-read-ahead
transport log facts, paired transport histories, and explicit semantic
state-machine components into checked bridge theorems. The most audit-facing
entry point is
`lemma_client_server_driver_key_material_agrees_from_public_success_components`;
it proves historical derived-key agreement, the aggregate key-material input
predicate, exact paired wire logs, and
`CS.supported_profile_client_server_key_material_agrees`.

The latest facade-accounting slices expose public
`client_driver_received_log_accounted` and
`server_driver_received_log_accounted` predicates on connected public operations,
and public `send`/`receive`/`close` postconditions expose the pre-call sent-exact
and received-accounted projections hidden inside the connected driver resource.
Successful `connect`/`accept` additionally expose ordered exact-prefix and
no-read-ahead facts, so the pairing bridge can upgrade those success states to
full protocol/transport receive equality.

## Remaining proof gaps

1. **Concrete client/server agreement bridge**
   - Connect concrete client and server driver post-states to the existing
     spec-level paired endpoint predicates.
   - Use the existing derived-key agreement lemmas once the concrete transcript
     and key-share agreement hypotheses are established from wire logs.

2. **Exact received-log pairing**
   - The current driver predicates expose exact sent logs and public received
     accounting, but received transport logs may include retained read-ahead and
     rejected consumed bytes. The next strengthening must carry an ordered
     accepted-prefix/no-rejected/no-retained fact, not just length/count
     accounting, before it can prove exact peer sent/received equality.
   - Both immediate theorem-surface obligations for that strengthening are now
     discharged. Shared spec lemma
     `lemma_legal_connection_delta_local_fail_control_failed` and client/server
     response lemmas expose that `LocalFail`-based decode-error,
     unexpected-message, and bad-Finished responses leave the connection in
     `ControlFailed`. New client/server network predicates
     `network_bytes_nonfailed_received_prefix_accepted` and
     `server_network_nonfailed_received_prefix_accepted` prove that a non-failed
     network step with nonzero consumed input records the consumed prefix as the
     accepted protocol raw-received delta. Driver-side helper lemmas now prove
     exact received-log append for such non-failed network steps when the prior
     consumed transport prefix was exact.
   - The exact-unless-failed property is now folded into the hidden client/server
     driver wire-log witnesses: in every non-failed state, the protocol
     `raw_received` log must be exactly the consumed transport prefix, while
     failed states still retain the weaker accounting relation needed for
     rejected consumed bytes.
   - Successful public client `connect` and server `accept` now expose ordered
     exact-prefix received-log facts, and `TLS13.Impl.Driver.Pairing` composes
     paired transport histories with those facts into a checked
     `paired_protocol_received_logs_exact_prefix` theorem.
   - `TLS13.Impl.Driver.Pairing` also exposes
     `lemma_client_server_driver_key_material_agrees_from_prefixes`, which uses
     those ordered-prefix public facts plus the existing supported-profile
     state-machine input predicate to prove
     `CS.supported_profile_client_server_key_material_agrees` without requiring
     impossible full TCP-history equality in the presence of retained read-ahead.
   - Successful public client `connect` and server `accept` now also expose
     `client_driver_received_no_read_ahead` and
     `server_driver_received_no_read_ahead`: `ServerWorkflowOk` /
     `DriverWorkflowOk` only return on application-ready states whose retained
     input buffer is empty, so the concrete transport receive length equals the
     protocol `raw_received` length.
   - `TLS13.Impl.Driver.Pairing` now also exposes
     `lemma_endpoint_transport_received_exact_from_prefix_no_read_ahead` and
     `lemma_paired_wire_logs_from_exact_prefix_no_read_ahead`: if each endpoint's
     concrete receive history has the same length as its protocol `raw_received`
     log, the ordered-prefix facts collapse to exact transport/protocol
     equality and yield full `CS.paired_wire_logs`.
   - `lemma_client_server_driver_key_material_agrees_from_no_read_ahead` now
     consumes the public application-ready, sent-exact, received-prefix, and
     no-read-ahead facts plus paired transport histories to prove both full
     `CS.paired_wire_logs` and
     `CS.supported_profile_client_server_key_material_agrees`.
   - `client_server_driver_supported_profile_state_inputs` now names only the
     remaining paired semantic state-machine obligations: paired X25519 key
     shares, paired transcript checkpoints, and precise current application
     record-state facts: each endpoint's installed application traffic slots
     match the expected derived key/IV material, and each current read/write
     record direction is at the application epoch. Handshake traffic-key
     agreement remains part of the historical derived-key theorem, while the
     current record-state component is application-only so the application-ready
     theorem surface does not require one endpoint record state to be
     simultaneously at handshake and application epochs. Key-schedule lineage is
     no longer caller-supplied at this bridge:
     `lemma_client_server_driver_supported_profile_derived_key_material_agrees`
     now proves the full historical derived-key agreement theorem from public
     application-ready success plus only paired X25519 shares and transcript
     checkpoints, deriving client/server lineage from endpoint reachability and
     role-correct installed application record keys. The aggregate bridge
     `lemma_client_server_driver_supported_profile_key_material_inputs_agree`
     reuses that derived-key theorem and calls the pure
     `lemma_supported_profile_application_record_material_inputs_agree_from_expected`
     bridge to turn those precise current application record-state facts into
     `supported_profile_application_record_material_inputs_agree`. The component theorem
     `lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components`
     proves the aggregate spec input predicate plus the same wire-log and
     key-material conclusions from those explicit components, and
     `lemma_client_server_driver_key_material_agrees_from_public_success_components`
     exposes the same result under an audit-facing public-success name while
     also returning the historical derived-key agreement fact explicitly.
   - `client_driver_application_ready` is now symmetric with
     `server_driver_application_ready` at the invariant layer: it includes the
     client end-to-end invariant, threaded through the Pulse handshake and
     receive helper postconditions.
   - The remaining proof work is to prove the paired supported-profile
     state-machine components from two live successful driver resources, rather
     than requiring them as external theorem premises. Key-schedule lineage is
     now discharged by a pure reachability-shape invariant plus installed
     application keys, and the driver-level derived-key theorem is independent
     of record-material agreement; paired X25519 shares, transcript checkpoints,
     installed application traffic slots matching expected derived material, and
     current application record epochs still need dedicated paired-state
     projection lemmas.

3. **Extraction and interoperability**
   - Keep the public API buffer/driver oriented.
   - Extract the verified server path to C.
   - Validate against the supported client/server profile with concrete
     certificates and network IO.

## Recommended next steps

1. Prove each remaining component of
   `client_server_driver_supported_profile_state_inputs` from successful paired
   driver resources: X25519 shares, transcript checkpoints, installed
   application traffic slots matching expected derived material, and current
   application record epochs.
2. Package those component proofs into a concrete driver-pair theorem that
   instantiates
   `lemma_client_server_driver_key_material_agrees_from_no_read_ahead_components`.
3. Re-run extraction and interop tests after each C-facing facade change.

## Engineering note

`TLS13.Impl.Server.Driver.fst` is still large. New work should prefer small
modules and `.fsti` boundaries, following the client-side factoring style. The
largest remaining risk is not the cryptographic theorem itself; it is keeping
the Pulse orchestration proof modular enough that scheduler readiness,
credential resources, raw-byte IO logs, and exact state transitions remain
usable without long verifier iterations.
