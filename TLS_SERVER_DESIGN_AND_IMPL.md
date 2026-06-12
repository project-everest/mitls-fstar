# TLS 1.3 server design, proof, and implementation plan

## Authoritative status

This is the single authoritative plan for adding a verified TLS 1.3 server to
this repository. It covers the supported server profile, the pure
role-parametric state-machine design, the client/server derived-key agreement
theorem family, the server Pulse implementation strategy, the runtime/TCB
surface, and the validation checklist.

The plan is intentionally spec-first. Server Pulse handlers, drivers, and C
runtime work should not begin until the pure state machine has enough role
precision to state and prove the main client/server derived-key agreement
theorems. Once those theorems are settled, the Pulse implementation should be a
mostly mechanical refinement of the already-audited pure transitions, following
the existing client implementation structure.

## End goal

Build a verified TLS 1.3 server for the same narrow profile as the verified
client:

- TLS 1.3 only.
- X25519 key exchange.
- `TLS_CHACHA20_POLY1305_SHA256`.
- Certificate-based server authentication.
- First server credential scheme: `RsaPssRsaeSha256` (`0x0804`).
- No PSK, no 0-RTT, no HelloRetryRequest, no client authentication, no early
  data, and no resumption in the first implementation.
- Application data, close_notify, and KeyUpdate only if they stay aligned with
  the current supported client profile.

The main proof target is two-layered:

1. **Local endpoint correctness**: each server API step preserves a
   calc-sample-style layered invariant from concrete raw buffers through parsed
   TLS records/messages, transcript and key schedule evolution, state-machine
   events, record keys, wire logs, and application-log projection.
2. **Client/server derived-key agreement**: for each supported protocol-derived
   key identified by a `derived_key_id`, paired client and server states derive
   equal peer read/write material when their derivation inputs agree.

## Non-goals for the first server milestone

The first server version should deliberately omit:

- PSK, 0-RTT, early data, and resumption.
- HelloRetryRequest.
- Client authentication.
- ALPN or non-empty EncryptedExtensions unless interop forces it.
- Multiple simultaneous accepted connections in one verified server object.
- A verified generic serializer for arbitrary TLS messages.
- A broad runtime C server that owns TLS scratch buffers or handshake polling.

## Current client and shared baseline

The current verified client path is the regression baseline. Every server
milestone must keep it green.

Shared or intended-to-be-shared layers:

| Layer | Reuse target | Server-specific work |
| --- | --- | --- |
| Pure messages | `TLS13.Messages`, most of `TLS13.Wire.Spec` | Strengthen server-side parse/serialize facts and ClientHello acceptability predicates. |
| Low-level messages | `TLS13.Impl.Messages` L-level message representations | Add construction/copy helpers only where needed for server messages. |
| Record layer | `TLS13.Record`, `TLS13.Record.Spec` | Prove role-correct server read/write projections. |
| Key schedule | `TLS13.Keys`, `TLS13.KeySchedule` | Add role-indexed traffic-label and derived-key theorem vocabulary. |
| Logs | `TLS13.ConnectionLog` raw sent/received streams and app projections | Add server trace projections and paired endpoint relations. |
| Parser | Existing TLS parser decodes ClientHello and other messages | Move role-neutral parse contracts out of client theorem modules where needed. |
| Serializer | Existing serializer hooks and C backend | Add fixed server builders with parse-back, transcript, and seal facts. |
| Pure connection model | `TLS13.Spec.ConnectionState` is currently client-shaped | Generalize roles, stages, key projections, transcript checkpoints, and endpoint pairing. |
| Pulse state | `TLS13.Impl.ConnectionState.Repr` is client-oriented but contains reusable storage patterns | Reuse storage where genuinely endpoint-neutral; add server credential/selection fields. |
| Driver pattern | Client driver retained-buffer, compaction, IO-history, and total-write patterns | Reuse for a single-connection server driver with listen/accept and signing. |
| TCBs | Crypto, AEAD, TCP read/write/close | Add typed listen/accept IO and server credential/signing TCBs. |

The client theorem surface that the server should mirror:

- extracted buffer/event API over a connection object;
- `process_network_bytes`-style network input step;
- `process_local_event`-style local action step;
- response predicates with exact network/app output slices;
- state correctness and end-to-end invariants;
- raw received decode and raw sent seal replay facts;
- record read/write key schedule projections;
- driver-level IO history relation for transport bytes versus protocol wire logs.

Current code anchors to preserve or factor:

- `src/spec/TLS13.Transcript.fst` defines `TLS13.Transcript.transcript` as raw
  bytes, with append and SHA-256 hash operations.
- `src/spec/TLS13.Spec.ConnectionState.fst` contains the client-shaped pure
  state machine, including `append_handshake_to_transcript`,
  `conn_event_transcript_delta`, `transcript_bytes_of_conn_events`,
  `connection_state_transcript_consistent`, `LocalDeriveSharedSecret`,
  `LocalInstallTrafficKeys`, `expected_traffic_secret`,
  `traffic_install_matches_key_schedule`, and
  `traffic_key_material_for_secret`.
- `src/spec/TLS13.Keys.fst` contains the deterministic schedule functions:
  `early_secret B.empty`, `handshake_secret early shared`, `master_secret
  handshake`, `client_handshake_traffic_secret`,
  `server_handshake_traffic_secret`, `client_application_traffic_secret`,
  `server_application_traffic_secret`, `derive_aead_key`, and
  `derive_aead_iv`.
- `TLS13.Crypto.Spec.fsti` exposes `x25519_public_from_private` and
  `x25519_shared`, but must either expose an X25519 agreement lemma or leave
  shared-secret equality as an explicit theorem premise.
- Existing implementation-facing surfaces to keep client-compatible include
  `TLS13.Impl.Client.fsti`, `TLS13.Impl.Client.Driver.fsti`,
  `TLS13.Impl.Client.Types`, `TLS13.Impl.Parser.fsti`, and
  `TLS13.Impl.Serializer.fsti`.

## Hard design principles

1. **Spec before implementation**: role-parametric pure state, transcript
   checkpoints, key-schedule projections, and paired endpoint theorems come
   before server Pulse handlers.
2. **One authoritative pure model**: do not build an unrelated duplicated server
   state machine. Endpoint-specific implementation modules are fine; endpoint-
   specific pure theorem vocabulary should be role-indexed where possible.
3. **Exact transcript bytes**: every handshake transition appends exactly
   `TLS13.Wire.Spec.serialize_handshake msg`, and named transcript checkpoints
   are proved from event logs.
4. **Role-correct traffic mapping**: endpoint role and record direction decide
   whether a read/write state uses client or server traffic labels.
5. **No vague key theorem**: key agreement is indexed by a derived-key
   identifier and follows the TLS 1.3 key-schedule dependency DAG.
6. **Small TCBs with typed postconditions**: crypto, OpenSSL credential/signing,
   parser/serializer C hooks, and TCP listen/accept stay behind narrow
   interfaces.
7. **Mechanical Pulse refinement**: once the pure spec is settled, each Pulse
   transition should prove that concrete state follows the pure transition and
   preserves the invariant.

## Supported server profile

First server version:

- Endpoint role: `ServerEndpoint`.
- Cipher suite: `TLS_CHACHA20_POLY1305_SHA256`.
- Group: X25519.
- Authentication: server certificate only.
- Credential scheme: `RsaPssRsaeSha256`.
- ClientHello acceptance requires:
  - TLS 1.3 supported versions extension;
  - offered `TLS_CHACHA20_POLY1305_SHA256`;
  - offered X25519 key share;
  - offered `RsaPssRsaeSha256`;
  - acceptable SNI according to server config, if an SNI policy is configured.
- Server flight:
  - cleartext `ServerHello`;
  - encrypted empty `EncryptedExtensions`;
  - encrypted `Certificate`;
  - encrypted `CertificateVerify`;
  - encrypted server `Finished`.
- Compatibility ChangeCipherSpec:
  - server does not send it in the first version;
  - receiving it may be tolerated during handshaking if it remains a small reuse
    of existing non-transcript CCS handling.
- Unsupported or malformed profile inputs must transition to explicit failure,
  not silently proceed.

## Role-parametric pure state-machine design

### Endpoint roles

The pure model should expose:

```fstar
type endpoint_role =
  | ClientEndpoint
  | ServerEndpoint
```

Role should flow into:

- connection configuration;
- handshake start/selection state;
- legal event predicates;
- record read/write key projections;
- transcript checkpoint predicates;
- raw/message replay consistency;
- endpoint theorem surfaces.

### Configuration

Client configuration retains:

- server name;
- trust store;
- validation time;
- offered cipher suites;
- offered signature schemes;
- client random/key-share generation inputs.

Server configuration adds:

- certificate chain bytes;
- credential identity;
- allowed signature schemes;
- supported cipher suites;
- supported groups;
- optional SNI policy;
- signing TCB identity for RSA-PSS/SHA-256.

### Handshake/session state

The pure handshake state should record enough information to audit transcript,
key-schedule, and pairing facts:

- ClientHello message and exact serialized bytes.
- ServerHello message and exact serialized bytes.
- Selected cipher suite.
- Selected group.
- Selected signature scheme.
- Client random and server random.
- Client X25519 public share.
- Server X25519 public share.
- Endpoint private key witness where needed for local shared-secret derivation
  predicates.
- Certificate chain and credential identity.
- CertificateVerify input and signature.
- Client and server Finished messages.
- Transcript bytes.
- Key schedule state.
- Handshake buffer/progress data needed by parsers and serializers.

### Server handshake stages

The exact constructors can change, but the model must distinguish at least:

| Stage | Required information |
| --- | --- |
| Awaiting ClientHello | Server config and no accepted client parameters. |
| ClientHello accepted | Parsed ClientHello, offered profile checked, selected suite/group/signature scheme recorded. |
| ServerHello sent | Server random/key share selected, ServerHello appended, `TH_SH` available. |
| Handshake keys installed | Server write and client read handshake traffic material installed role-correctly. |
| EncryptedExtensions sent | Empty EncryptedExtensions appended under server handshake write key. |
| Certificate sent | Certificate chain appended. |
| CertificateVerify signed/sent | CertificateVerify input is `certificate_verify_input(hash(TH_before_CV))`; signature appended. |
| Server Finished sent | Server Finished verify_data is computed over `TH_before_SF`; `TH_SF` available. |
| Application traffic secrets derived | Application traffic secrets are based on `TH_SF`; application use still blocked. |
| Client Finished received | Client Finished parsed under client handshake read key. |
| Client Finished verified | Client Finished MAC checked over `TH_SF`; connection may enter application data. |
| Application data | App data, KeyUpdate, tickets, and close_notify according to supported profile. |
| Closing/Closed/Failed | Same close/failure discipline as client, role-correct for alerts and logs. |

### Server legal events

Add legal events for:

- receive `ClientHello`;
- select parameters and generate server random/key share;
- derive server-side X25519 shared secret;
- send `ServerHello`;
- install server handshake write key and client handshake read key;
- send `EncryptedExtensions`;
- send `Certificate`;
- sign/send `CertificateVerify`;
- send server `Finished`;
- derive/install server application write and client application read keys;
- receive client `Finished`;
- verify client `Finished`;
- send/receive application data;
- send/receive KeyUpdate if supported;
- send/receive close_notify;
- fail with explicit TLS error.

Each legal event must specify:

- source stage/control state;
- required stored artifacts;
- pure functional state update;
- transcript delta, if any;
- raw sent/received delta, if any;
- record read/write sequence and epoch update;
- key schedule update;
- application log or pending application update;
- failure behavior for unsupported profile inputs.

## Transcript checkpoints

Transcript state is byte-oriented. Checkpoints must be named and proved from
event-log projections rather than inferred from control-state names.

| Checkpoint | Transcript contents | Key/proof use |
| --- | --- | --- |
| `TH_CH` | `ClientHello` | Server has accepted client parameters; not enough for handshake traffic. |
| `TH_SH` | `ClientHello || ServerHello` | Handshake traffic secrets. |
| `TH_before_CV` | through `Certificate` | CertificateVerify input. |
| `TH_before_SF` | through `CertificateVerify` | Server Finished verify_data. |
| `TH_SF` | through server `Finished` | Application traffic secrets and client Finished verification context. |
| `TH_CF` | through client `Finished` | Full handshake complete; not the base application traffic-secret context. |
| `TH_KU(label,n)` | traffic update generation point, if modeled | KeyUpdate agreement by label and generation. |

Client and server transcript update discipline:

- Client sends ClientHello; server receives the same ClientHello.
- Server sends ServerHello; client receives the same ServerHello.
- Server sends EncryptedExtensions, Certificate, CertificateVerify, and
  Finished; client receives the same messages in the same transcript order.
- Client sends Finished; server receives the same client Finished.
- Compatibility ChangeCipherSpec is non-transcript.
- Alerts, application data, tickets, and KeyUpdate do not alter the handshake
  transcript.

Required lemmas:

- endpoint event-log consistency implies endpoint transcript consistency;
- paired handshake event logs imply equal transcript bytes at each checkpoint;
- equal transcript bytes imply equal transcript hashes;
- each Finished or CertificateVerify input uses the pre-message transcript hash
  required by TLS 1.3.

## Role-correct key schedule vocabulary

### Traffic labels

```fstar
type traffic_label =
  | ClientTraffic
  | ServerTraffic

let traffic_label_for_endpoint role dir =
  match role, dir with
  | ClientEndpoint, TrafficWrite -> ClientTraffic
  | ClientEndpoint, TrafficRead  -> ServerTraffic
  | ServerEndpoint, TrafficWrite -> ServerTraffic
  | ServerEndpoint, TrafficRead  -> ClientTraffic
```

The existing client projection must reduce to:

- client write handshake = client handshake traffic;
- client read handshake = server handshake traffic;
- client write application = client application traffic;
- client read application = server application traffic.

The server projection must prove:

- server write handshake = server handshake traffic;
- server read handshake = client handshake traffic;
- server write application = server application traffic;
- server read application = client application traffic.

### Derived key identifiers

```fstar
type base_secret_id =
  | EarlySecret
  | HandshakeSecret
  | MasterSecret

type derived_key_id =
  | BaseSecret of base_secret_id
  | TrafficSecret of traffic_epoch * traffic_label
  | TrafficKey of traffic_epoch * traffic_label
  | TrafficIV of traffic_epoch * traffic_label
  | FinishedKey of traffic_label
  | TrafficUpdateSecret of traffic_label * nat
  | ExporterMasterSecret
  | ResumptionMasterSecret
```

First theorem scope:

- `TrafficSecret (TrafficHandshake, ClientTraffic)`;
- `TrafficSecret (TrafficHandshake, ServerTraffic)`;
- `TrafficSecret (TrafficApplication, ClientTraffic)`;
- `TrafficSecret (TrafficApplication, ServerTraffic)`;
- `TrafficKey` and `TrafficIV` for those traffic secrets;
- `FinishedKey ClientTraffic`;
- `FinishedKey ServerTraffic`;
- `TrafficUpdateSecret label n` only if KeyUpdate stays in the first server
  profile.

Exporter and resumption master secrets remain out of the first proof unless the
implementation exposes them. Randomness, private keys, certificates, PSK/0-RTT
secrets, and unsupported key material are not part of the theorem family.

### Dependency DAG

The key agreement proof follows this dependency graph:

```text
paired X25519 key shares + X25519 agreement law
  -> same shared secret

same shared secret + empty PSK
  -> same early secret
  -> same handshake secret
  -> same master secret

same handshake secret + same TH_SH
  -> same client/server handshake traffic secrets
  -> same handshake AEAD key/IV
  -> same Finished keys

same master secret + same TH_SF
  -> same client/server application traffic secrets
  -> same application AEAD key/IV

same traffic secret generation n
  -> same traffic secret generation n+1
  -> same updated AEAD key/IV
```

The proof rule is:

```text
agreement on every input to a derivation
  implies agreement on that derived key material
```

This is not a simple linear induction over all keys. Application traffic-secret
agreement depends on master-secret agreement and transcript-hash agreement at
`TH_SF`; it does not directly depend on handshake AEAD key agreement except
through the separate proof that both endpoints reached the same authenticated
transcript.

## Endpoint pairing predicates

The two-party theorem needs pure predicates relating a client state and a server
state.

### Wire-log pairing

```fstar
paired_wire_logs client server =
  client.cs_wire_log.raw_sent == server.cs_wire_log.raw_received /\
  server.cs_wire_log.raw_sent == client.cs_wire_log.raw_received
```

This is the pure counterpart of the driver-level IO-history relation.

### Handshake-event pairing

```fstar
paired_handshake_events checkpoint client server
```

This should state that sent/received ClientHello, ServerHello,
EncryptedExtensions, Certificate, CertificateVerify, and Finished events are
paired up to the requested transcript checkpoint.

### X25519 key-share pairing

```fstar
paired_x25519_key_shares client server
```

Meaning:

- the client's sent public key share equals the server's parsed ClientHello key
  share;
- the server's sent public key share equals the client's parsed ServerHello key
  share;
- each public share corresponds to the endpoint's private key;
- both X25519 shared-secret computations are exposed:
  - `x25519_shared client_sk server_pub`;
  - `x25519_shared server_sk client_pub`.

The predicate should stop before silently asserting shared-secret equality. That
equality must come from either:

- an explicit `TLS13.Crypto.Spec` X25519 agreement law; or
- a first-version theorem premise stating shared-secret equality, with the TCB
  boundary documented.

### Key derivation checkpoint pairing

```fstar
same_key_derivation_checkpoint checkpoint client server
```

This says both endpoints are being compared at the same TLS key-schedule point.
It is not transcript equality.

Suggested checkpoint vocabulary:

```fstar
type key_derivation_checkpoint =
  | DeriveHandshakeTraffic
  | DeriveApplicationTraffic
  | DeriveTrafficUpdate of traffic_label * nat
```

`DeriveHandshakeTraffic` requires both endpoints to be at `TH_SH`.
`DeriveApplicationTraffic` requires both endpoints to be at `TH_SF`.
`DeriveTrafficUpdate label n` requires both endpoints to have applied the same
number of updates for the same traffic label.

### Derivation input agreement

```fstar
derivation_inputs_agree key_id client server
```

This packages exactly the inputs required by the `derived_key_id`:

- supported profile agreement;
- shared-secret or base-secret agreement;
- transcript checkpoint and transcript-hash agreement;
- traffic label agreement;
- role/direction mapping;
- KeyUpdate generation count, when applicable.

## Main pure theorem family

Final pure theorem shape:

```fstar
theorem_paired_endpoints_derived_key_agrees :
  key_id:derived_key_id ->
  client:connection_state ->
  server:connection_state ->
  Lemma
    (requires
      client_endpoint_consistent client /\
      server_endpoint_consistent server /\
      paired_endpoint_states_for_key key_id client server /\
      derivation_inputs_agree key_id client server)
    (ensures
      peer_derived_key_material_agrees key_id client server)
```

`peer_derived_key_material_agrees` should instantiate to:

- traffic-secret equality for `TrafficSecret`;
- AEAD key equality for `TrafficKey`;
- AEAD IV equality for `TrafficIV`;
- Finished-key equality for `FinishedKey`;
- updated traffic-secret equality for `TrafficUpdateSecret`.

For record-layer use, lift this to:

```text
client write material for ClientTraffic == server read material for ClientTraffic
server write material for ServerTraffic == client read material for ServerTraffic
```

## Spec proof gates before implementation

Server Pulse implementation is blocked until these gates are complete.

### Gate 1: role clarity

Checklist:

- [ ] `ClientEndpoint` and `ServerEndpoint` roles exist in the pure model.
- [ ] Client configuration remains behaviorally unchanged.
- [ ] Server configuration records supported suite/group/signature policy,
      credential identity, and certificate chain.
- [ ] Read/write direction is never interpreted without endpoint role.
- [ ] Client read/write key projections reduce to the existing client
      projections.
- [ ] Server read/write key projections prove the correct traffic-label mapping.

### Gate 2: transcript precision

Checklist:

- [ ] Every client and server handshake message transition appends exactly
      `serialize_handshake msg`.
- [ ] Non-transcript messages are explicitly non-transcript.
- [ ] `TH_CH`, `TH_SH`, `TH_before_CV`, `TH_before_SF`, `TH_SF`, and `TH_CF`
      are named predicates/lemmas.
- [ ] CertificateVerify input uses `hash(TH_before_CV)`.
- [ ] Server Finished uses `hash(TH_before_SF)`.
- [ ] Client Finished verification uses `hash(TH_SF)`.
- [ ] Paired legal events imply equal transcript bytes at each checkpoint.

### Gate 3: X25519/shared-secret boundary

Checklist:

- [ ] `paired_x25519_key_shares` records both endpoints' public shares and the
      local private/public correspondence.
- [ ] The crypto spec exposes an X25519 agreement lemma, or the theorem explicitly
      assumes shared-secret equality.
- [ ] The TCB boundary is documented in the pure theorem and audit text.
- [ ] Same shared secret implies same early, handshake, and master secrets for
      the supported empty-PSK profile.

### Gate 4: derived-key agreement

Checklist:

- [ ] `derived_key_id` and `derivation_inputs_agree` are defined.
- [ ] Handshake traffic-secret agreement is proved at `TH_SH`.
- [ ] Application traffic-secret agreement is proved at `TH_SF`.
- [ ] AEAD key/IV agreement is proved by deterministic derivation from traffic
      secret agreement.
- [ ] Finished-key agreement is proved by deterministic derivation from the
      relevant traffic secret.
- [ ] KeyUpdate agreement is proved by label and generation count if KeyUpdate is
      in scope.
- [ ] Out-of-scope derived keys are explicitly not claimed.

### Gate 5: record-material agreement

Checklist:

- [ ] Endpoint record read/write projections expose installed key/IV material.
- [ ] Client write equals server read for `ClientTraffic`.
- [ ] Server write equals client read for `ServerTraffic`.
- [ ] Record sequence/epoch consistency is preserved.
- [ ] Sent seal and accepted received decode replay use the agreed material.

## Phase-by-phase implementation plan

### Phase 0: baseline and naming

Checklist:

- [ ] Keep current client verification, extraction, and interop gates green.
- [ ] Choose module names:
      - shared endpoint proof vocabulary: `TLS13.Impl.Endpoint.Types`;
      - role-parametric pure state, if split: `TLS13.Spec.EndpointState`;
      - server public API: `TLS13.Impl.Server.fsti` / `.fst`;
      - server theorem vocabulary: `TLS13.Impl.Server.Types.fst`;
      - server driver: `TLS13.Impl.Server.Driver.fsti` / `.fst`;
      - server credential TCB: `TLS13.ServerCredentials.fsti` or
        `TLS13.OpenSSL.Server.fsti`;
      - runtime wrapper: `runtime/tls13_server_driver.h` / `.c`.
- [ ] Decide whether KeyUpdate remains in first server scope.
- [ ] Decide whether the first key-agreement theorem uses an X25519 agreement
      lemma or an explicit shared-secret equality premise.

Validation:

- [ ] `make verify`
- [ ] `make check-admits`
- [ ] `make extract-driver-bundle`
- [ ] `make test-extracted-client-driver-slice`
- [ ] `make test-openssl-echo`

### Phase 1: role-parametric pure state and invariants

Checklist:

- [ ] Add `ServerEndpoint`.
- [ ] Add server configuration fields.
- [ ] Replace client-only start/session state with role-aware handshake data.
- [ ] Add server handshake stages.
- [ ] Add server legal events.
- [ ] Generalize expected traffic secret by role, direction, epoch, and label.
- [ ] Prove client projection compatibility.
- [ ] Prove server projection correctness.
- [ ] Generalize event-log, transcript, record-layer, key-schedule, raw replay,
      seal replay, decode replay, and application-log consistency.
- [ ] Add transcript checkpoints and derivation-input extraction helpers.

Validation:

- [ ] Existing client theorem modules still verify.
- [ ] No client public API behavior changes.

### Phase 2: paired endpoint traces and derived-key theorem family

Checklist:

- [ ] Define `paired_wire_logs`.
- [ ] Define `paired_handshake_events`.
- [ ] Define `paired_x25519_key_shares`.
- [ ] Define `same_key_derivation_checkpoint`.
- [ ] Define `derivation_inputs_agree`.
- [ ] Add or assume X25519 agreement.
- [ ] Prove transcript pairing up to each checkpoint.
- [ ] Prove base-secret agreement.
- [ ] Prove traffic-secret agreement.
- [ ] Prove AEAD key/IV and Finished-key agreement.
- [ ] Prove peer record-material agreement.
- [ ] Expose `theorem_paired_endpoints_derived_key_agrees`.

Validation:

- [ ] This phase verifies in pure/spec modules without server Pulse code.
- [ ] The theorem scope lists supported and out-of-scope `derived_key_id` cases.

### Phase 3: shared endpoint/codec predicate refactor

Checklist:

- [ ] Extract role-neutral response/status records from client theorem modules
      into a shared endpoint module.
- [ ] Extract role-neutral output-slice and parse/decode helper predicates.
- [ ] Keep client local events, client input well-formedness, and client
      invariants such as `local_input_wf`, `network_input_wf`,
      `client_state_correct`, `client_end_to_end_invariant`, `network_out`, and
      `app_out` in client theorem modules.
- [ ] Point parser and serializer contracts at shared endpoint predicates where
      appropriate.
- [ ] Keep exact consumed-prefix helpers such as `Pulse.Lib.Array.sub` /
      `return_sub` available to client and server drivers.
- [ ] Preserve public client API shape.

Validation:

- [ ] Client verification unchanged.
- [ ] Client extraction and interop unchanged.

### Phase 4: server credential and signing TCB

Checklist:

- [ ] Define server credential identity and certificate-chain spec.
- [ ] Relate credential identity to leaf public key and supported signature
      scheme.
- [ ] Define typed signing postcondition for CertificateVerify.
- [ ] Add Pulse/C interface for credential allocation/free from in-memory bytes.
- [ ] Add signing function for server CertificateVerify input.
- [ ] Keep private key bytes outside protocol logic.
- [ ] Keep Finished HMAC verification outside this TCB.

Validation:

- [ ] TCB interface exposes exact typed postconditions.
- [ ] C stubs do not return success without establishing the typed postcondition.

### Phase 5: server serializers and codec support

Checklist:

- [ ] Add supported ClientHello acceptability lemmas.
- [ ] Add ServerHello serialize/parse-back facts.
- [ ] Add empty EncryptedExtensions serialize/parse-back facts.
- [ ] Add Certificate serialize/parse-back facts over configured chain.
- [ ] Add CertificateVerify serialize/parse-back facts.
- [ ] Add server Finished serialize/parse-back facts.
- [ ] Expose exact bytes written and length bounds.
- [ ] Expose record header/AAD facts.
- [ ] Expose protected-record seal facts.
- [ ] Expose transcript-fragment equality for each handshake fragment.
- [ ] Add or expose fixed server builders with stable names:
      `serialize_server_hello_from_selection`,
      `serialize_empty_encrypted_extensions`,
      `serialize_certificate_from_credential`,
      `build_server_certificate_verify_input`,
      `serialize_certificate_verify_from_signature`, and
      `serialize_server_finished_outputs`.
- [ ] Ensure contracts expose `TLS13.Wire.Spec.parse_record`,
      `parse_tls_message`, `TLS13.Record.Spec.seal`, and
      `TLS13.Handshake.Spec.certificate_verify_input(hash(transcript_before_cv))`
      facts where relevant.
- [ ] Avoid broad generic serializers unless proof requires them.

Validation:

- [ ] Server serializer contracts are precise enough for transcript and raw-log
      proofs.

### Phase 6: server buffer/event API and theorem surface

Recommended API shape:

```text
new_server
next_local_action
process_network_bytes
process_local_event
```

Checklist:

- [ ] Define `server_state_correct`.
- [ ] Define `server_end_to_end_invariant`.
- [ ] Define server response/status types.
- [ ] Define server local event kinds.
- [ ] Define `server_network_bytes_end_to_end_correct`.
- [ ] Define `server_local_event_end_to_end_correct`.
- [ ] Constructor establishes the server invariant.
- [ ] Network/local steps preserve the server invariant.
- [ ] Emitted bytes expose raw-delta, parse-back, seal, and write-key provenance.
- [ ] Consumed bytes expose exact consumed prefix, parse/decode classification,
      open facts, and read-key provenance.
- [ ] Server invariants expose facts needed to instantiate
      `theorem_paired_endpoints_derived_key_agrees` with a client state.

Validation:

- [ ] API postconditions are strong enough for the future top-level driver.
- [ ] The server theorem surface does not duplicate the pure key-agreement proof;
      it preserves the invariant needed to instantiate it.

### Phase 7: server state mutations and handlers

Checklist:

- [ ] Create small `.fsti` boundaries for server state mutations.
- [ ] Reuse shared helpers where endpoint-independent.
- [ ] Add network handlers:
      - ClientHello accept/reject;
      - compatibility CCS receive if supported;
      - client Finished receive/open;
      - application data;
      - alerts;
      - KeyUpdate if supported;
      - decode/decrypt errors.
- [ ] Add local handlers:
      - server random and key share generation;
      - cipher/group/signature selection;
      - shared-secret and traffic-secret derivation;
      - handshake key installation;
      - server flight emission;
      - client Finished verification;
      - application key installation;
      - application data, KeyUpdate, close_notify.
- [ ] Add failure transitions:
      - unsupported cipher suite;
      - missing/unsupported X25519 key share;
      - unsupported or credential-incompatible signature scheme;
      - malformed ClientHello;
      - bad client Finished;
      - application data before client Finished;
      - short output buffer;
      - decode/decrypt failure.

Validation:

- [ ] Each handler proves it follows the pure transition.
- [ ] Each handler preserves server invariant.
- [ ] No broad catches or success-shaped fallbacks.

### Phase 8: verified top-level server driver

Public driver target:

```text
new_server
accept
send
receive
close
```

Checklist:

- [ ] `new_server` allocates credential context and Pulse-owned buffers.
- [ ] `accept` creates/listens/accepts one TCP channel, runs handshake to
      completion, closes listener, and returns connected server handle.
- [ ] `send`, `receive`, and `close` operate on one connected server handle.
- [ ] Driver owns retained receive buffer.
- [ ] Driver owns network output, application output, and signing scratch buffers.
- [ ] Driver maintains exact IO-history relation:
      - server transport sent bytes;
      - server transport received bytes;
      - protocol raw sent/received wire logs;
      - retained buffered read-ahead.
- [ ] Driver uses total-write `TLS13.IO.write` postconditions.
- [ ] Driver uses fueled loops for handshake/receive/close.
- [ ] C wrapper owns only handle/lifetime/error state.

Validation:

- [ ] No TLS scratch buffers owned by runtime C.
- [ ] No TLS handshake polling in runtime C.

### Phase 9: IO, runtime, extraction, and C TCBs

Checklist:

- [ ] Extend IO TCB with `listen_tcp`.
- [ ] Extend IO TCB with `accept_tcp`.
- [ ] Add listener close/free if listener state persists.
- [ ] Add server credential/signing C shim.
- [ ] Use concrete C stub names such as
      `c_stubs/tls13_server_credentials_karamel.c`,
      `c_stubs/tls13_server_credentials_karamel.h`,
      `c_stubs/tls13_io_karamel.c`, and `tls13_io_stubs.c`, with
      `c_stubs/tls13_connection_backend.h` extended only for typed serializer
      hooks.
- [ ] Add extraction targets:
      - `extract-server-krml`;
      - `extract-server-bundle`;
      - `extract-server-driver-bundle`.
- [ ] Add test targets:
      - `test-extracted-server-driver-slice`;
      - `test-openssl-sclient`;
      - `test-verified-client-server`.
- [ ] Ensure generated symbols avoid POSIX collisions with `accept`, `listen`,
      `send`, and `close`.

Validation:

- [ ] C wrappers are small and typed.
- [ ] Generated ABI is authoritative.

### Phase 10: validation and audit

Checklist:

- [ ] Pure theorem gates pass.
- [ ] Server object allocation smoke test passes.
- [ ] Credential context creation/free smoke test passes.
- [ ] Serializer parse-back tests pass.
- [ ] Supported ClientHello accepted.
- [ ] Unsupported cipher suite rejected.
- [ ] Missing/unsupported X25519 key share rejected.
- [ ] Unsupported signature scheme rejected.
- [ ] Bad client Finished rejected.
- [ ] Application data before client Finished rejected.
- [ ] OpenSSL `s_client` connects to verified server.
- [ ] Application echo works.
- [ ] close_notify works.
- [ ] KeyUpdate works if in scope.
- [ ] Verified client connects to verified server.
- [ ] Pure paired-endpoint derived-key theorem instantiates on paired
      implementation states.
- [ ] Existing OpenSSL echo client test still passes.
- [ ] Existing client driver slice test still passes.
- [ ] `make verify` passes.
- [ ] `make check-admits` stays at zero.
- [ ] `make check-c-stubs` passes if C stubs are added.

Audit checklist:

- [ ] Supported profile and rejected features are explicit.
- [ ] Public server APIs and usage are documented.
- [ ] Server transcript sequence is documented.
- [ ] Role-correct key-schedule direction mapping is documented.
- [ ] Derived-key theorem names and supported scope are documented.
- [ ] Out-of-scope secrets are documented.
- [ ] X25519/shared-secret TCB boundary is documented.
- [ ] Server credential/signing TCB is documented.
- [ ] Parser/serializer C backend additions are documented.
- [ ] IO listen/accept TCB additions are documented.
- [ ] Runtime C owned code is documented and contains no protocol logic.
- [ ] Validation commands and interop evidence are documented.

## Suggested implementation order

1. Role-parametric pure state, endpoint roles, transcript checkpoints, and
   role-correct key-projection lemmas.
2. Endpoint pairing predicates and derived-key agreement theorem family.
3. Shared endpoint predicate refactor, preserving the client proof.
4. Server credential/signing spec and typed TCB.
5. Server serializer contracts and C backend hooks.
6. Public server buffer/event API and theorem surface.
7. Server state mutation modules and handlers.
8. Server buffer/event API implementation.
9. Verified top-level server driver.
10. Runtime C wrapper and extraction targets.
11. OpenSSL `s_client` interop.
12. Verified client-to-server interop with pure theorem instantiation.
13. Audit documentation updates.

## Proof hardening rules

- Verify `.fsti` before `.fst`.
- Keep public postconditions strong enough for downstream callers.
- No `admit()` or `assume_`.
- No broad C fallback that returns success without a typed TCB postcondition.
- No hidden weakening of parser/serializer contracts.
- No role-ambiguous key projection lemmas.
- No theorem that omits shared-secret equality from key agreement assumptions.
- No implementation phase before pure derived-key theorem gates.
- Keep transcript checkpoint lemmas named and small.
- Keep derived-key agreement lemmas indexed by `derived_key_id`.
- Follow the key-schedule dependency DAG.
- Preserve low rlimits by factoring role-parametric lemmas into small modules.
