# Main pairing theorem: end-to-end key-material agreement

This note explains the audit-facing theorem
`TLS13.Impl.Driver.Pairing.lemma_client_server_driver_end_to_end_key_material_agrees`.
It is grounded in the current code in
`src/impl/TLS13.Impl.Driver.Pairing.{fsti,fst}` and the supporting pure
connection-state lemmas in `src/spec/TLS13.Spec.ConnectionState.fst` and
`src/spec/TLS13.ConnectionState.Lemmas.{fsti,fst}`.

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
  `TLS13.Spec.ConnectionState.fst:2084-2090`).

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

The current verified byte-level progress is a cleartext-handshake theorem rather
than a full byte-trace theorem.  `TLS13.Spec.WireFormatLemmas` now exposes
lemmas that derive:

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
- `TLS13.ConnectionState.ProtectedWireLemmas.lemma_protected_handshake_wire_equal_from_sent_seal_peer`,
  which proves a single protected handshake message's serialized-byte equality
  from sender seal replay, receiver decode replay, peer key/IV agreement, and
  aligned record sequence numbers.  The follow-up
  `lemma_protected_handshake_wire_equal_from_event_projections_peer` lifts this
  to the event-projection predicates used by the replay invariants.  The
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

See `src/spec/TLS13.Crypto.Spec.fsti:18-77`.

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
(`src/impl/TLS13.Crypto.fsti:16-20`, `119-173`). The default client/server
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

The remaining proof obligation is to use that head-replay extractor
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
head-replay extractor.
The AEAD open(seal(...)) step is available, but it remains an explicit trust
assumption in the crypto spec.

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
