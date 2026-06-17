# Audit guide 2026-06-16

This document is a fresh audit guide for the current verified TLS 1.3 client and
server driver surfaces, the paired client/server derivation agreement theorem,
and the trusted assumptions still outside the mechanized proof.

The intended audit result is a signed-off statement of the form:

> For the supported profile and first application-traffic epoch, successful
> client/server driver handshakes over paired transport histories produce paired
> wire logs and agreeing TLS 1.3 key material, modulo the listed TCB assumptions.

## Supported theorem profile

The current theorem is intentionally narrow:

- TLS 1.3 supported profile:
  - X25519 key exchange.
  - `TLS_CHACHA20_POLY1305_SHA256`.
  - `RsaPssRsaeSha256`.
  - No PSK / 0-RTT modeled in this theorem.
- First application-traffic epoch only.
- No KeyUpdate in the states compared by the theorem.
- Paired transport histories remain an explicit precondition:
  - client received bytes are server sent bytes;
  - server received bytes are client sent bytes.
- The theorem compares states at an application-ready point with no driver
  read-ahead: the transport histories exactly account for the protocol raw logs.

## Files to audit first

1. `src/impl/TLS13.Impl.Client.Driver.fsti`
2. `src/impl/TLS13.Impl.Server.Driver.fsti`
3. `src/impl/TLS13.Impl.Driver.Pairing.fsti`
4. `src/spec/TLS13.Spec.ConnectionState.fst`
5. `src/spec/TLS13.ConnectionState.Lemmas.fsti`
6. `src/spec/TLS13.Spec.WireFormatLemmas.fsti`
7. TCB interfaces:
   - `src/impl/TLS13.Impl.Parser.fsti`
   - `src/impl/TLS13.Impl.Serializer.fsti`
   - `src/spec/TLS13.Crypto.Spec.fsti`
   - `src/impl/TLS13.Crypto.fsti`
   - `src/spec/TLS13.X509.Spec.fsti`
   - `src/impl/TLS13.X509.fsti`
   - `src/impl/TLS13.OpenSSL.fsti`
   - `src/impl/TLS13.IO.fsti`

## Top-level client driver API audit

Audit file: `src/impl/TLS13.Impl.Client.Driver.fsti`.

### Public resources and observations

Key predicates:

- `client_driver_live d st`
- `client_driver_connected d st received sent`
- `client_driver_closed d st`
- `client_driver_wire_logs_match st received sent buffered buffered_len`
- `client_driver_application_ready st`
- `client_driver_sent_log_exact st sent`
- `client_driver_received_log_exact_prefix st received`
- `client_driver_received_no_read_ahead st received`

The connected predicate owns the concrete TCP channel history tracked by
`TLS13.IO`. The protocol-level raw byte logs live in
`st.cs_wire_log.raw_sent` and `st.cs_wire_log.raw_received`. The retained input
buffer is hidden inside `client_driver_wire_logs_match`; this is why public
success states used by the paired theorem require both exact-prefix accounting
and `client_driver_received_no_read_ahead`.

### Public functions

- `new_client`
  - Allocates/configures a client driver.
  - Ensures `CT.client_state_correct` and `CT.client_end_to_end_invariant` for
    the configured initial state.
- `connect`
  - On `DriverWorkflowOk`, returns `client_driver_connected`.
  - Ensures:
    - `client_driver_application_ready st1`;
    - config preservation;
    - sent log exactness;
    - received log accounted, exact prefix, and no read-ahead.
- `send`
  - Requires a connected driver and `CT.local_input_wf` for
    `LocalSendApplicationData`.
  - Preserves connected ownership.
  - Relates the transition to `client_driver_send_correct`.
  - Preserves pre/post sent-log exactness and received-log accounting.
- `receive`
  - Requires a connected driver and caller output buffer.
  - Preserves connected ownership.
  - Relates result status and output bytes to
    `client_driver_receive_correct`.
  - Preserves config, sent-log exactness, and received-log accounting.
- `close`
  - Consumes a connected driver and returns `client_driver_closed`.
  - Relates the close path to `client_driver_close_correct`.

### Client API sign-off questions

- [ ] Do the public resources hide exactly the implementation details we want
      hidden, while still exposing enough raw-byte history for pairing?
- [ ] Is `client_driver_application_ready` the right public success predicate:
      end-to-end invariant, `ControlApplicationData`, installed client
      application record keys, and stable client X25519 projection?
- [ ] Is the distinction between received-log accounting, exact prefix, and
      no-read-ahead clear and sufficient?
- [ ] Does `connect` expose all facts needed by the paired theorem without
      leaking lower-level implementation details?
- [ ] Should `send` / `receive` expose no-read-ahead in any additional cases, or
      is it correct that the theorem is applied only at points where retained
      input is known empty?
- [ ] Does `receive` copyout correctness prove the bytes returned to C are the
      same application bytes produced by the verified protocol transition?
- [ ] Is `close` intentionally weaker than `send` / `receive` with respect to
      post-state application readiness, and is that acceptable for the API?

## Top-level server driver API audit

Audit file: `src/impl/TLS13.Impl.Server.Driver.fsti`.

### Public resources and observations

Key predicates:

- `server_driver_live d st certificate_chain credential_identity`
- `server_driver_connected d st certificate_chain credential_identity received sent`
- `server_driver_closed d st certificate_chain credential_identity`
- `server_driver_wire_logs_match st received sent buffered buffered_len`
- `server_driver_application_ready st`
- `server_driver_sent_log_exact st sent`
- `server_driver_received_log_exact_prefix st received`
- `server_driver_received_no_read_ahead st received`

Server resources additionally carry:

- the concrete certificate chain bytes;
- an abstract `server_credential_identity`;
- the connection between credentials and signing is delegated to the OpenSSL TCB.

### Public functions

- `new_server`
  - Takes certificate-chain and private-key buffers.
  - Produces `server_driver_live` plus an existential
    `credential_identity`.
  - Ensures `ST.server_state_correct`, `CM.can_start_server`, and
    `ST.server_end_to_end_invariant` for the initial server state.
- `accept`
  - Requires a live driver and a supported server configuration:
    - supported cipher suite includes `TLS_CHACHA20_POLY1305_SHA256`;
    - supported group includes `X25519`;
    - allowed signature schemes include `RsaPssRsaeSha256`;
    - server SNI policy is `None`.
  - On `ServerWorkflowOk`, returns `server_driver_connected` and ensures:
    - `server_driver_application_ready st1`;
    - config preservation;
    - sent log exactness;
    - received log accounted, exact prefix, and no read-ahead.
  - On `ServerWorkflowClosed`, returns closed state and preserves config.
  - Other statuses return a connected driver with config preservation but no
    application-ready claim.
- `send`
  - Requires connected server driver and
    `ST.server_local_event_input_ready` for application data.
  - Preserves connected ownership.
  - Relates the transition to `server_driver_send_correct`.
- `receive`
  - Requires connected server driver and output buffer.
  - Preserves connected ownership.
  - Relates status, network loop, and output bytes to
    `server_driver_receive_correct`.
- `close`
  - Requires connected server driver and `server_driver_application_ready st0`.
  - Returns `ServerWorkflowClosed`, closed ownership, config preservation, and
    `server_driver_close_correct`.

### Server API sign-off questions

- [ ] Are the server `accept` supported-profile preconditions exactly the
      intended interop profile?
- [ ] Is `server_sni_policy == None` intentionally part of the verified
      supported profile?
- [ ] Does `accept` expose enough successful-handshake facts without exposing
      internal orchestration stages?
- [ ] Are non-OK `accept` outcomes specified strongly enough for safe caller
      cleanup/retry behavior?
- [ ] Is the credential identity abstracted at the right level, or should the
      public API expose more certificate/key binding facts?
- [ ] Does `server_driver_receive_correct` tie returned application bytes to the
      same verified network transition and app-output buffer?
- [ ] Is server `close` requiring `server_driver_application_ready` the desired
      public precondition?

## Paired derivation agreement theorem audit

Audit file: `src/impl/TLS13.Impl.Driver.Pairing.fsti`.

### Canonical theorem

The audit-facing theorem is:

```fstar
lemma_client_server_driver_end_to_end_key_material_agrees
```

Its input predicate is:

```fstar
client_server_driver_end_to_end_agreement_inputs
```

That expands to:

```fstar
client_server_driver_key_material_no_read_ahead_supported_wire_hello_derivation_checkpoint_inputs
```

The canonical inputs are:

1. `client_server_driver_public_success_supported_wire_hello_inputs`
   - client/server application-ready driver states;
   - client/server sent logs exact;
   - client/server received logs exact prefixes;
   - client/server no-read-ahead;
   - paired transport histories;
   - supported client config wire profile.
2. `CS.paired_key_derivation_checkpoints client server`
   - same `DeriveHandshakeTraffic` checkpoint;
   - same `DeriveApplicationTraffic` checkpoint.
3. `client_server_driver_first_epoch_no_key_update_state_inputs`
   - both endpoints satisfy
     `CS.first_epoch_application_traffic_material_no_key_update_invariant`.

The theorem ensures:

- `client_server_driver_supported_profile_derived_state_inputs client server`
- `CS.supported_profile_all_derived_key_material_agrees client server`
- `CS.supported_profile_client_server_key_material_inputs_agree client server`
- `paired_driver_transport_logs_exact ...`
- `CS.paired_wire_logs client server`
- `CS.supported_profile_client_server_key_material_agrees client server`

### Compatibility wrapper

The older theorem:

```fstar
lemma_client_server_driver_key_material_agrees_from_public_success_supported_wire_hello_and_handshake_events
```

is now a wrapper. It takes `paired_handshake_events`, derives
`CS.paired_key_derivation_checkpoints`, and calls the canonical theorem.

### The theorem proof chain to audit

1. Public driver success facts plus paired transport histories imply:
   - exact paired transport logs;
   - `CS.paired_wire_logs`.
2. Raw replay plus `TLS13.Spec.WireFormatLemmas` imply:
   - paired ClientHello key-share equality;
   - paired ServerHello key-share equality.
3. Hello key-share equality plus stable endpoint projections imply:
   - `CS.paired_x25519_key_shares`.
4. Paired X25519 shares plus key-schedule lineage and paired derivation
   checkpoints imply:
   - all supported-profile derived key material agrees.
5. First-epoch no-KeyUpdate application traffic invariant plus application-ready
   record-key installation imply:
   - application record material inputs agree.
6. Derived key agreement plus record material agreement imply:
   - `CS.supported_profile_client_server_key_material_agrees`.

### Paired theorem sign-off questions

- [ ] Is `paired_transport_histories` the right external environment
      precondition, and is it acceptable to keep it explicit?
- [ ] Is `CS.paired_key_derivation_checkpoints` the right remaining semantic
      checkpoint precondition, or should it be further derived from wire replay?
- [ ] Is the no-read-ahead requirement acceptable for the theorem's intended
      comparison point?
- [ ] Is the theorem intentionally first-epoch/no-KeyUpdate only?
- [ ] Does `first_epoch_application_traffic_material_no_key_update_invariant`
      state exactly what should be assumed for the no-KeyUpdate theorem?
- [ ] Should the first-epoch material invariant be proven from legal reachability
      before final sign-off, or is it acceptable as an explicit audit precondition?
- [ ] Does the theorem output exactly the agreement facts needed by downstream
      callers, or should it also expose lower-level derived material equalities
      individually?
- [ ] Should server supported-profile configuration be an explicit theorem input
      for readability, even if current proof obtains enough from application
      readiness/key-schedule lineage?

## Wire-format and parser/serializer TCB audit

### Pure wire lemma boundary

Audit file: `src/spec/TLS13.Spec.WireFormatLemmas.fsti`.

This is currently an interface-only assumption boundary. It states the
supported-profile parseback and injectivity facts used by the paired theorem.

Important points:

- ClientHello exact parseback is not assumed for `Some B.empty` SNI.
- The supported profile uses a weaker `client_hello_wire_equivalent` relation
  because empty SNI serializes like absent SNI.
- The canonical paired theorem only needs Hello key-share equality, not full
  ClientHello equality.
- Raw replay lemmas bridge:
  - `CS.paired_wire_logs`;
  - raw sent/received replay consistency;
  - supported client config/profile;
  - paired cleartext Hello key shares.

Sign-off questions:

- [ ] Are the stated wire-format lemmas exactly the right TCB boundary?
- [ ] Is empty-SNI canonicalization handled correctly?
- [ ] Should these lemmas be implemented directly over `TLS13.Wire.Spec`, or
      discharged by EverParse-derived theorems?
- [ ] Are the supported-profile restrictions complete: cipher suite, signature
      scheme, and any missing named-group/SNI constraints?
- [ ] Is key-share equality, rather than full ClientHello equality, the right
      theorem dependency?

### Extracted parser TCB

Audit file: `src/impl/TLS13.Impl.Parser.fsti`.

**STATUS (2026-06-17):** CLIENT PARSERS NOW VERIFIED via EverParse integration.

After merging `origin/main`, client-side parsers use auto-generated, verified code from
`TLS13.Wire.Generated.*` modules (65+ modules generated from `tls.qd.rfc`). The parser TCB
for **client** messages is eliminated. Server-side parsers still use `c_stubs` temporarily
and are planned for Phase 5 (see MERGE_PHASE2_COMPLETE.md).

This module connects concrete parser code to pure `TLS13.Wire.Spec` facts.

Key functions:

- `parse_tls_message` - now uses generated parsers for client messages
- `decode_network_record`
- `decode_network_buffer`

Sign-off questions:

- [ ] On parser success, do the postconditions prove the returned low-level
      message is valid for the pure parsed message?
- [ ] On parser failure, do the postconditions rule out all matching pure parses
      for the relevant content type?
- [ ] Does `decode_network_buffer` consume exactly the first complete TLS record
      and leave suffix retention to the verified driver?
- [ ] Is `CT.network_input_wf` strong enough for both cleartext and protected
      ApplicationData records?
- [ ] Do the C parser/backend functions actually satisfy these contracts for all
      length/error cases?

### Extracted serializer TCB

Audit file: `src/impl/TLS13.Impl.Serializer.fsti`.

This module is trusted to connect concrete serializer code to pure
`TLS13.Wire.Spec` serialization facts.

Key areas:

- ClientHello serialization from handshake start.
- ServerHello / encrypted flight builders.
- CertificateVerify input builders.
- TLSInnerPlaintext construction.
- Record serialization and output-prefix facts.

Sign-off questions:

- [ ] Do serializer postconditions always expose exact output prefixes, not just
      lengths/statuses?
- [ ] Are fixed buffer capacities sufficient and checked before every write?
- [ ] Do serializer contracts match the actual C backend byte layout?
- [ ] Are record headers, handshake lengths, and transcript bytes exactly tied
      to `TLS13.Wire.Spec`?
- [ ] Are all supported-profile messages covered by precise parseback facts?

## Crypto TCB audit

Pure spec file: `src/spec/TLS13.Crypto.Spec.fsti`.

Implementation interface: `src/impl/TLS13.Crypto.fsti`.

Trusted operations:

- SHA-256
- HMAC-SHA256
- HKDF extract/expand-label
- X25519 public key and shared secret
- X25519 agreement lemma
- TLS 1.3 record nonce construction
- ChaCha20-Poly1305 seal/open
- RSA-PSS/SHA-256 signature verification predicate
- random byte generation

Important caveat:

`random_bytes` proves buffer ownership/length behavior, not entropy or
unpredictability. The functional-correctness theorem assumes generated material
is the material recorded in the model; it is not a cryptographic security proof
of randomness.

Sign-off questions:

- [ ] Do the HACL/OpenSSL-backed implementations match the pure functions in
      `TLS13.Crypto.Spec`?
- [ ] Is `lemma_x25519_shared_agreement` acceptable as a crypto axiom/TCB fact?
- [ ] Are failure cases for `x25519_shared` and AEAD open modeled correctly?
- [ ] Does the proof need any explicit freshness/entropy property, or is
      functional correctness over chosen bytes sufficient for this audit?
- [ ] Are HKDF labels/contexts in `TLS13.Keys` and `TLS13.KeySchedule` tied to
      the TLS 1.3 RFC strings intended for this profile?

## Certificate and signature TCB audit

Pure spec file: `src/spec/TLS13.X509.Spec.fsti`.

Pulse/OpenSSL boundary: `src/impl/TLS13.OpenSSL.fsti`.

Additional implementation interface: `src/impl/TLS13.X509.fsti`.

Trusted assumptions:

- `X509.Spec.validate_chain` captures the intended hostname/time/trust-store
  validation policy.
- `OpenSSL.auth_context_new` creates an auth context for client validation.
- `OpenSSL.validate_certificate_for_local_event` returns a payload satisfying
  `CT.local_input_wf LocalValidateCertificate` on success.
- `OpenSSL.verify_certificate_signature_for_local_event` returns a payload
  satisfying `CT.local_input_wf LocalVerifyCertificateSignature` on success.
- `OpenSSL.server_credentials_new` creates server credentials with an abstract
  `server_credential_identity`.
- `OpenSSL.sign_certificate_verify` signs input so that
  `C.verify_signature RsaPssRsaeSha256 credential_identity input signature`
  holds.
- `OpenSSL.copy_server_certificate_chain` returns exactly the stored certificate
  chain bytes.

Sign-off questions:

- [ ] Does `X509.Spec.validate_chain` model the certificate policy we actually
      want to trust?
- [ ] Does the OpenSSL implementation enforce hostname, validation time, trust
      anchors, and chain construction consistently with `X509.Spec`?
- [ ] Is `peer_identity.permitted_signature_schemes` checked at the right place?
- [ ] Does `server_credentials_new` ensure the private key corresponds to the
      certificate chain's leaf public key, even though the spec exposes only an
      existential `credential_identity`?
- [ ] Does `sign_certificate_verify` use exactly the TLS 1.3
      CertificateVerify input bytes from the verified serializer?
- [ ] Are RSA-PSS parameters fixed to `RsaPssRsaeSha256` as intended?

## I/O and runtime TCB audit

Audit file: `src/impl/TLS13.IO.fsti`.

Trusted operations:

- TCP connect/listen/accept/close.
- `read` appends an arbitrary chunk to the channel received history and returns
  exactly that chunk in the output prefix.
- `write` appends the requested output prefix to the channel sent history and
  currently specifies `n == len`.

Sign-off questions:

- [ ] Is the abstract channel-history model faithful enough for TCP stream I/O?
- [ ] Is it acceptable that `write` is specified as a full write (`n == len`)?
- [ ] Are EOF, socket errors, short reads, and close behavior represented at the
      right abstraction level?
- [ ] Do runtime C drivers call the verified driver APIs without bypassing
      retained-buffer or history accounting?
- [ ] Are generated test certificates and OpenSSL interop tests sufficient smoke
      coverage for this TCB boundary?

## Extraction and C boundary audit

Relevant directories:

- `runtime/`
- `c_stubs/`
- `_extract/` generated bundles
- `third_party/hacl-star/`

Sign-off questions:

- [ ] Are all C entry points routed through the verified Pulse driver facades?
- [ ] Are handwritten C stubs limited to the intended TCB interfaces?
- [ ] Are buffer lengths passed consistently as `SizeT.t` and checked before
      writes?
- [ ] Are ownership/freeing conventions in extracted code and C wrappers
      leak-free for success and failure paths?
- [ ] Are the tested bundles the same bundles intended for deployment?

## Current known limitations before broader claims

- The paired theorem is a first-epoch/no-KeyUpdate theorem.
- Multi-epoch KeyUpdate agreement is planned but not proved.
- `TLS13.Spec.WireFormatLemmas.fsti` is interface-only and must be treated as a
  TCB until implemented or replaced by EverParse-derived facts.
- Parser/serializer implementation interfaces are trusted boundaries.
- Crypto and X509 semantics are trusted through their spec interfaces and
  HACL/OpenSSL-backed implementations.
- This is a functional-correctness/agreement theorem, not a full cryptographic
  security theorem.

## Final sign-off checklist

- [ ] Client public driver API is the intended top-level client surface.
- [ ] Server public driver API is the intended top-level server surface.
- [ ] Successful `connect` / `accept` states expose exactly the facts needed for
      paired agreement.
- [ ] Paired transport histories are an acceptable environmental precondition.
- [ ] Paired key-derivation checkpoints are an acceptable remaining semantic
      checkpoint precondition.
- [ ] First-epoch/no-KeyUpdate restriction is acceptable for this theorem.
- [ ] Wire-format lemma boundary is acceptable as a named TCB.
- [ ] Parser/serializer contracts are acceptable as implementation TCBs.
- [ ] Crypto function specs and X25519 agreement lemma are acceptable TCB facts.
- [ ] Certificate validation/signing assumptions match the desired deployment
      policy.
- [ ] I/O history model is the intended abstraction of TCP.
- [ ] Remaining limitations are documented and not accidentally hidden by theorem
      names.
