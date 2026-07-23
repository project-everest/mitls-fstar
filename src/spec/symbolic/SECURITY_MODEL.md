# TLS 1.3 symbolic security model

This directory contains a machine-checked, extrinsic DY* model of the
repository's TLS 1.3 client and server. The existing TLS state machine and
`TLS13.Spec.StateMachine.Canonical.canonical_wire_step` remain authoritative:
the symbolic product records cryptographic meanings and security events while
each honest step advances the existing concrete model.

## Scope

The proof covers the full 1-RTT, server-authenticated profile with X25519,
RSA-PSS-RSAE-SHA256, SHA-256/HMAC/HKDF, and
TLS_CHACHA20_POLY1305_SHA256. It covers both endpoint roles, protected
handshake records, generation-zero application traffic, bidirectional
application data, and segmented application-data sends.

It does not cover PSK, resumption, 0-RTT, HelloRetryRequest, client
certificates, post-handshake authentication, KeyUpdate, exporters, alternate
algorithms, certificate path building or revocation, forward secrecy,
post-compromise security, liveness, side channels, or a computational
reduction for the concrete cryptographic implementations.

## Model boundary

`TLS13.Symbolic.Product` keeps concrete connection states and symbolic shadows
in lockstep. Honest wire steps carry `canonical_wire_step`; projection erases
the symbolic components, and conditional lifting reconstructs product
executions from concrete executions with explicit realization evidence.
`TLS13.Symbolic.Bridge.represents` is execution-indexed and relational: there
is deliberately no global function from concrete bytes to symbolic terms.

Protected-record realizations bind the exact concrete key, static IV, TLS
nonce computation, five-byte AAD, inner plaintext, ciphertext, role,
direction, epoch, and sequence number to an `AeadEnc` term. Application sends
follow the same recursive segmentation as `sent_application_data_records_seal_from`.
The public symbolic nonce is an injective sequence token; the AEAD bridge ties
it, for this execution, to the exact concrete `tls13_record_nonce` output.

Honest application input is secret by default. Its symbolic content carries a
session/application-state label and is embedded in a structured
`application_plaintext`; attacker-controlled data is not relabeled as honest
secret input.

## Headline theorem map

| Claim | Main theorem |
| --- | --- |
| Conditional concrete execution lifting | `Product.concrete_execution_has_product_lift` |
| Concrete projection and reachability | `Product.reachable_endpoint_projects_exactly` |
| DY trace invariant | `Invariant.secure_product_execution_preserves_invariant` |
| Attacker knowledge closure | `Invariant.attacker_only_knows_publishable` |
| Named-server authentication | `Authentication.concrete_client_acceptance_authenticates_named_server` |
| Anonymous-client key confirmation | `Authentication.concrete_server_acceptance_confirms_anonymous_client` |
| Injective server agreement | `Authentication.injective_server_agreement` |
| Full-session agreement | `Authentication.concrete_full_session_agreement` |
| Schedule-secret secrecy | `Secrecy.established_schedule_secret_secrecy` |
| Symbolic key separation | `Secrecy.client_server_handshake_traffic_separated`, `Secrecy.client_handshake_application_traffic_separated`, `Secrecy.server_handshake_application_traffic_separated`, `Secrecy.client_server_application_traffic_separated`, `Secrecy.finished_record_key_separated`, `Secrecy.record_key_iv_separated` |
| Per-key nonce freshness | `RecordSecurity.generated_record_nonce_was_unused` |
| Record origin and integrity | `RecordSecurity.accepted_record_has_matching_sent_origin` |
| Direction/epoch substitution rejection | `RecordSecurity.cross_direction_record_substitution_rejected`, `RecordSecurity.cross_epoch_record_substitution_rejected` |
| Replay rejection after sequence advance | `RecordSecurity.protected_record_replay_rejected_after_sequence_advance` |
| Secret application plaintext structure | `RecordSecurity.sent_application_record_has_secret_structure` |
| Application-data confidentiality | `RecordSecurity.recorded_honest_application_data_secrecy` |
| Exact canonical record linkage | `RecordSecurity.honest_canonical_transition_uses_exact_record_semantics`, `RecordSecurity.protected_send_realization_is_complete` |

Authentication theorems expose credential compromise where server
impersonation is relevant. Secret-schedule theorems expose the labels supplied
for the two ephemeral-usage terms; interpreting these as endpoint-state
compromise additionally requires tying them to the intended non-public
principal-state labels. Record integrity exposes the live AEAD key: a
successful symbolic decryption has a matching sent event unless that exact key
is publishable. Application confidentiality separately exposes compromise of
the application state that owned the plaintext.

## Assumption ledger

| Assumption or trusted boundary | Source | Consumers |
| --- | --- | --- |
| Intended bridge from fresh concrete bytes to role/session-specific `RandGen` entries | `Bridge.fresh_value_bridge` | Defined boundary; not yet connected to the headline proof chain |
| Intended bridge from X25519 public/shared computations to ideal `DhPub`/`Dh` terms | `Bridge.x25519_public_bridge`, `Bridge.x25519_shared_bridge` | Defined boundary; not yet connected to product lifting or key lineage |
| Intended SHA-256 and HKDF bridges | `Bridge.hash_bridge`, `Bridge.hkdf_extract_bridge`, `Bridge.hkdf_expand_label_bridge` | Defined boundary; not yet connected to product lifting or key lineage |
| HMAC computation corresponds to an ideal DY MAC | `Bridge.hmac_bridge` | Explicit Finished authentication premise |
| RSA-PSS signing and verification correspond to ideal DY signatures | Signature predicates in `Bridge` | CertificateVerify origin and server authentication |
| Validated server name and leaf key match a trusted registry entry | `Bridge.x509_identity_bridge` | Named-server authentication |
| ChaCha20-Poly1305 seal/open correspond to ideal `AeadEnc` | `Bridge.aead_seal_bridge`, `Bridge.aead_open_bridge` | Record origin, integrity, replay, confidentiality |
| Concrete cryptographic functions and X.509 validation satisfy their abstract F* interfaces | `TLS13.Crypto.Spec`, `TLS13.X509.Spec` | Concrete side of the connected bridge predicates |
| Each honest transition supplies hygienic event/state entries | `Invariant.secure_product_step`, `Invariant.trace_extension_hygienic` | Reachable DY trace invariant |
| A concrete execution supplies well-formed product states, endpoint refinement, representation extension, event realization, and exact AEAD record witnesses | `Product.symbolically_realizable_execution` | Conditional concrete lifting |
| Key-schedule terms have complete symbolic lineage and match the installed target | `Secrecy.complete_key_schedule_lineage`, `Secrecy.schedule_target_matches` | Schedule-secret secrecy |
| Ephemeral terms have expected usages and caller-supplied labels | `Secrecy.ephemeral_pair_has_labels` | Schedule-secret secrecy; intended endpoint-state labels are not forced |
| DY constructors model perfect cryptography and attacker deduction | Pinned extrinsic DY* core | All symbolic security theorems |

These assumptions do not assert global injectivity or collision freedom for
concrete X25519, hashes, HKDF, signatures, or AEAD. Symbolic purpose
separation is constructor/label separation, not concrete non-collision.
Forward secrecy is not claimed.

`SYMBOLIC_AUDIT.md` gives the detailed skeptic's review, including bridge
connectivity, realization inhabitation, label interpretation, context
agreement, and theorem-by-theorem overclaim checks.

## Verification

DY* is verified with Z3 4.15.3 in its separate cache. TLS symbolic modules are
verified with Z3 4.13.3 and consume the checked DY* core. The symbolic files
set no exceptional local SMT resource limits.

```sh
make -j"$(nproc)" verify-symbolic-model
make -j"$(nproc)" verify-symbolic-invariant
make -j"$(nproc)" verify-symbolic-authentication
make -j"$(nproc)" verify-symbolic-secrecy
make -j"$(nproc)" verify-symbolic-records
make -j"$(nproc)" verify-symbolic
```

`PLAN_SYMBOLIC.md` records the complete phased design and the distinction
between required claims and the optional forward-secrecy stretch goal.
