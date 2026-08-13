# Server / client parity: gap analysis and interop test plan

Status date: 2026-08-12.  Branch `interop`.

## Why this document exists

The top-100 interop push (commits `8b0430278` .. `db6f7fb71`) moved the
verified **client** three times in a row:

| commit | client gained | sweep |
| --- | --- | --- |
| `baaa66317` | cross-record handshake reassembly | 77 -> 83 |
| `4b5e7a086` | `TLS_AES_128_GCM_SHA256` negotiation | 83 -> 88 |
| `db6f7fb71` | `secp256r1` key exchange | 88 -> 96 |

The verified **server** did not move with it.  Nothing in the test suite
noticed, because every server-side test pins its OpenSSL peer to the one
profile the server implements -- `test_extracted_server_openssl_client` sets

```c
SSL_CTX_set_ciphersuites(ctx, "TLS_CHACHA20_POLY1305_SHA256")
SSL_CTX_set1_groups_list(ctx, "X25519")
SSL_CTX_set1_sigalgs_list(ctx, "rsa_pss_rsae_sha256")
```

which is exactly the server's own profile.  A test configured from the
implementation under test cannot discover what the implementation cannot do.

This document records the analysis, and `test/unit/test_server_interop_matrix.c`
plus `test/unit/test_atlas_loopback.c` implement the standing gate that keeps
the analysis true.

## Summary

The two endpoints **are** interoperable today: the verified client's current
offer is one the verified server can serve, and `make test-atlas-loopback`
proves it end to end, including KeyUpdates in both directions.  That is the
good news, and it is not luck: the client offers ChaCha20-Poly1305 first and
sends an X25519 key share alongside its P-256 one, so the server's single
profile is always inside the client's offer.

They are **not** at parity.  The client can negotiate four things the server
cannot serve, and every one of them is a capability a real peer may insist on:

| capability | client | server | first blocking site |
| --- | --- | --- | --- |
| `TLS_CHACHA20_POLY1305_SHA256` | yes | yes | -- |
| `TLS_AES_128_GCM_SHA256` | yes | **no** | `TLS13.Spec.StateMachine.server_hello_matches_selection:1476` |
| X25519 key exchange | yes | yes | -- |
| `secp256r1` key exchange | yes | **no** | `TLS13.Spec.StateMachine:1626` (server `LocalDeriveSharedSecret`) |
| cross-record handshake reassembly | yes | **no** | `TLS13.Spec.StateMachine.legal_protected_handshake_step:1986` |
| HelloRetryRequest | n/a (rejects) | **no** | `TLS13.Impl.Serializer.Handshake.fst:1704` |
| short/empty `legacy_session_id` echo | n/a | **no** | `TLS13.Wire.Semantics.clientHello_session_id_32:71` |
| `rsa_pss_rsae_sha256` credentials | yes | yes | -- |
| `ecdsa_secp256r1_sha256` credentials | verifies | **cannot present** | `TLS13.Impl.Server.Auth.fst:320` |
| KeyUpdate (send, receive, mandated reply) | yes | yes | -- |
| ChangeCipherSpec tolerance | yes | yes | -- |
| TCP short reads / retained buffer | yes | yes | -- |

The parity risk is therefore **asymmetric and latent**: today the client's
offer happens to contain the server's profile, so nothing is broken.  The
moment the client's offer is widened past that intersection -- dropping
ChaCha20 for AES-GCM, or dropping the X25519 share now that P-256 works -- the
two verified endpoints stop interoperating, and until now no test would have
said so.

## The gaps in detail

### G1. The server cannot select `TLS_AES_128_GCM_SHA256`

The *record layer* is already algorithm-agile for both roles.  Commit
`c7ac7eea7` replaced the key-length inference (`C.aead_alg_of_key`) with an
explicit tag threaded from the accepted ServerHello: `R.direction_state` carries
`alg : C.aead_alg`, `CS.traffic_key_material` carries `traffic_alg`, and the
server's own key installation already reads the negotiated algorithm --
`TLS13.Spec.StateMachine.fst:947` derives the client application traffic
material with `traffic_key_material_for_secret (negotiated_aead_alg hs) secret`.

What is missing is *selection*.  The spec pins it:

```fstar
(* TLS13.Spec.StateMachine.fst:1466 *)
let server_hello_matches_selection (selection:...) (sh:GSH.serverHello) : prop =
  ...
  selection.server_selected_cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256 /\
  Sem.serverHello_cipher_suite sh == Some selection.server_selected_cipher_suite /\
  ...
```

and the implementation repeats the literal `T.TLS_CHACHA20_POLY1305_SHA256` at
55 sites across `TLS13.Impl.Server.fst`,
`TLS13.Impl.Server.Send.fst`, `TLS13.Impl.Server.Driver.BufferedHandshake.fst`,
`TLS13.Impl.Server.Driver.BufferedWorkflow.fst` and
`TLS13.Impl.Server.CanonicalProtocol.fst`.  `mk_server_hello_witness` already
takes the suite as a parameter, so the ServerHello *constructor* is ready; it is
the callers, and the spec-level `server_hello_matches_selection`, that fix it.

Note that `negotiated_aead_alg` reads the algorithm off `hs_server_hello`, i.e.
off the message the server itself sent.  So once the server may send an AES
ServerHello, the key schedule follows without further work -- the change is
concentrated in selection and in the exact-length ServerHello lemmas, not in
the record layer.

Interop consequence: a peer that offers only AES-GCM cannot connect.  That is
not hypothetical -- it is the configuration Microsoft's properties and several
of the top-100 hosts use, which is precisely why the client needed AES-128-GCM.

### G2. The server has no `secp256r1` key exchange, and no HelloRetryRequest

Two independent blockers, both fatal on their own.

**The parser rejects the ClientHello.**  `clientHello_representable`
(`TLS13.Wire.Spec.fsti:307`, revealed at `:314`) requires the `ch_extensions`
scan to yield `Some key_share`, and `lemma_ch_extensions_connect` (`:334`)
pins that key share to `Sem.clientHello_key_share_x25519`.  A ClientHello whose
only key share is P-256 is therefore not representable, and the synth layer
turns it into `None` before any state-machine code runs.  This is the exact
mirror image of the bug commit `db6f7fb71` fixed on the client side, where
`serverHello_representable` required `Some? (serverHello_key_share_x25519 b) &&
length = 32` and had to be generalised to `Some? (Sem.serverHello_kex_share b)`.

**The state machine's server arm is X25519-only.**  The client's
`LocalDeriveSharedSecret` dispatches on the negotiated group (`:1607`, via
`server_hello_kex` and `start_kex_private g`).  The server's arm does not:

```fstar
(* TLS13.Spec.StateMachine.fst:1626 *)
| LocalDeriveSharedSecret shared, ControlHandshaking HsClientHelloReceived ->
  model.model_config.config_role == ServerEndpoint /\
  ...
     (match client_hello_key_share selection.server_selected_client_hello with
      | Some k -> C.x25519_shared sk k == Some shared
      | None -> False)
```

`server_handshake_selection` itself is X25519-shaped
(`server_key_share_private : option C.x25519_private`,
`server_key_share_public : C.x25519_public`, `:190`), even though it carries a
`server_selected_group : T.named_group` field that the acceptability predicate
does check against `cfg.server_supported_groups`.  The bookkeeping is there; the
crypto is not.  `TLS13.Impl.Server.Send.fst:201` hard-codes
`{ GKE.group = GNG.X25519; ... }` in the emitted ServerHello.

The client-side pattern to copy already exists: `TLS13.KEX` is the single
group-dispatching module, `C.kex_group` / `C.kex_public g` / `C.kex_shared g`
are the agile spec vocabulary, and `Repr.kex_share_storage` is the 65-byte
uniform runtime buffer with an explicit group tag.

**No HelloRetryRequest.**  `M.HelloRetryRequest` exists only as a message the
*client* receives and always rejects (`:982`), and
`TLS13.Impl.Serializer.Handshake.fst:1704` states plainly that the
implementation does not support it.  Without HRR the server cannot ask a client
that guessed P-256 to resend with X25519, so "supported_groups lists X25519 but
key_share carries only P-256" -- OpenSSL's behaviour when P-256 is listed first
-- is unserviceable.

### G3. The server cannot reassemble a handshake message split across records

Commit `baaa66317` gave the client a third kind of protected-handshake step: a
BUFFERING step that takes delivery of a record, appends its plaintext to a
pending reassembly buffer, advances the record read sequence, and delivers no
message.  It is what made Meta's three-record server flight work.

That mechanism is **client-only by construction**:

```fstar
(* TLS13.Spec.StateMachine.fst:1979 *)
let legal_protected_handshake_step (model:connection_model) (step:...) : GTot prop =
  ...
  model.model_config.config_role == ClientEndpoint /\
  (if step.protected_handshake_buffering then ... )
```

and `protected_handshake_buffering_stage` (`:1972`) enumerates only client
stages.  The server does not receive through `ConnProtectedHandshake` at all: it
takes the client Finished as an ordinary `ConnNetworkEvent`
(`:936`), and `TLS13.Impl.Server.Network.process_client_hello` requires the
record fragment to be *exactly* the serialized ClientHello
(`TLS13.Impl.Server.Network.fsti:60`).

Two distinct things must not be confused here, and the test suite now separates
them explicitly:

* **TCP short reads** -- one TLS record arriving in several `read()` calls -- are
  handled.  `decode_network_buffer` returns `NetworkBufferNeedMoreInput` and the
  driver retries against a retained buffer with `consumed_len == 0`
  (`TLS13.Impl.Server.Driver.BufferedNetwork.fst:457`).  This is the
  `tcp-dribble` cell, and it passes.
* **Record fragmentation** -- one handshake message arriving as two TLS records
  -- is not handled.  This is the `clienthello-across-two-records` cell, and it
  fails.

Interop consequence: any peer whose ClientHello does not fit one record, or
whose stack fragments it, cannot connect.  This is a live concern as client
hellos grow (post-quantum key shares push a ClientHello past 1500 bytes and
some stacks split them).

A related, milder limitation applies to both roles: `parse_tls_message`
(`TLS13.Wire.Spec.fst:921`, handshake arm at `:927`) requires `consumed == B.length fragment`, so several
handshake messages coalesced into one record are rejected rather than drained.

### G4. The server echoes a padded `legacy_session_id`

`Sem.clientHello_session_id_32` (`TLS13.Wire.Semantics.fst:71`) normalises the
client's `legacy_session_id` to exactly 32 bytes, and
`TLS13.Impl.Server.Send.fst:221` echoes those 32 bytes verbatim -- clamping to
32 zero bytes if the stored value is not 32 long.  The whole ServerHello size
reasoning depends on this: `lemma_mk_server_hello_witness_bytesize`
(`Send.fst:252`) proves the ServerHello is *exactly* 122 bytes, on the
hypothesis `Seq.length session_id == 32`.

A client in middlebox-compatibility mode always sends a 32-byte session id, so
this is invisible in practice -- and it is why the existing OpenSSL test passes
with compatibility mode deliberately left on.  A client with compatibility mode
*off* sends an empty session id, gets 32 zero bytes back, and must abort under
RFC 8446 4.1.3.  This is the `no-middlebox-compat` cell.

### G5. The server can only present an RSA-PSS credential

`TLS13.Impl.Server.Auth.fst:320` builds the CertificateVerify with
`GCV.algorithm = T.Rsa_pss_rsae_sha256` unconditionally, and
`TLS13.Impl.Server.CanonicalProtocol.fst:131` requires
`selection.server_selected_signature_scheme == T.Rsa_pss_rsae_sha256`.  The
client *verifies* both `Rsa_pss_rsae_sha256` and `Ecdsa_secp256r1_sha256` (its
`config_signature_schemes` lists both, and the top-100 sweep depends on ECDSA
chains), so this too is a one-sided capability.  This gap is lower priority
than G1-G3: it needs an ECDSA signing credential and an ECDSA test certificate,
not just negotiation.

### What is NOT a gap

Worth stating, because these were checked and are fine:

* **ChangeCipherSpec tolerance.**  `TLS13.Spec.StateMachine.fst:1202` accepts
  `M.TlsChangeCipherSpec` at any handshaking stage for either role, and
  `TLS13.Impl.Server.Network.process_change_cipher_spec` returns `StepOk` with
  zero output.
* **`legacy_session_id` echo for 32-byte ids** (RFC 8446 D.4) -- implemented,
  and the existing OpenSSL test runs with middlebox compatibility on precisely
  to cover it.
* **KeyUpdate**, in all three shapes: server-initiated rotation, receive-side
  rotation on a peer KeyUpdate, and the mandated `update_not_requested` reply to
  an `update_requested`.  Covered by the existing server test and now also by
  the loopback test.
* **Server preference over client preference.**  The server selects ChaCha20
  even when the client lists it last, which RFC 8446 4.1.1 permits.  The
  `aes-first-chacha-last` cell pins this.
* **Retained-buffer short reads**, as above.

## The interop test plan

Three properties are wanted, and they need three different instruments.

### P1. The two verified endpoints interoperate -- `test-atlas-loopback`

`test/unit/test_atlas_loopback.c` forks the verified server and connects the
verified client to it, then drives eight application records and four KeyUpdates
from each side.

This is the only test in the tree in which the ClientHello under test is the one
ATLAS actually sends.  It is the direct regression gate on the intersection
discussed above: widen the client's offer past the server's profile and this
test fails, while every OpenSSL-paired test stays green.

The client driver owns its socket (it binds, connects and handshakes in one
call), so the harness cannot hand it a pre-connected fd and cannot wait on the
peer's `listen()`.  It retries the whole connect for a bounded window instead.
Retrying cannot mask a rejection: the server serves exactly one connection and
then exits, so a genuine failure leaves nothing listening, and the server's own
exit status fails the test independently of what the client concludes.

### P2. The server's capability surface is pinned -- `test-server-matrix`

`test/unit/test_server_interop_matrix.c` drives OpenSSL clients across five
axes -- cipher suites, key-exchange groups, signature schemes,
middlebox-compatibility mode, and framing -- and compares the observed outcome
of every cell against a recorded expectation.

Two design decisions carry the value:

1. **Expectations are two-sided.**  A cell recorded as a gap fails the test if
   it starts *succeeding*.  When someone implements G1 or G2, the harness names
   the row to flip, so the capability change is recorded in the same commit as
   the implementation.  A "known failures are skipped" harness would let a gap
   close silently and then reopen silently.
2. **Successful cells assert the negotiated parameters**, not just success:
   `SSL_get_cipher_name` and `OBJ_nid2sn (SSL_get_negotiated_group ...)` are
   checked against the suite and group the case is about.  Without that, the
   `x25519-and-p256` cell would still pass if the server had picked P-256, and
   `aes-first-chacha-last` would still pass if it had picked AES -- which are
   exactly the outcomes the cells exist to distinguish.

The framing axis is served by an in-process TCP proxy that re-frames the
client->server stream at the record layer.  It re-frames only *cleartext*
handshake records: a protected record is a single AEAD-sealed unit, so
splitting its ciphertext would test nothing but the tag.  The `tcp-dribble` cell
runs through the same proxy code and passes, which is what makes the
`clienthello-across-two-records` failure attributable to record fragmentation
rather than to the proxy.

Current ledger (all fourteen cells agree):

```
baseline-chacha-x25519             ok        the server's single profile
openssl-defaults                   ok        stock OpenSSL offer
atlas-client-offer                 ok        what the verified client sends
aes128-only                        refused   G1
aes256-only                        refused   out of scope for both roles
aes-first-chacha-last              ok        server preference wins
p256-only                          refused   G2
x25519-and-p256                    ok        X25519 selected
p256-first-x25519-listed           refused   G2 (needs HelloRetryRequest)
rsa-pss-only                       ok        the test credential's scheme
ecdsa-only                         refused   G5
no-middlebox-compat                refused   G4
tcp-dribble                        ok        retained-buffer retry loop
clienthello-across-two-records     refused   G3
```

### P3. The established connection keeps working -- existing tests

`test-openssl-sclient` remains the deep post-handshake test: sixteen
application records and eight KeyUpdates with on-the-wire accounting via
OpenSSL's message callback.  The matrix deliberately does *not* duplicate this;
it runs one echo per cell, because it measures which offers are reachable, not
what happens afterwards.

### Where this runs

Both targets are in `make test`, which is what CI runs
(`.github/workflows/ci.yml`, the `tls-root (make test)` job).  They need no
network access -- everything is loopback -- so they are safe there, unlike the
top-100 sweep in `test/interop/sweep.sh`.

## Recommended order for closing the gaps

1. **G1 (AES-128-GCM selection).**  Highest interop value per unit of proof
   work: the record layer, key schedule and ServerHello constructor are already
   agile, so the change is concentrated in those 55 selection sites and the
   exact-length ServerHello lemmas.  Flip the `aes128-only` cell.
2. **G3 (cross-record ClientHello reassembly).**  Independent of negotiation,
   and increasingly load-bearing as client hellos grow.  The client's buffering
   step is the design to mirror, but on the cleartext network-buffer path rather
   than the protected one.  Flip `clienthello-across-two-records`.
3. **G2 (secp256r1, then HelloRetryRequest).**  The largest of the three:
   generalising `clientHello_representable`, making
   `server_handshake_selection` group-indexed through `C.kex_group`, and routing
   the server's ECDH through `TLS13.KEX`.  HRR is a separate, later step.  Flip
   `p256-only`, then `p256-first-x25519-listed`.
4. **G4 (variable-length session-id echo).**  Small in wire terms, but it
   unpins the exact 122-byte ServerHello length that the send path's length
   reasoning currently rests on.  Flip `no-middlebox-compat`.
5. **G5 (ECDSA credentials).**  Needs an ECDSA test credential as well as
   negotiation.  Flip `ecdsa-only`.
