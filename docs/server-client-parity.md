# Server / client parity: gap analysis and interop test plan

Status date: 2026-08-13.  Branch `interop`.

**Progress:** G1 (server-side `TLS_AES_128_GCM_SHA256` selection), G4
(variable-length `legacy_session_id` echo) and G5 (ECDSA server credentials)
are **closed**; see the sections below.  G2 and G3 remain open, and both are
research-scale rather than incremental -- the closing sections say why, now
from *measurement* rather than estimate: G3's buffering design was built
against the whole tree and its fallout enumerated, and G2's surface was
counted.

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

They are **not** at parity.  The client can still negotiate three things the
server cannot serve, and every one of them is a capability a real peer may
insist on:

| capability | client | server | first blocking site |
| --- | --- | --- | --- |
| `TLS_CHACHA20_POLY1305_SHA256` | yes | yes | -- |
| `TLS_AES_128_GCM_SHA256` | yes | yes (G1 closed) | -- |
| X25519 key exchange | yes | yes | -- |
| `secp256r1` key exchange | yes | **no** | `TLS13.Spec.StateMachine:1626` (server `LocalDeriveSharedSecret`) |
| cross-record handshake reassembly | yes | **no** | `TLS13.Spec.StateMachine.legal_protected_handshake_step:1986` |
| HelloRetryRequest | n/a (rejects) | **no** | `TLS13.Impl.Serializer.Handshake.fst:1704` |
| short/empty `legacy_session_id` echo | n/a | yes (G4 closed) | -- |
| `rsa_pss_rsae_sha256` credentials | yes | yes | -- |
| `ecdsa_secp256r1_sha256` credentials | verifies | yes (G5 closed) | -- |
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

### G1. The server cannot select `TLS_AES_128_GCM_SHA256` -- CLOSED

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

#### How it was closed

The obvious shape -- thread a `cipher_suite : U16.t` parameter from the
selection step down to the ServerHello writer -- would have touched some fifteen
functions across ten modules, each with its own pre/post-condition to restate.
It was rejected in favour of making the choice a **deterministic function of
state the server already stores**:

```fstar
(* TLS13.Impl.ConnectionState.Model.fsti *)
noextract
let server_selected_suite (st:CS.connection_state) : T.cipher_suite =
  match st.CS.cs_model.CS.model_handshake.CS.hs_client_hello with
  | Some ch ->
    if cipher_suite_offered_b (Sem.clientHello_cipher_suites ch)
         T.TLS_CHACHA20_POLY1305_SHA256
    then T.TLS_CHACHA20_POLY1305_SHA256
    else T.TLS_AES_128_GCM_SHA256
  | None -> T.TLS_CHACHA20_POLY1305_SHA256
```

Because the policy reads only the stored ClientHello mirror, *any* later point
in the flow can recompute it and get the same answer.  So the ServerHello writer
does not need the suite passed to it: `TLS13.Impl.ConnectionState.Queries.
read_negotiated_server_suite` re-scans the stored ClientHello at write time and
returns the wire code, with the postcondition
`IM.cipher_suite_of_u16 suite == CM.server_selected_suite st0`.  The fifty-five
literal sites became fifty-five occurrences of `CM.server_selected_suite 'st0`,
a mechanical substitution with no new parameters.

Three supporting pieces were needed:

* **A decidable offer test.**  `CS.cipher_suite_offered` is `prop`-valued, so a
  `Tot` function cannot scrutinise it.  `cipher_suite_offered_b` is its boolean
  companion, tied to it by `lemma_cipher_suite_offered_b` (an SMT pattern), so
  the policy is total and the spec-level lemmas still speak in `prop`.
* **A conclusive scan.**  The runtime scan `scan_u16_for` previously only
  promised soundness on `found == true`.  Deciding *absence* of ChaCha20 --
  which is what selects the fallback -- needs the negative direction too, so its
  postcondition and loop invariant were strengthened to
  `found == false ==> forall j < len. bytes[j] <> target`.
* **A linkage between the selection and the write.**  The spec requires the
  emitted suite to equal the *stored selection's* suite, while the writer can
  only recompute the *policy*.  The two are tied together by adding
  `selection.server_selected_cipher_suite == CM.server_selected_suite st` to the
  `LocalSendServerHello` arm of `ST.server_local_event_input_ready`.  That arm
  is cheap to strengthen precisely because
  `server_internal_ready_implies_kind_ready` deliberately excludes it, so its
  only producers are explicit lemmas in `TLS13.Impl.Server.Send` and the
  concrete driver code -- there is no generic introduction rule to repair.

`server_hello_matches_selection` now requires only
`H.is_supported_cipher_suite selection.server_selected_cipher_suite`, and
`TLS13.Impl.Server.CanonicalProtocol.server_supported_profile_selection`
additionally requires the configuration to offer AES-128-GCM, which the default
server config does.

Observable result: the `aes128-only`, `aes256-then-aes128`, `aes128-tcp-dribble`
and `aes128-x25519-and-p256` matrix cells all negotiate
`TLS_AES_128_GCM_SHA256` against a real OpenSSL client, and the four
ChaCha-preferring cells are unchanged -- server preference still wins when both
are offered.

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

The mirror-the-client design for closing this was subsequently **built against
the whole tree and measured**; the spec-level fallout turned out to be small and
mechanical, but the implementation needs a concrete reassembly buffer in the
server's connection representation before the spec mechanism buys any
capability.  The full measurement -- which modules need a new match
arm, why `lemma_received_client_hello_raw_length` has to be restated as a
determinism property rather than a length one, which three cross-endpoint
pairing theorems have to be restricted, and why the decoder rather than the
state machine is the blocker -- is recorded in the roadmap entry for G3 below.

### G4. The server echoes a padded `legacy_session_id` -- **CLOSED**

*Was:* `Sem.clientHello_session_id_32` normalised the client's
`legacy_session_id` to exactly 32 bytes and the send path echoed those 32 bytes
-- clamping to 32 *zero* bytes when the stored value was shorter.  The whole
ServerHello size reasoning rested on this: `lemma_mk_server_hello_witness_bytesize`
proved the ServerHello was *exactly* 122 bytes, on the hypothesis
`Seq.length session_id == 32`.  A client with middlebox-compatibility mode off
sends an empty session id, got 32 zero bytes back, and had to abort under
RFC 8446 4.1.3.

*Now:* the session id is carried the way key shares already were -- a
fixed-width buffer plus an explicit length, with the length as the sole carrier
of the wire width:

* `TLS13.Wire.Semantics.clientHello_session_id` returns the offered id at its
  true width (`{ Seq.length r <= 32 }`), and `pad_session_id_32` zero-pads it
  into the 32-byte mirror buffer.  `serverHello_session_id_echo` is likewise
  width-carrying.  This is exactly the shape `CryptoSpec.pad_share_65` uses for
  a key share whose logical width depends on the group.
* The runtime mirror stores the width.  `IM.client_hello` and `IM.server_hello`
  gained a `*_session_id_len : SZ.t` field, and -- because the stored
  `IM.client_hello` slot is allocated once and its scalar fields are never
  rewritten -- `handshake_message_storage` gained a `client_hello_session_id_len
  : box SZ.t`, alongside the other ClientHello metadata lengths.
  `CQ.read_client_hello_session_id` now returns that width.
* Sizes follow the width.  `lemma_server_hello_of_selection_bytesize` and
  `lemma_mk_server_hello_witness_bytesize` now prove the ServerHello *message*
  is `90 + |sid|` bytes and `lemma_sh_size` that its *record* is `95 + |sid|`
  (122/127 only in the compatibility case).  Every `== 127` precondition on the
  send path became `== 95 + Seq.length (CM.stored_client_hello_session_id st)`,
  and the two fixed-size output buffers (in `Serializer.ServerHello` and in the
  buffered driver) became heap `Pulse.Lib.Vec`s sized at run time.
* The linkage that makes this sound is carried where G1's already is: the
  `LocalSendServerHello` arm of `ST.server_local_event_input_ready` now states
  `hs_client_hello == Some selection.server_selected_client_hello`, so the id
  the writer recovers from the mirror is provably the id the Model-level
  canonical ServerHello echoes.

`no-middlebox-compat` is `ok`, together with three new cells that cross the
empty-id path with the suite-fallback, retry-loop and two-key-share axes.

### G5. The server can only present an RSA-PSS credential -- **CLOSED**

**Was:** `TLS13.Impl.Server.Auth.fst` built the CertificateVerify with
`GCV.algorithm = T.Rsa_pss_rsae_sha256` unconditionally and wrote the literal
wire code `0x0804us`; `TLS13.Impl.Server.CanonicalProtocol.fst` and eight other
server modules *required* `selection.server_selected_signature_scheme ==
T.Rsa_pss_rsae_sha256`; and `tls13_openssl_server_credentials_new` rejected any
key whose `EVP_PKEY_base_id` was not `EVP_PKEY_RSA`.  The client meanwhile
verifies both schemes -- its `config_signature_schemes` lists both, and the
top-100 sweep depends on ECDSA chains -- so this was a one-sided capability.

**Now:** the scheme the server negotiates and signs under is a function of the
credential it was configured with, so the two cannot drift.

* `TLS13.Crypto.Spec.credential_signature_scheme : public_key -> signature_scheme`
  names the scheme a credential's key can produce, with
  `lemma_credential_signature_scheme_supported` (SMT-patterned) restricting it
  to `Rsa_pss_rsae_sha256` or `Ecdsa_secp256r1_sha256`.  Making it a function of
  the *identity* rather than a new ghost index on `O.is_server_credentials`
  is what kept the change small: the index would have rippled through ~74
  occurrences in 15 modules.
* `TLS13.Impl.ConnectionState.Repr.server_connection_config` sets
  `server_allowed_signature_schemes = [credential_signature_scheme identity]`.
  There is exactly one construction site for a `CS.server_config` and
  `credential_identity` was already a parameter of it, so no new config field
  and no signature change were needed.
* `CQ.select_supported_server_parameters_runtime` takes the wire code as a
  parameter and scans the client's `signature_algorithms` for *that* code
  rather than for `0x0804` (`Model.lemma_signature_schemes_match_{first,index,
  exists}_offer` are the scheme-generic replacements for the old RSA-specific
  offer lemmas).  The caller in the buffered driver obtains the code from the
  credential itself via the new `TLS13.OpenSSL.server_credential_signature_scheme`.
* `TLS13.Impl.Server.Auth` writes that same runtime code into
  `IM.certificate_verify_scheme` and states `GCV.algorithm =
  credential_signature_scheme identity` in the model, the two being tied
  together by `IM.signature_scheme_matches`.  `O.sign_certificate_verify`'s
  postcondition now says the signature verifies under
  `credential_signature_scheme identity`.
* `CS.server_selection_acceptable` needed no change: it already required the
  selected scheme to be in *both* the server's allowed list and the client's
  `signature_algorithms`.  The spec was agile all along; only the
  implementation was pinned.
* On the C side, `tls13_openssl_server_credentials_new` now accepts P-256 EC
  keys, the signing stub branches to plain `EVP_DigestSign` with SHA-256 for
  them, and `scripts/generate-test-certs.sh` issues an ECDSA P-256 leaf from the
  same test CA -- so the credential axis varies the leaf key and nothing else.

The matrix gained a **credential axis** and eight cells.  `ecdsa-only` is `ok`
against an ECDSA credential; the two cross cells
(`ecdsa-only-rsa-credential`, `rsa-pss-only-ecdsa-credential`) are `refused`,
which is the half of the property that matters: the server must still refuse an
offer its own key cannot satisfy.  `both-sigalgs-{rsa,ecdsa}-credential` show
the same client offer resolving either way purely as a function of the server's
key.

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

`test/unit/test_server_interop_matrix.c` drives OpenSSL clients across seven
axes -- cipher suites, key-exchange groups, signature schemes, the server's own
credential, middlebox-compatibility mode, framing, and protocol version -- and
compares the observed outcome of every cell against a recorded expectation.

Two design decisions carry the value:

1. **Expectations are two-sided.**  A cell recorded as a gap fails the test if
   it starts *succeeding*.  When someone implements G2 or G3, the harness names
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

A third decision was added once the first three gaps closed: **a gap is
recorded on more than one axis wherever it is claimed to be axis-independent.**
G2 is a key-exchange gap and G3 a record-layer one, so neither should depend on
the credential or the suite; `ecdsa-credential-p256-only` and
`aes128-clienthello-across-two-records` say so as ledger entries rather than as
prose.  A partial fix that closed a gap on only one axis -- P-256 that works for
RSA credentials but not EC ones, say -- would otherwise look like a complete
one.

Current ledger (all thirty-four cells agree; `cred` is the key the verified
server is started with):

```
CASE                                 cred   outcome
baseline-chacha-x25519               rsa    ok        chacha preferred when offered
openssl-defaults                     rsa    ok        stock OpenSSL offer
atlas-client-offer                   rsa    ok        what the verified client sends
aes128-only                          rsa    ok        G1: fallback arm of the policy
aes256-only                          rsa    refused   out of scope for both roles
aes-first-chacha-last                rsa    ok        server preference wins
aes256-then-aes128                   rsa    ok        G1: fallback past an unsupported suite
aes128-tcp-dribble                   rsa    ok        G1: AES-GCM through the retry loop
p256-only                            rsa    refused   G2
x25519-and-p256                      rsa    ok        X25519 selected
aes128-x25519-and-p256               rsa    ok        G1: both agile axes at once
p256-first-x25519-listed             rsa    refused   G2 (needs HelloRetryRequest)
ecdsa-credential-p256-only           ecdsa  refused   G2 is independent of the credential axis
rsa-pss-only                         rsa    ok        the RSA credential's scheme
ecdsa-only-rsa-credential            rsa    refused   G5: RSA key cannot serve an ECDSA-only offer
ecdsa-only                           ecdsa  ok        G5: ECDSA credential signs CertificateVerify
rsa-pss-only-ecdsa-credential        ecdsa  refused   G5: EC key cannot serve an RSA-only offer
both-sigalgs-ecdsa-credential        ecdsa  ok        G5: credential picks ECDSA out of both
both-sigalgs-rsa-credential          rsa    ok        G5: same offer, the other arm
ecdsa-credential-aes128              ecdsa  ok        G5+G1
ecdsa-credential-no-middlebox-compat ecdsa  ok        G5+G4
ecdsa-credential-dribble             ecdsa  ok        G5: ECDSA through the retry loop
ecdsa-credential-openssl-defaults    ecdsa  ok        G5: stock OpenSSL vs an EC server
ecdsa-credential-x25519-and-p256     ecdsa  ok        G5 with two key shares on offer
ecdsa-credential-aes-first-chacha-last ecdsa ok       G5 with the server's suite preference
ecdsa-credential-aes128-no-middlebox-dribble ecdsa ok G5+G1+G4 and the retry loop at once
no-middlebox-compat                  rsa    ok        G4: empty session id echoed verbatim
no-middlebox-compat-aes128           rsa    ok        G4+G1: empty id and the fallback arm
no-middlebox-compat-dribble          rsa    ok        G4: empty id through the retry loop
no-middlebox-compat-x25519-and-p256  rsa    ok        G4: empty id with two key shares
tcp-dribble                          rsa    ok        retained-buffer retry loop
clienthello-across-two-records       rsa    refused   G3
aes128-clienthello-across-two-records rsa   refused   G3 is independent of the suite axis
tls12-only                           rsa    refused   correctly refused: no TLS 1.3 in supported_versions
```

The last row is the one negative capability assertion that is not a gap.  The
verified server implements exactly one protocol version, and
`TLS13.Wire.Spec.clientHello_representable` requires the extension scan to have
seen a `supported_versions` entry naming TLS 1.3, so a TLS 1.2 ClientHello is
refused at the parser rather than downgraded.  The cell pins that: it fails if
the server ever starts accepting an offer that does not name TLS 1.3.  It is
also the reason the version axis exists at all -- every other cell pins the
OpenSSL client to TLS 1.3 with `min == max`, so no cell can silently start
succeeding for the wrong version.

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

1. ~~**G1 (AES-128-GCM selection).**~~  **Done.**  Closed by the deterministic
   negotiation policy described above; `aes128-only` and three new AES-128 cells
   are `ok`.
2. ~~**G4 (variable-length session-id echo).**~~  **Done.**  The ServerHello is
   now `90 + |sid|` bytes and its record `95 + |sid|`; `no-middlebox-compat` and
   three new empty-session-id cells are `ok`.
3. ~~**G5 (ECDSA credentials).**~~  **Done.**  The negotiated scheme is now
   `credential_signature_scheme` of the configured credential; `ecdsa-only` is
   `ok` and seven further credential-axis cells pin both directions.

The two that remain are **not** incremental, and this section is deliberate
about that rather than leaving them on a roadmap that implies they are next
week's work.

4. **G3 (cross-record ClientHello reassembly).**  The blocking site is
   `CS.received_cleartext_tls_message_raw`'s ClientHello arm
   (`TLS13.Spec.StateMachine.fst:2105`), which forces the message to arrive in
   exactly one `T.Handshake` record.

   The spec-level cost of weakening it was **measured**, not estimated: the arm
   was widened to a disjunction admitting a two-record split and the whole tree
   re-verified.  Only **two** proofs break, and the count matters because the
   predicate is mentioned about 120 times across 18 modules -- almost all of
   those uses are *constructions*, which a weaker predicate cannot disturb.
   The two genuine inverters are:

   * `WFL.lemma_received_client_hello_raw_length`
     (`TLS13.Spec.WireFormatLemmas.fst:243`), which concludes that a received
     ClientHello's raw delta has exactly the length of the canonical
     single-record serialization.  Under a split that is simply false -- the
     two-record encoding is five bytes longer -- so the lemma has to be
     restated.  Its eight call sites are all in
     `ProtectedWireSegmentation.fst`, and all of them are in a *paired* setting
     where the peer is the verified client; the client's `Sent` arm is
     `cleartext_tls_message_raw`, which still pins one record, so the
     single-record fact is recoverable there from the sender's side.
   * `SP.lemma_received_tls_raw_delta_legal_raw_record_parse_success`
     (`TLS13.Impl.Server.CanonicalProtocol.fst:295`), which needs the whole
     delta to parse as one record.  `raw_record_parse_success` would have to
     become "parses as one or more records".

   **That measurement is a lower bound, and taking it for the whole cost would
   be a mistake.**  Weakening a predicate can only disturb its *consumers*, and
   two consumers is genuinely all there are.  But nothing in the tree yet
   *produces* a two-record delta, so the probe never exercised the obligations
   that arise on the producing side.  Those are where the actual obstacle is,
   and it is structural:

   * `TLS13.Spec.Endpoint.Wire.wire_message` carries a proof field
     `wm_parse_ok : squash (parse_record_wire wm_raw == Some (ct, frag,
     B.length wm_raw))` -- a wire message **is** exactly one record, by
     construction.
   * A network step is `server_step st0 (SM.WireEvent wire) st1`, consuming one
     `wire_message`, and `TLS13.Impl.Server.CanonicalProtocol` discharges
     `Seq.equal (CW.wire_serialize wire) consumed` for the consumed prefix.

   One step therefore consumes exactly one record, and a ClientHello arriving in
   two records has no way to become one step.  (`CS.protected_record_count` is
   *not* the obstacle -- it is consulted only on the non-cleartext branch of
   `network_message_raw_delta_legal`, so the cleartext ClientHello path never
   reaches it.)

   The way through is the one the client already uses, and it is worth copying
   rather than inventing: `legal_protected_handshake_step` gives the client a
   **buffering step** that takes delivery of a record and sets its plaintext
   aside without interpreting it, so one record is still one step and the
   message is emitted only when the reassembly buffer holds a whole one.  It is
   explicitly gated `config_role == ClientEndpoint` and lives on the protected
   path.  G3 is that mechanism built again for the server on the *cleartext*
   path: a buffering event in the connection model, its reassembly buffer in
   `hs_buffers`, and the exhaustive matches over `conn_event` in the state
   machine and the `TLS13.System.*` pairing layer extended to carry it.

   Only then does the implementation work matter -- and it is real too:
   `TLS13.Impl.Parser.fst`'s buffer decoder decides
   `NetworkBufferNeedMoreInput` purely at record granularity (a short header, or
   a header whose fragment has not fully arrived).  A complete record whose
   fragment is an *incomplete handshake message* falls through to
   `NetworkBufferDecodeError`; it needs a third outcome so the driver leaves
   those bytes uncommitted in the retained buffer instead of erroring.

   So the original "this is a re-proof, not a patch" verdict stands, but for a
   sharper reason than the mention-count that first suggested it: not because
   the predicate is load-bearing in 18 modules, but because one-record-per-step
   is an invariant of the System layer, and relaxing it means giving the server
   the buffering event the client has.

   **The buffering-event design was then built and measured end to end.**  A
   `ConnCleartextHandshake` constructor was added to `conn_event`, with
   `hb_cleartext_handshake_bytes` in `hs_buffers`, a
   `legal_cleartext_handshake_step` gated on `ServerEndpoint` and
   `HsAwaitingClientHello`, a `step_cleartext_handshake` that touches nothing
   but the buffer, a `received_cleartext_tls_message_raw_buffered` raw-delta
   rule, and an empty-buffer bridge lemma carrying an `SMTPat` so that every
   pre-existing proof stays applicable whenever the buffer is empty.  The whole
   tree was then re-verified repeatedly to enumerate the fallout.  The result is
   worth recording, because it is not what the mention-count predicted:

   * **The exhaustiveness fallout is small and mechanical.**  Despite
     `ConnProtectedHandshake` appearing 425 times in 59 files, under twenty
     modules needed a new arm, and every one of them was `[]`, `None`, `True`,
     `False`, `record`, `pending` or a one-line `()`: `Endpoint.API`,
     `Endpoint.Client`, `Endpoint.Server`, `StateMachine.Canonical`,
     `StateMachine.Log`, `StateMachine.Correspondence`, `StateMachine.KeyMaterial`,
     `StateMachine.Replay`, `Spec.WireFormatLemmas`, `ConnectionState.Lemmas`,
     `ConnectionState.RecordKeyEpoch`, `ConnectionState.AppDataBufferEmpty`,
     `ConnectionState.ServerHelloSelectionLink`, `ProtectedWireHead`,
     `System.ServerNotCFR`, plus `Impl.Client.Types`, `Impl.Server.ChannelLog`
     and `Impl.Client.Driver.State` on the implementation side.  A cleartext
     buffering step advances no key schedule, no read sequence, no transcript
     and no log, so it is inert almost everywhere.
   * **`WFL.lemma_received_client_hello_raw_length` had to be restated, and the
     restatement is instructive.**  It cannot be stated against the canonical
     single-record serialization at all, because a reassembled handshake message
     may be longer than one record's fragment can hold.  What survives, and is
     all the replay-determinism proofs actually use, is that the buffer is a
     *function of the model*: two replays of the same delivery from the same
     model see the same buffer, hence the same remaining fragment, hence the
     same record length.  Restated that way it proves cleanly.
   * **The real casualty is the cross-endpoint pairing layer.**
     `lemma_paired_replay_split_prefixes_equal_single_client_hello` and its two
     companions match the client's *sent* records against the server's
     *received* records one for one, and a server that reassembles does not
     align that way -- the delivering record carries only the tail of the
     message.  They can only be kept by adding a
     `cleartext_handshake_buffer_empty server_model` hypothesis, i.e. by
     restricting a proved property to the case the feature does not occur.
   * **The blocker is on the implementation side, and it is not the third
     decoder outcome.**  `TLS13.Impl.Parser.DecoderWF.lemma_mk_cleartext_network_input_wf`
     must establish `CT.received_tls_raw_delta_legal st0 msg raw` from nothing
     but the record it just parsed.  Under the buffered rule that is *false*
     whenever the buffer is non-empty and the new record's fragment happens to
     parse as a whole ClientHello on its own, so the decoder can no longer
     discharge it without knowing the model's reassembly buffer.  The decoder is
     shared by both roles (`Client.fst` and `Server.Network.fst` both call
     `decode_network_buffer`), so this is not a server-local change.

   That last point is the crux: **the server needs a concrete reassembly buffer
   in its connection representation, tied by invariant to
   `pending_cleartext_handshake` of the ghost model** -- exactly the plumbing the
   client's protected buffer already has, which spans thirteen implementation
   modules including `ConnectionState.Repr`, `ConnectionState.Network`,
   `ConnectionState.Queries`, `ConnectionState.LocalHandshake`,
   `System.WireStep` and `System.AppExtrasInv`.  Until that concrete buffer
   exists, landing the spec mechanism alone would buy no capability while
   weakening three proved pairing theorems, so the spec work was deliberately
   **not** merged; it is preserved as a patch rather than carried as dead weight.

   Order of work, when it is picked up: (1) concrete pending buffer in the
   server representation plus its model-correspondence invariant; (2) the third
   decoder outcome and a buffer-aware `network_input_wf`; (3) the spec
   mechanism above; (4) the pairing-theorem hypotheses; (5) flip
   `clienthello-across-two-records`, and add a three-record cell and an
   over-cap cell to pin the boundaries.
5. **G2 (secp256r1, then HelloRetryRequest).**  The largest; its surface was
   counted rather than guessed -- `server_key_share_private` occurs 166 times in
   27 modules, `server_key_share_public` 78 times in 20, and
   `server_selected_group` 41 times in 11, because
   `server_handshake_selection` is X25519-*shaped*, not merely X25519-valued.

   The surface was then also *mapped*, and the map is much more encouraging
   than the count.  **Nothing in the crypto or key-exchange layer needs to
   change.**  `TLS13.Crypto.Spec` already exports `kex_group`, `kex_public_len`,
   `kex_public g`, `kex_public_from_private g`, `kex_shared g`, `pad_share_65` /
   `unpad_share_65` and `lemma_kex_shared_agreement`; `TLS13.KEX` already
   exports the runtime agile ECDH `kex_shared_runtime g sk pk65 out`; and
   `TLS13.Crypto.p256_public_from_private` is already a binding the *client*
   calls.  The model-level accessors are agile too:
   `TLS13.Spec.StateMachine.client_hello_kex ch g`, `server_hello_kex sh`,
   `negotiated_kex_group`, `start_kex_private/public`.  Every one of these was
   built for the client, which already offers and completes P-256, and every
   one of them is directly reusable by the server.

   What is X25519-shaped is only the *server's own* four areas, and each has a
   client-side template to copy:

   * **Key generation** -- `TLS13.Impl.Server.Setup.fst:758` calls
     `Crypto.x25519_public_from_private` into a 32-byte buffer.  The client's
     `TLS13.Impl.ConnectionState.LocalHandshake.try_start_handshake` (~:139-161)
     generates *both* pairs into a 32-byte private and a 65-byte public, and
     stores them as two parallel fields.  This is additive: keep
     `server_key_share_private/public` and add `server_p256_private/public`, so
     the ~150 existing occurrences keep their meaning.
   * **ECDH** -- `LocalHandshake.try_derive_server_shared_secret_from_private_array`
     (~:5231) calls the raw `Crypto.x25519_shared_runtime` and reads the peer
     share through the 32-byte-only `Sem.clientHello_key_share_x25519`.  The
     client's `try_derive_shared_secret` (~:4950) already calls
     `KEX.kex_shared_runtime` under a stored group tag; the server needs the
     same shape, and the group-dependent obligations then have to be re-proved
     through `Server.Keys.fst`.
   * **ServerHello writer** -- `TLS13.Impl.Server.Send.fst:202` hard-codes
     `GKE.group = GNG.X25519` and clamps the share to 32 bytes, and the
     `90`/`95`/`122` byte-length lemmas are proved against that.  Encouragingly
     the *storage* is already 65-byte padded (`:1345-1356`, with an explicit
     `IM.server_hello_kex_group` field), and the output buffer is already sized
     at run time as `90 + |session_id|`; the work is to make the base
     `90 + (share_width - 32)` and the tag a parameter.
   * **The ClientHello scan** -- `TLS13.Impl.Parser.scan_ch_key_share` (~:4287)
     writes into a 32-byte vector via `probe_copy_x25519_key`, which stops at
     the first X25519 entry and skips every other group; the server's stored
     mirror `Repr.client_hello_slot_exactly` (~:891-923) is a single 32-byte
     slot.  The client-facing `scan_sh_key_share` / `try_copy_kex_share`
     (~:3776 / ~:3632) is *already* the agile version -- it accepts X25519 at 32
     or Secp256r1 at 65 into a padded 65-byte buffer and returns the group tag.
     Rewriting the ClientHello scan against that template, and generalising
     `Wire.Spec.ch_extensions` / `kse_list_find_x25519` /
     `clientHello_representable` from "find the first X25519 share" to "find the
     first share at a group the server supports", is the deepest part.

   So the honest shape of G2 is: two additive changes with working templates,
   two invasive ones, and no new cryptography.  The single biggest obstacle is
   that the server's *spec* invariants are monomorphically typed --
   `server_key_share_private: option C.x25519_private` and
   `x25519_public_from_private` / `x25519_shared` appear inside
   `server_selection_key_share_consistent` and every downstream lemma in
   `Server.Keys`, `ConnectionState.Lemmas` and `StateMachine.Correspondence` --
   so the re-typing has to be carried through roughly a hundred proof sites.
   The additive two-field pattern is what keeps that from being a rewrite.

   HelloRetryRequest -- needed for `p256-first-x25519-listed`, and a whole
   extra flight in the server state machine -- is a separate and later step
   again.

   The map has since been turned into a staged, file-and-line-level
   implementation plan in **`docs/server-p256-plan.md`**: six stages, of which
   the first five are capability-neutral by construction (the configured
   `server_supported_groups` stays `[T.X25519]` until the last one), so the work
   can be abandoned at any stage with the gate still green and no theorem
   weakened.  That file also carries the same treatment of G3.

   **Stage S1 has landed** (`c909c4b8b`).  `server_handshake_selection` now
   carries `server_p256_private` / `server_p256_public` beside the X25519 pair,
   and `server_selection_key_share_consistent` is a two-clause, group-indexed
   statement.  Three invariants -- `server_selected_client_hello_reachable_shape`
   and both `server_x25519_*_projection`s -- now carry the group-indexed reading
   rather than only the X25519 one.  The accessors `server_kex_private`,
   `server_kex_public` and `server_selected_kex_group` mirror the client's
   `start_kex_*` exactly.  No cell moved and no behaviour changed.

   S1 also produced a result that reshapes the rest of the plan.  Rewriting
   `legal_event`'s server `LocalDeriveSharedSecret` arm into group-dispatched
   form fails in 5 files for one reason: both directions of those proofs need
   *"the selected group is X25519"*, and the spec cannot supply it --
   `server_selection_acceptable` only offers `named_group_offered` over
   `cfg.server_supported_groups`, which is an arbitrary list at the spec level
   and is `[T.X25519]` only in the implementation's config.  The invariant that
   would supply it is the `server_x25519_*_projection` family, whose
   generalisation drags in every consumer of the ServerHello's 32-byte share.
   So the derive arm cannot be generalised before the ServerHello writer is;
   stages S4 and S5 must land as one commit.  Stages S2 (parser gate) and S3
   (server P-256 keygen) remain independent of that and can go first.

   **Stage S2 has landed** (`76c48ed62`), but rescoped.  The plan had S2 widen
   the spec-level acceptance gate so that a P-256-only ClientHello *parses*.
   Measurement said no: `ch_extensions` has 169 occurrences (62 in
   `TLS13.Impl.Parser.fst`, 51 in `TLS13.Wire.Spec.Reveal.Handshake.fst(i)`),
   and changing its arity buys no capability while the request is refused one
   layer up at `server_selection_acceptable`.  The gate therefore moved
   wholesale into the final stage, where a matrix-cell flip pays for it.  What
   landed instead is storage plumbing: `TLS13.Impl.Messages.client_hello` gains
   a 65-byte `client_hello_p256_key_share` and a `client_hello_has_p256_key_share`
   flag; `is_valid_client_hello` and `client_hello_slot_exactly` gain the
   matching ownership and shape; and the allocator, parser, serializer and free
   paths were extended.  The slot is *additive* rather than a widening of
   `client_hello_key_share` (72 occurrences in 25 files, but only three real
   construction sites), so every existing occurrence keeps its meaning.

   S2 produced two findings worth recording.  First, the `has_p256` flag
   **cannot be constrained by `client_hello_slot_exactly`**: that invariant
   describes a struct allocated once whose scalar fields are never rewritten,
   which is exactly why the session-id width already lives in a separate
   metadata `Box`.  So the slot invariant carries ownership and shape only, and
   the flag must become a `Box` before anything actually fills the slot.
   Second, growing a slprop this widely used enlarges the SMT context of every
   proof that mentions it, and two distant, unrelated queries broke --
   `Client.ChannelImplementation.lemma_network_response_app_out_length` and the
   `LocalSendServerHello` arm of `Impl.Server.process_local_event`.  Both were
   repaired by *naming the projection* (a new lemma in one case, two explicit
   `assert (pure ...)` steps discharging a guarded hypothesis in the other), not
   by raising an rlimit or changing a `z3seed`.

Until they are done, `clienthello-across-two-records`,
`aes128-clienthello-across-two-records`, `p256-only`,
`ecdsa-credential-p256-only` and `p256-first-x25519-listed` stay recorded as
`refused`, and the harness will fail if any of them starts succeeding by
accident.  The two duplicated rows are deliberate: they are what makes a
*partial* fix -- one that closes a gap on one axis but not the other --
distinguishable from a complete one.
