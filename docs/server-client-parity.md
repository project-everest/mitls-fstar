# Server / client parity: gap analysis and interop test plan

Status date: 2026-08-13.  Branch `interop`.

**Progress:** G1 (server-side `TLS_AES_128_GCM_SHA256` selection), **G2
(`secp256r1` key exchange)**, **G3 (cross-record cleartext handshake
reassembly, both roles)**, G4 (variable-length `legacy_session_id` echo) and
G5 (ECDSA server credentials) are **all closed**; see the sections below.  G2
was closed on 2026-08-18 by `c6fdefad6`, the last of the staged commits laid
out in `docs/server-p256-plan.md`; G3 was closed by the `B9`..`B15` series in
the same plan -- the server half on 2026-08-22 (`9ef353062`) and the client
half immediately after (`6299e0957` and the ledger flip that follows it).
HelloRetryRequest remains out of scope and is tracked separately.

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
| `secp256r1` key exchange | yes | yes (G2 closed) | -- |
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

> **Status: CLOSED (2026-08-18, `c6fdefad6`).**  The secp256r1 half of this gap
> is gone.  The gap analysis below is the original one and is kept because it
> names, at file and line, every place that had to move; the staged plan that
> moved them is `docs/server-p256-plan.md`.
>
> What the server does now: `ch_key_share_pick` accepts a ClientHello whose only
> key_share is a well-formed 65-byte uncompressed secp256r1 point, the ECDH runs
> at whichever group that gate picked, the ServerHello carries the matching
> group tag and a 65-byte share, and the default `server_supported_groups` is
> `[X25519; Secp256r1]`.  X25519 still wins whenever both shares are well
> formed, so no pre-existing peer changes behaviour.  Three ledger cells flipped
> to `OK`: `p256-only`, `p256-first-x25519-listed` and
> `ecdsa-credential-p256-only`.
>
> `p256-first-x25519-listed` flipped **without** HelloRetryRequest, contrary to
> the prediction below.  Given `P-256:X25519`, OpenSSL sends its key_share for
> P-256 only and merely *lists* X25519 in `supported_groups`; the gate follows
> the share that was actually sent, so no retry is needed.  HelloRetryRequest is
> still unimplemented, and is only reachable if a peer offers *no* group the
> server supports — which the ledger does not currently exercise.

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

### G3. Neither role could reassemble a handshake message split across records -- **CLOSED**

*Closed by the `B9`..`B15` series (`b2f000afe` .. the client ledger flip).  The
analysis that follows is kept because it is the reasoning the design came out
of, and because the two false starts it records are the interesting part; the
"how it was actually closed" summary is at the end of the section.*

Commit `baaa66317` gave the client a third kind of protected-handshake step: a
BUFFERING step that takes delivery of a record, appends its plaintext to a
pending reassembly buffer, advances the record read sequence, and delivers no
message.  It is what made Meta's three-record server flight work.

That mechanism was **client-only by construction**:

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

Two distinct things must not be confused here, and the test suite separates
them explicitly:

* **TCP short reads** -- one TLS record arriving in several `read()` calls -- are
  handled.  `decode_network_buffer` returns `NetworkBufferNeedMoreInput` and the
  driver retries against a retained buffer with `consumed_len == 0`
  (`TLS13.Impl.Server.Driver.BufferedNetwork.fst:457`).  This is the
  `tcp-dribble` cell, and it always passed.
* **Record fragmentation** -- one handshake message arriving as two TLS records
  -- was not handled.  This is the `clienthello-across-two-records` cell, and it
  used to fail.

This gap was **not server-only**, which the ledger said out loud before it was
closed.  The verified *client* refused a ServerHello torn across two records
for the same reason, and `test/unit/test_client_record_split.c` measured it as
`serverhello-across-two-records` (see P2b below).  The client's
`protected_handshake_buffering` did not help: it is confined to the protected
path and to stages at or after ServerHello, and a ServerHello is cleartext.

Interop consequence: any peer whose ClientHello did not fit one record, or
whose stack fragmented it, could not connect.  This was a live concern as client
hellos grow (post-quantum key shares push a ClientHello past 1500 bytes and
some stacks split them).

A related limitation applies to the **cleartext path only**, and the scope is
narrower than this paragraph used to claim.  `parse_tls_message`
(`TLS13.Wire.Spec.fst:921`, handshake arm at `:927`) requires
`consumed == B.length fragment`, so several handshake messages coalesced into
one *cleartext* record are rejected rather than drained.  The **protected** path
does drain them: `protected_handshake_step` carries an `offset` and a `consumed`
count, and a non-`head` step continues inside the buffer its head published
without advancing `record_read`, which is what
`try_process_protected_handshake_drain` walks.  That is how Meta's flight is
handled in the `test/interop` sweep, where `Certificate` begins at offset 6 of
the first record and runs past its end -- several messages in one record *and*
one message across records, at the same time.

The cleartext restriction is close to vacuous in TLS 1.3 anyway: a ClientHello
is the client's entire cleartext flight and a ServerHello the server's, and the
CCS that may follow a ServerHello under middlebox compatibility carries a
different content type, so it is necessarily a separate record.

Two designs for closing this have now been built against the whole tree and
measured.  The blocker is **not** where the first analysis put it.

* The first analysis named
  `TLS13.Impl.Parser.DecoderWF.lemma_mk_cleartext_network_input_wf:245` -- a
  buffer-aware `network_input_wf` -- as the blocker.  That is wrong.
  `process_client_hello` (`TLS13.Impl.Server.Network.fsti:33`) takes `raw` and
  `fragment` as two *separate* arrays and constrains them independently
  (`event_raw_delta_legal` on the former, `Seq.equal fragment (serialize_handshake ...)`
  on the latter).  Nothing requires `fragment` to be the fragment of a single
  record of `raw`, so the server's ClientHello processing layer is already
  record-count-agnostic and `network_input_wf` need never be weakened.
* Widening the ClientHello arm of `received_cleartext_tls_message_raw`
  *disjunctively* (old disjunct kept verbatim, so only inversion sites can
  break) was re-implemented and put through a full verify: **two** errors across
  89 rebuilt modules, confirming the earlier count.  This probe's formulation
  broke `WFL.lemma_client_hello_sent_received_eq`
  (`TLS13.Spec.WireFormatLemmas.fst:128`) rather than
  `WFL.lemma_received_client_hello_raw_length` (`:243`); both live in that
  module and both are inverters, so which one surfaces first depends on the
  exact shape of the added disjunct.  Either is benign -- each has the
  *sender's* single-record form in scope and so can refute the split case.  The
  other error, `TLS13.Impl.Server.CanonicalProtocol.fst:324`, is the real wall,
  and `make -k` skipping its dependents makes "two" a lower bound.
* **The real wall is that one protocol step consumes exactly one TLS record.**
  `TLS13.Spec.Endpoint.Wire.wire_message` carries a `wm_parse_ok` squash pinning
  `parse_record_wire wm_raw == Some (ct, frag, B.length wm_raw)`, and the server
  driver's correctness statement is phrased against that class throughout
  `TLS13.Impl.Server.CanonicalProtocol` -- which is on the driver's critical
  path, aliased by `Server.Driver` and all six `Server.Driver.Buffered*`
  modules, not a standalone meta-theorem.

Consequently the *archived* design -- a `ConnCleartextHandshake` buffering event,
where each buffering step still consumes exactly one record -- is the
architecturally conservative route, because it leaves `wire_message`, the
canonical protocol refinement and the cross-endpoint pairing theorems untouched.
Both routes, their costs and the recommendation are written up in
`docs/server-p256-plan.md`, section "G3 line-level plan".

#### How it was actually closed

The archived route is the one that landed, and it landed for both roles.  The
shape is the same on each side, and it is worth stating compactly because the
analysis above is long:

* **One new event.**  `CS.ConnCleartextHandshake` carries a
  `cleartext_handshake_step` -- a fragment and the resulting stream -- and
  `CS.legal_cleartext_handshake_step` gates it on a non-empty fragment, on the
  role's pre-hello control stage, on `stream <= max_pending_cleartext_handshake`
  (32768), and on `parse_tls_message Handshake stream == None`.  That last
  conjunct makes buffering a **last resort**: a record whose fragment already
  parses as a whole message can never be buffered instead of delivered, so the
  existing single-record path keeps its meaning exactly.
* **One new raw-delta rule.**  `CS.received_cleartext_tls_message_raw_buffered`
  reads the pending buffer out of the model: with an empty buffer it is
  byte-equality against the canonical single-record serialization (the old
  rule), and with a non-empty one it is a parse of `pending ++ fragment`.  It is
  an `if`, not a disjunction, because the replay-determinism proofs in
  `ProtectedWireSegmentation` need the rule to be a *function* of the raw bytes.
  `CS.lemma_received_cleartext_tls_message_raw_buffered_of_empty` carries an
  `SMTPat`, so every pre-existing proof stays applicable whenever the buffer is
  empty.  That is what keeps the cost of the change bounded -- but it is *not*
  free: `TLS13.System.fst` still grew by 206 lines, because something has to
  say the buffer *is* empty at the points the paired-system theorems are
  stated.  `tls_system_inv` gains four conjuncts --
  `CS.cleartext_handshake_buffer_empty` for each endpoint's model, plus
  `no_cleartext_buffering_steps` on each endpoint's event log -- preserved by
  `lemma_client_no_cleartext_buffering_pres` and
  `lemma_server_no_cleartext_buffering_pres`.  Ten pre-existing lemmas in
  `ProtectedWireSegmentation` pick up a matching empty-buffer hypothesis.  This
  follows an existing precedent in identical shape rather than setting one:
  `protected_witnesses_ok` was *already* conditioned on
  `CCShape.no_buffering_steps` before this branch, and the two new cleartext
  hypotheses sit literally beside that pre-existing protected one in both
  flagship inversion lemmas' `requires`.  The honest reading is that the
  paired-system theorems now hold for *non-reassembling* runs; extending them
  to cover reassembly is future work, and is called out as such below.
* **A concrete buffer beside the ghost one.**  The prediction above that "the
  server needs a concrete reassembly buffer in its connection representation,
  tied by invariant to `pending_cleartext_handshake` of the ghost model" was
  correct, and that plumbing (`ConnectionState.Repr` / `.Network` / `.Queries`,
  and the role-agnostic `CQ.can_buffer_cleartext_handshake` /
  `CQ.copy_pending_cleartext_handshake`) is the bulk of the work.
* **Two implementation entry points per role**, chained in that order ahead of
  the ordinary decode-error path: a delivery that fires only when the pending
  buffer is NON-empty (`try_deliver_reassembled_client_hello` in
  `TLS13.Impl.Server.Network.fst`, `try_deliver_reassembled_server_hello` in
  `TLS13.Impl.Client.fst`), and a buffering step behind it
  (`try_buffer_cleartext_handshake_record`, one per role).

The one place the two roles genuinely differ is where the reassembled delivery
lands in the correctness statement.  The server's
`server_network_bytes_end_to_end_correct` has few enough conjuncts to admit it
directly.  The client's `network_bytes_end_to_end_correct` does not: it projects
a DECODED MESSAGE out of every consumed record, and a message spread over
several records has no such projection.  So on the client the reassembled
delivery lands in the **weak** disjunct, `CT.coalesced_head_step_correct`, which
was widened to admit a received cleartext `ConnNetworkEvent` carrying
`raw_record_parse_success` explicitly.  That is sound for the same reason the
server's version is: a reassembled delivery supplies `legal_response_for_event`,
the record shape, a vacuous decode projection (its guard is
`network_message_is_cleartext ... == false`) and a zero-output response.

Also worth recording, because the earlier analysis got it wrong: the
implementation-side blocker named above --
`DecoderWF.lemma_mk_cleartext_network_input_wf` having to establish the raw
rule from nothing but the record it just parsed -- was real, and the fix is that
the projection is a **disjunction** of the record-local rule and the buffered
one rather than a replacement.  The shared decoder proves the record-local
disjunct, which is all it can know; the empty-buffer `SMTPat` collapses the two
everywhere the buffer is empty.  A straight replacement broke
`Client.CanonicalProtocol.lemma_client_network_input_projection_refines_core`,
and that failure is what pointed at the disjunction.

Finally, the concern about threat models stands and is discharged by the cap.
A server buffering a ClientHello accumulates bytes from an **unauthenticated**
peer before any key exists, so `max_pending_cleartext_handshake` is load-bearing
for resource safety and not merely for the record-counting argument that
motivates the client's `max_pending_protected_handshake`.

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
   it starts *succeeding*.  When G2 and G3 were implemented, the harness named
   the row to flip, so the capability change was recorded in the same commit as
   the implementation.  A "known failures are skipped" harness would let a gap
   close silently and then reopen silently.
2. **Successful cells assert the negotiated parameters**, not just success:
   `SSL_get_cipher_name` and `OBJ_nid2sn (SSL_get_negotiated_group ...)` are
   checked against the suite and group the case is about.  Without that, the
   `x25519-and-p256` cell would still pass if the server had picked P-256, and
   `aes-first-chacha-last` would still pass if it had picked AES -- which are
   exactly the outcomes the cells exist to distinguish.
3. **What the key-share axis covers was measured, not assumed.**  The cells
   whose group list is `X25519:P-256` configure the client's *supported_groups*;
   they do **not** make it send two `KeyShareEntry` values.  OpenSSL 3.0 emits
   exactly one key share, for the first group in the list -- `X25519:P-256`
   produces a single 32-byte `0x001d` entry and `P-256:X25519` a single 65-byte
   `0x0017` entry.  (The `*` prefix that would ask for two is an OpenSSL 3.2
   feature.)  So those cells exercise *"one share offered, a second group merely
   listed"*, which is precisely the shape that makes `p256-first-x25519-listed`
   require a HelloRetryRequest, and they are labelled that way.

   The genuinely multi-`KeyShareEntry` ClientHello is covered by
   `test_atlas_loopback`: the verified **client's** canonical ClientHello
   carries two entries, `[kse; pkse]` at
   `TLS13.Impl.ConnectionState.Model.client_hello_of_start`.  That is the path
   the server's group-tagged acceptance scan (stage S6.7c) and its 65-byte
   secp256r1 mirror slot (stage S2) actually sit on, so the matrix and the
   loopback are complementary and neither subsumes the other.

The framing axis is served by an in-process TCP proxy that re-frames the
client->server stream at the record layer.  It re-frames only *cleartext*
handshake records: a protected record is a single AEAD-sealed unit, so
splitting its ciphertext would test nothing but the tag.  The `tcp-dribble` cell
runs through the same proxy code and passes, which is what made the
`clienthello-across-two-records` failure attributable to record fragmentation
rather than to the proxy -- and, now that the cell is `ok`, is what makes its
success attributable to reassembly rather than to a proxy that quietly stopped
splitting.

A third decision was added once the first three gaps closed: **a gap is
recorded on more than one axis wherever it is claimed to be axis-independent.**
G2 is a key-exchange gap and G3 a record-layer one, so neither should depend on
the credential or the suite; `ecdsa-credential-p256-only` and
`aes128-clienthello-across-two-records` say so as ledger entries rather than as
prose.  A partial fix that closed a gap on only one axis -- P-256 that works for
RSA credentials but not EC ones, say -- would otherwise look like a complete
one.  The same decision is why `clienthello-across-three-records` exists beside
the two-record cell: two records only ever buffer onto an EMPTY pending buffer
and then deliver, whereas three make the middle record coalesce onto an ALREADY
NON-EMPTY one, which is a distinct branch of the buffering step.

**Two and three records are coverage choices, not a limit.**  Three records
*saturate* the branch structure -- first record onto an empty buffer, middle
onto a non-empty one, last coalesces and parses -- so a fourth takes the
identical path to the third and a hundredth adds no new arm.  The capability
itself is inductive: `cleartext_handshake_stream` is just `pending ++ fragment`
and **no record counter appears anywhere in the step relation**, so the only
limits are the byte caps (§ "Resource safety" below) and the requirement that
each fragment be non-empty.  Because that is an easy thing to assert and a
harder thing to believe, both matrices carry an N-way cell as well --
`clienthello-across-many-records` and `serverhello-across-many-records` -- in
which the proxy emits 8-byte records and lets N follow from the message size.
The proxy prints the N it produced rather than the test hard-coding one; today
that is 24 records for OpenSSL's 190-byte ClientHello and 16 for its 122-byte
ServerHello.

Current ledger (all thirty-six cells agree; `cred` is the key the verified
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
p256-only                            rsa    ok        G2: secp256r1-only offer
x25519-and-p256                      rsa    ok        X25519 selected
aes128-x25519-and-p256               rsa    ok        G1: both agile axes at once
p256-first-x25519-listed             rsa    ok        G2: only a P-256 share is sent
ecdsa-credential-p256-only           ecdsa  ok        G2 is independent of the credential axis
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
ecdsa-credential-x25519-and-p256     ecdsa  ok        G5 with a two-group supported_groups
ecdsa-credential-aes-first-chacha-last ecdsa ok       G5 with the server's suite preference
ecdsa-credential-aes128-no-middlebox-dribble ecdsa ok G5+G1+G4 and the retry loop at once
no-middlebox-compat                  rsa    ok        G4: empty session id echoed verbatim
no-middlebox-compat-aes128           rsa    ok        G4+G1: empty id and the fallback arm
no-middlebox-compat-dribble          rsa    ok        G4: empty id through the retry loop
no-middlebox-compat-x25519-and-p256  rsa    ok        G4: empty id, two-group groups list
tcp-dribble                          rsa    ok        retained-buffer retry loop
clienthello-across-two-records       rsa    ok        G3: reassembled out of the cleartext buffer
aes128-clienthello-across-two-records rsa   ok        G3 is independent of the suite axis
clienthello-across-three-records     rsa    ok        G3: the middle record coalesces onto a non-empty buffer
clienthello-across-many-records      rsa    ok        G3: 8-byte records -- the reassembly is inductive, not special-cased for small N
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

### P2b. The client-side mirror of the framing axis -- `test-client-record-split`

The server matrix above re-frames the *client -> server* direction only.  That
left the symmetric question unmeasured: what does the **verified client** do
when the **server's** cleartext ServerHello arrives as two records?  The
prose answer -- "there is no cleartext reassembly in the tree for either role"
-- was asserted in this document and in the header of
`test/unit/test_server_interop_matrix.c`, but nothing executed it, so nothing
would notice when it stopped being true.

`test/unit/test_client_record_split.c` executes it.  It runs the extracted,
verified client against the local OpenSSL echo server through an in-process
proxy that re-frames the **server -> client** stream, and records five cells:

```
CASE                               EXPECT   NOTE
passthrough                        ok       control: the proxy is transparent
serverhello-tcp-dribble            ok       control: TCP segmentation, not record segmentation
serverhello-across-two-records     ok       G3, client side: the mirror of clienthello-across-two-records
serverhello-across-three-records   ok       G3: the middle record coalesces onto a non-empty buffer
serverhello-across-many-records    ok       G3: 8-byte records -- the reassembly is inductive, not special-cased for small N
```

The split cells were recorded as `refused` when the harness was written, and
that refusal was a *protocol* refusal which the harness proved rather than
asserted: cells connect with `tls13_client_driver_connect_reporting`, and the
split cell reported `connect: verified protocol step failed` -- the verified
state machine rejecting a truncated ServerHello.  A TCP error or a timeout
would have read differently.  The row then failed loudly the moment the
capability landed, which is exactly what it was for.

The two controls are load-bearing.  A single cell proves little on its own,
because a harness broken for any reason at all would report "refused" and, while
the row expected refused, would have looked green.  `passthrough` shows the
proxy relays faithfully, so the split cells' verdicts are attributable to the
re-framing; `serverhello-tcp-dribble` separates TCP-level segmentation -- which
the client's retained receive buffer and `NeedMoreInput` retry loop already
absorb -- from record-level segmentation, which is the capability.  If a control
cell goes red, the split cells' verdicts must not be read at all until it is
green again.

The client's `protected_handshake_buffering` does not cover these cells, and the
distinction is easy to get wrong.  That buffering is confined to the protected
path and to stages at or after ServerHello
(`protected_handshake_buffering_stage` = `HsServerHelloReceived`,
`HsEncryptedExtensionsReceived`, `HsCertificateValidated`,
`HsCertificateVerifyVerified`).  A ServerHello is cleartext and precedes all of
them; what these cells exercise is the *cleartext* buffering G3 added.
Cross-record buffering on the protected path *is* exercised -- by the
real-world sweep in `test/interop`, where Meta serves its flight in three
protected records with `Certificate` starting at offset 6 of the first and
running past its end -- but by the sweep, not by this file.

So G3 was a **both-roles** gap, and both halves are now closed.  The
record-local ServerHello delivery in `TLS13.Impl.Handle.Handshake` still gates
on `can_receive && buffer_empty`, so it declines to fire while a partial message
is pending; `CN.mark_received_server_hello` itself imposes no such gate, which
is what lets the reassembled path take the buffered reading of
`received_cleartext_tls_message_raw_buffered` without disturbing the unbuffered
one.

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

The two that remained were **not** incremental, and this section is deliberate
about that rather than leaving them on a roadmap that implied they were next
week's work.  Both have since landed.

4. ~~**G3 (cross-record cleartext reassembly, both roles).**~~  **Done.**  The
   entry below is the pre-implementation scoping, kept verbatim because its two
   wrong turns are instructive and because comparing the estimate against what
   landed is useful.  What actually landed, and where the estimate was right and
   wrong, is summarised under "How it was actually closed" in the G3 section
   above.

   **First, a correction to the intuition that this is a port of client work.**
   It is natural to say "the client already does cross-record reassembly, so
   copy it", and the rest of this entry used to open that way.  Measured against
   the source, that is false in the way that matters.  The client's mechanism
   lives on the **protected** path and is gated to
   `protected_handshake_buffering_stage` = {`HsServerHelloReceived`,
   `HsEncryptedExtensionsReceived`, `HsCertificateValidated`,
   `HsCertificateVerifyVerified`} -- every one of them *after* ServerHello.  A
   ServerHello itself split across two records would fail on the **client**
   exactly as a ClientHello does on the server.  Grepping the tree for cleartext
   buffering of any kind returns **zero** hits.  So nobody has done cleartext
   reassembly in this codebase, for either role; G3 is not behind the client, it
   is a problem the client also has and has never had to face, because in
   practice no server splits a ServerHello.

   The structural reason the two paths are not interchangeable is the shape of
   the event, and it is visible in three lines of
   `TLS13.Spec.StateMachine.fst:516-519`:

   ```
   type conn_event =
     (* a PARSED message -- no bytes, no offset, no consumed count *)
     | ConnNetworkEvent of directed_message M.tls_message
     (* bytes + offset + consumed + head + buffering *)
     | ConnProtectedHandshake of protected_handshake_step
     | ConnLocalEvent of local_event
   ```

   `protected_handshake_step` is a record of
   `{message; fragment: B.bytes; offset: nat; consumed: nat; head: bool;
   buffering: bool}`.  It was *born* describing "a record's plaintext, of which
   a sub-slice is the message" -- the one-record-one-message equation was
   already broken there by construction, and the segmentation lemmas were
   written to track a running buffer.  Adding client reassembly was therefore
   adding **one `bool` field** to a type that already had the byte-level
   vocabulary to say what a partial delivery is.

   `ConnNetworkEvent` carries a **fully parsed `tls_message`** and nothing else.
   There is no fragment, no offset, no consumed count -- the cleartext event has
   no vocabulary for "bytes that are not yet a message", and
   `WS.parse_tls_message` closes the loop by requiring `consumed == B.length
   fragment` on the Handshake arm: a cleartext record **is** exactly one whole
   message.  To buffer on this path you must first introduce bytes into the
   cleartext event.  That is a new constructor, because changing
   `ConnNetworkEvent`'s payload would touch its 1927 occurrences across 104
   modules.

   And a new constructor is precisely what the server's own proofs are stated
   against the *absence* of: `ServerCanonicalShape.fst:280` reads
   `| CS.ConnProtectedHandshake _ -> False`, i.e. the server's canonical-shape
   theorem asserts the server never takes a buffering step at all.  The client's
   step is additionally gated `config_role == ClientEndpoint`
   (`legal_protected_handshake_step`), so it cannot simply be un-gated and
   reused -- the server would then be able to take protected-handshake steps,
   which is a different and much larger change than cleartext reassembly.

   Finally the threat models differ, which is why the cap is not a detail.  The
   client buffers only *after* handshake keys are installed, so every byte it
   accumulates has already been AEAD-authenticated: only the genuine peer can
   grow that buffer.  A server buffering a ClientHello is accumulating bytes
   from an **unauthenticated** attacker before any key exists, so
   `max_pending_cleartext_handshake` is load-bearing for resource safety, not
   merely for the liveness/record-counting argument that motivates the client's
   `max_pending_protected_handshake`.

   With that said, here is the measured cost.  The blocking site is
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

   The way through is the client's *idea*, though -- as established above --
   not its code: `legal_protected_handshake_step` gives the client a **buffering
   step** that takes delivery of a record and sets its plaintext aside without
   interpreting it, so one record is still one step and the message is emitted
   only when the reassembly buffer holds a whole one.  That shape is the right
   one.  What cannot be reused is the step itself: it is gated
   `config_role == ClientEndpoint`, it lives on the protected path, and it rides
   on an event that already carries bytes.  G3 is that mechanism **re-built**
   for the server on the *cleartext* path: a buffering event in the connection
   model, its reassembly buffer in `hs_buffers`, and the exhaustive matches over
   `conn_event` in the state machine and the `TLS13.System.*` pairing layer
   extended to carry it.

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
   is an invariant of the System layer on the cleartext path, and relaxing it
   means giving the server a cleartext analogue of the buffering event the
   client has on the protected path.

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

   *That order was followed, with one correction: step (2) turned out not to be
   needed as stated.  No third decoder outcome was added -- an incomplete
   handshake message keeps falling through the existing "did not parse" arm,
   and the decoder's postcondition was merely STRENGTHENED with a clause pinning
   the outer content type.  Nor was a buffer-aware `network_input_wf` needed:
   the decoder proves the record-local disjunct of a widened projection and the
   empty-buffer `SMTPat` does the rest, so the shared decoder's statement of
   `network_input_wf` was left alone.  An over-cap cell was not added; the cap is
   exercised at the spec level by `legal_cleartext_handshake_step` and at the
   implementation level by the `Bounds.max_client_hello_len_sz` /
   `max_handshake_flight_len` guards on the coalescing path.*

   **The spec attempt itself is preserved on the branch
   `g3-route-b-spec-attempt`** (24 files, +529/-20), whose commit message
   carries the full fallout enumeration above.  It was archived rather than
   merged because, as measured, landing it alone would have bought no capability
   while weakening three proved pairing theorems -- step (1) had to come first.
   It has since been **superseded** by the `B9`..`B15` series, which does step
   (1) first and then re-lands the spec mechanism on top of it; the branch is
   only of historical interest now.  It was checked to still apply cleanly to
   `interop` as of `e0727d23c`; recover the diff with

   ```
   git diff interop...g3-route-b-spec-attempt
   ```
5. **G2 (secp256r1, then HelloRetryRequest).**  *Done as of `c6fdefad6`; the
   secp256r1 half is closed and HelloRetryRequest was not needed for any ledger
   cell.  The scoping below is kept because it is the estimate the staged plan
   in `docs/server-p256-plan.md` was built from, and comparing the two is
   useful when scoping G3.*  The largest; its surface was
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

   **Stage S3 has landed** (`b97d28f3b`), and one finding collapsed it.
   `C.x25519_private` and `C.p256_private` are *both* `B.bytes_of_len 32`, and a
   server transmits exactly one key share and runs exactly one ECDH -- the one
   named by `server_selected_group`.  So a single 32-byte secret derives both
   publics, with no cross-group exposure and no way for the peer to observe the
   unused one.  There is therefore no second random, no extra array parameter
   and no change to the driver's payload width: the selection literals simply
   gained `server_p256_private = Some <the same bytes>` and
   `server_p256_public = p256_public_from_private <the same bytes>`.  S3
   verified with **zero** proof repair.

   **Stages S4 and S5 have landed as one commit** (`c02ab1b13`), rescoped.  The
   plan had them make the *implementation* agile; measurement said defer.
   Making the ServerHello writer group-parametric means making its length
   arithmetic parametric (`90 + |sid|` becomes `58 + |ks| + |sid|`), which
   touches around forty numeric sites plus the assert-dense EverParse chain in
   `Impl.Serializer.Handshake.fst:453-880` -- and buys no capability while every
   selection literal still says `T.X25519`.  What landed instead is that the
   **specification** became fully group-parametric: `server_hello_matches_-`
   `selection`, `legal_event`'s server `LocalDeriveSharedSecret` arm, both
   `server_x25519_*_projection`s and `paired_x25519_key_shares` all now read a
   group and use the S1 accessors.

   The crux was where the group comes from, and the answer is the one the client
   already uses: where a ServerHello exists, recover it from the *message*
   (`server_hello_kex sh`); before one exists, from the selection
   (`server_selected_kex_group selection`).  Inside the implementation the
   answer is *nowhere* -- `connection_state` stores thirty-two private bytes and
   a presence flag, never a group tag -- so the restriction cannot be recovered
   from the representation and has to be asserted by it.  That is
   `CR.server_selection_group_pinned`, one named predicate carried as a `pure`
   conjunct of `server_selection_presence_exactly`; deleting it is the S6
   off-switch.

   S4/S5 also confirmed R7 at spec scale.  Generalising the projections forced
   the same generalisation through every consumer that *concluded* X25519-shaped
   facts from them -- `paired_x25519_key_shares`, the three `*_corresponds`
   predicates, the `HandshakeAgreementNonReady` helpers, both
   `Impl.Driver.Pairing` producers and `ConnectionState.Lemmas`' shared-secret
   agreement -- and there was no cheaper cut.  Two Pulse/F* gotchas cost real
   time: a Pulse `match` on an enum does **not** refine the scrutinee in a `_`
   catch-all (use a boolean `if`), and an `.fsti` `val`'s `requires` must imply
   the `.fst` `let`'s, or the error surfaces confusingly at the *body*.  No cell
   moved.

   **Stages S6.1 through S6.8c-2 have landed** (`5ee056664`, `b578465f0`,
   `0bd78b985`, `613e12980`, `c360e2165`, `cab78ad8d`, `2537d001c`,
   `e4594e008`, `1cac89cab`, `c40d2e1cc`, `b80502853`, `b7c8aa36b`,
   `bf2581056`), all capability-neutral,
   all with the ledger unmoved.  Between them they have taken every part of the
   feature *except the behaviour* off the final commit's critical path: the
   parser reads a secp256r1 share, the ClientHello mirror stores it, the
   negotiated group is observable at run time, the ECDH itself dispatches on it,
   the ServerHello's specification, size arithmetic, Pulse write chain and
   abstract witness are all group-parametric, the ECDH's *postcondition* speaks
   of `kex_shared g`, the acceptance scan's key-share accumulator is
   group-tagged, and the two runtime facilities the flip needs -- a group-agile
   derivation of the server's own share, and a query for the negotiated group --
   both exist and are verified.

   Two measurements from that work are worth carrying forward.  First, the
   "169 `ch_extensions` occurrences" that twice caused the acceptance gate to be
   deferred were almost entirely *type* churn: the scan's key-share accumulator
   was typed "thirty-two bytes".  Retyping it as an explicit `(group, share)`
   pair -- following the codebase's own law that a group is a tag and never a
   length -- reduced the gate to one replaceable expression.  Second, the ECDH's
   X25519 *precondition* cannot be pre-staged: replacing it with the honest
   policy-agreement clause verifies through all five layers above it but cannot
   be discharged by a selection *builder* that still names `T.X25519` literally.
   The resolution is not a new ghost query but the flip itself -- a builder that
   takes the group *from* the policy proves the agreement by definition.

   Two further measurements from S6.8c-1 sharpen what "one commit" actually
   covers.  (a) The model's ServerHello **size arithmetic generalises for free**,
   exactly as the witness's did: `lemma_server_hello_of_selection_bytesize` now
   concludes `58 + kex_public_len g + |sid|`, `valid_selection` is untouched, and
   both of its consumers keep deriving `90 + |sid|` because `kex_public_len`
   reduces definitionally at `KexX25519`.  (b) The concrete-share widening is
   **much smaller than it looked**: the driver calls the entry point that takes
   the server's *private* key, and `kex_private` is 32 bytes for both groups, so
   `Driver.BufferedHandshake` is not on that path at all.  Only a stack-local in
   `Send.fst:1572` and `process_send_server_hello_from_arrays`' signature (plus
   its re-export in `Server.fsti/.fst`) widen to 65 bytes.  **S6.8c-2 has since
   landed exactly that** (`bf2581056`): the send path's own share buffer is now
   65 bytes wide and filled by `KEX.kex_public_from_private_runtime`, at a
   literal `KexX25519` and with the literal width `32` in every
   `unpad_share_65` — which is what kept it capability-neutral.  It also added
   `CryptoSpec.padded_share_65` (the "zero-padded 65-byte buffer" predicate the
   send path carries) and an additive postcondition on
   `kex_public_from_private_runtime` giving `pad_share_65` of the share when the
   buffer handed in is zeroed.

   So the buffer is not what makes the rest indivisible.  The wall is the ~24
   statements of `95 + |stored session id|`, which are keyed on the connection
   *state*: their group is `CM.stored_client_hello_kex_group 'st0`, provably
   `KexX25519` only from the acceptance gate's clause inside
   `IM.is_valid_client_hello` and not from the pure part of any postcondition.
   Generalising them changes what every caller must prove, so unlike the
   selection-keyed arithmetic it cannot be staged capability-neutrally.

   What is left, in one commit: widen the gate, have the seven selection
   builders take the group from the policy and the share from
   `KEX.kex_public_from_private_runtime` (the send path already calls it, at a
   literal group), replace the ServerHello's `90`/`95`
   with `58`/`63 + kex_public_len g`, drop the ECDH's X25519 precondition and
   `CR.server_selection_group_pinned`, add `T.Secp256r1` to
   `server_supported_groups`, and flip `p256-only` and
   `ecdsa-credential-p256-only`.  Every item is a deletion or a substitution of
   an expression that already exists.  `docs/server-p256-plan.md` §7 "S6.8c"
   carries it at file-and-line level.

Until they are done, `clienthello-across-two-records`,
`aes128-clienthello-across-two-records`, `p256-only`,
`ecdsa-credential-p256-only` and `p256-first-x25519-listed` stay recorded as
`refused`, and the harness will fail if any of them starts succeeding by
accident.  The two duplicated rows are deliberate: they are what makes a
*partial* fix -- one that closes a gap on one axis but not the other --
distinguishable from a complete one.
