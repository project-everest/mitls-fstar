# Fresh Needham-Schroeder-Lowe model

The active development follows the same architecture as `dh-sample`:

- `NSL.Sample.StateMachine` is the only protocol semantics. Its four labelled
  endpoint rules carry their ordered fresh, PKE, send, and completion stories.
- `NSL.Sample.Protocol` only instantiates `Common.Protocol.System`.
- Delivery, replay, injection, freshness, provenance, compromise, canonical
  histories, and history folding are entirely generic.
- `NSL.Sample.DY.*` interprets canonical histories directly and proves the DY*
  invariant and compromise-aware security consequences without a Product or
  Lifting state machine.

The intended audit path is:

1. Review the four rules in `NSL.Sample.StateMachine`; these are the complete
   protocol semantics.
2. Review `NSL.Sample.DY.Profile` for the PKE authorization policy and labels.
3. Review the fold cases in `NSL.Sample.DY.Model` that map generic effects to
   DY* entries.
4. Check the exported statements in `NSL.Sample.DY.Invariant`,
   `NSL.Sample.DY.Coherence`, and `NSL.Sample.DY.Security`. Their bodies are
   machine-checked proofs, not additional transition semantics.

`NSL.Sample.Crypto.fsti` is the explicit concrete PKE boundary. The main
reachable-security theorem requires a prefix-local simulation of each
successful decryption. `honest_full_run_secure` closes that premise for an
actual four-transition run of the authoritative state machine: both endpoints
complete, and all three ciphertext acceptances use genuine prior DY* `PkeEnc`
terms rather than the compromise alternative.

This instantiation is deliberately a closed two-party role session: the
responder accepts Message 1 only for the configured initiator, because the
generic system currently owns exactly those two PKE keys. Supporting unbounded
principal identities requires a generic identity-indexed key registry; the
model does not pretend that an external recipient is protected by the
configured initiator's key.
