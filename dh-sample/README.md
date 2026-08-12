# Fresh ISO-DH model

The active development is intentionally small:

- `DH.Sample.StateMachine` contains the four authoritative, intrinsically
  labelled endpoint rules and their semantic effects.
- `DH.Sample.Protocol` is only an instantiation of `Common.Protocol.System`.
- `Common.Protocol.System` owns delivery, replay, injection, freshness,
  provenance, compromise, and canonical history construction.
- `Common.Protocol.Interpretation` lets a symbolic backend fold that history
  directly; no protocol-specific product or lifting state machine is required.
- `DH.Sample.DY.Model` is the direct canonical-history-to-DY* interpretation.
- `DH.Sample.DY.Invariant` proves every interpreted history satisfies a
  non-vacuous DY* core `trace_invariant`, including injection and compromise.
- `DH.Sample.DY.Coherence` audits the four authoritative rule witnesses once
  and proves reachable completions contain their matching acceptance.
- `DH.Sample.DY.Security` derives authentication/transcript agreement modulo
  compromise and matching-session key secrecy using the DY* attacker theorem.

Concrete signature verification is connected by the explicit
`crypto_simulation` premise: `DH.Sample.Crypto.fsti` deliberately does not claim
EUF-CMA. The premise is checked at each acceptance against the symbolic model of
the preceding canonical-history prefix. An explicit honest-run witness proves
that the genuine-signature, non-compromise branch is inhabited. The end-to-end
theorem is `reachable_security`; its conclusions are `security_consequences`.
Session snapshots retain ephemeral and key material, so the model intentionally
claims no forward secrecy after compromise.
