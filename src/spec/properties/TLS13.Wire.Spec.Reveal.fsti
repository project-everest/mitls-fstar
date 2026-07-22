module TLS13.Wire.Spec.Reveal

(* Minimal aggregator restoring ONLY the clean (no deleted-M-record) record-framing,
   CertificateVerify signing-context, Finished-reveal, Alert, and byte-util spec helpers
   that the record-level serializers still depend on, PLUS the read/build-direction
   handshake reveal layer (TLS13.Wire.Spec.Reveal.Handshake) that the byte-level
   parser (TLS13.Impl.Parser) and handshake serializer import as [RV.*].  The
   handshake correspondence is now expressed over the generated QuackyDucky codec
   (via [WS.synth_handshake_msg_of] / [WS.serialize_handshake]), NOT the old
   [handshake_synth] hand-codec; the guarded [synth_handshake_msg_of] reveals gate
   parse acceptance on the per-message [representable] predicates. *)

include TLS13.Wire.Spec.Reveal.Record
include TLS13.Wire.Spec.Reveal.CertificateVerify
include TLS13.Wire.Spec.Reveal.Finished
include TLS13.Wire.Spec.Reveal.Alert
include TLS13.Wire.Spec.Reveal.Handshake
