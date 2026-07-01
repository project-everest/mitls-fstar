module TLS13.Wire.Spec.Reveal

(* Minimal aggregator restoring ONLY the clean (no deleted-M-record) record-framing,
   CertificateVerify signing-context, and byte-util spec helpers that the record-level
   serializers still depend on. The handshake-message correspondence (ClientHello/
   ServerHello/Certificate/Finished serialize/parse reveal) that the old Reveal layer
   carried is intentionally NOT restored -- it is replaced by the generated copyful
   serializers (TLS13.Impl.Serializer.FinishedPOC). *)

include TLS13.Wire.Spec.Reveal.Record
include TLS13.Wire.Spec.Reveal.CertificateVerify
include TLS13.Wire.Spec.Reveal.Handshake
