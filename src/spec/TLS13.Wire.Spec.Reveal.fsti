module TLS13.Wire.Spec.Reveal

(* Minimal aggregator restoring ONLY the clean (no deleted-M-record) record-framing,
   CertificateVerify signing-context, Finished-reveal, Alert, and byte-util spec helpers
   that the record-level serializers still depend on.  The handshake-message
   correspondence (ClientHello/ServerHello/Certificate serialize/parse reveal and the
   old [handshake_synth] hand-codec) that the pre-migration Reveal layer carried is
   intentionally NOT restored -- it is replaced by the generated copyful serializers
   (TLS13.Wire.Spec now exposes the QuackyDucky codec directly).  The valid record-level
   and Finished/Alert reveal lemmas are re-exported here via [include]. *)

include TLS13.Wire.Spec.Reveal.Record
include TLS13.Wire.Spec.Reveal.CertificateVerify
include TLS13.Wire.Spec.Reveal.Finished
include TLS13.Wire.Spec.Reveal.Alert
