module TLS13.Wire.Spec.Reveal.Alert

module B = TLS13.Bytes
module GA = TLS13.Wire.Generated.Alert
module LP = LowParse.Spec
module M = TLS13.Messages
module T = TLS13.Types
module WS = TLS13.Wire.Spec

val lemma_ptm_alert:
  fragment:B.bytes ->
  Lemma (ensures WS.parse_tls_message T.Alert fragment ==
    (match LP.parse GA.alert_parser fragment with
     | Some (alert, consumed) ->
       if consumed == B.length fragment
       then Some (M.TlsAlert alert.GA.description)
       else None
     | None -> None))
