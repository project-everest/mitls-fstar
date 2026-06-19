module TLS13.Wire.Spec.Reveal.Alert

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

val lemma_ptm_alert:
  fragment:B.bytes ->
  Lemma (ensures (
    if B.length fragment == 2
    then
      WS.parse_tls_message T.Alert fragment ==
        (match U8.v (Seq.index fragment 1) with
         | 0   -> Some (M.TlsAlert T.CloseNotify)
         | 10  -> Some (M.TlsAlert T.UnexpectedMessage)
         | 20  -> Some (M.TlsAlert T.BadRecordMac)
         | 40  -> Some (M.TlsAlert T.HandshakeFailure)
         | 46  -> Some (M.TlsAlert T.CertificateUnknown)
         | 47  -> Some (M.TlsAlert T.IllegalParameter)
         | 50  -> Some (M.TlsAlert T.DecodeError)
         | 51  -> Some (M.TlsAlert T.DecryptError)
         | 70  -> Some (M.TlsAlert T.ProtocolVersion)
         | 110 -> Some (M.TlsAlert T.UnsupportedExtension)
         | _   -> None)
    else WS.parse_tls_message T.Alert fragment == None))
