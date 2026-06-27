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
         | 0   -> Some (M.TlsAlert T.Close_notify)
         | 10  -> Some (M.TlsAlert T.Unexpected_message)
         | 20  -> Some (M.TlsAlert T.Bad_record_mac)
         | 40  -> Some (M.TlsAlert T.Handshake_failure)
         | 46  -> Some (M.TlsAlert T.Certificate_unknown)
         | 47  -> Some (M.TlsAlert T.Illegal_parameter)
         | 50  -> Some (M.TlsAlert T.Decode_error)
         | 51  -> Some (M.TlsAlert T.Decrypt_error)
         | 70  -> Some (M.TlsAlert T.Protocol_version)
         | 110 -> Some (M.TlsAlert T.Unsupported_extension)
         | _   -> None)
    else WS.parse_tls_message T.Alert fragment == None))
