module TLS13.Wire.Spec.Reveal.Alert

friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

private let lemma_nat_of_byte_reveal (b:B.byte)
  : Lemma (WS.nat_of_byte b == U8.v b) =
  ()

private let lemma_alert_description_of_byte_reveal (b:B.byte)
  : Lemma (WS.alert_description_of_byte b ==
      (match U8.v b with
       | 0   -> Some T.CloseNotify
       | 10  -> Some T.UnexpectedMessage
       | 20  -> Some T.BadRecordMac
       | 40  -> Some T.HandshakeFailure
       | 46  -> Some T.CertificateUnknown
       | 47  -> Some T.IllegalParameter
       | 50  -> Some T.DecodeError
       | 51  -> Some T.DecryptError
       | 70  -> Some T.ProtocolVersion
       | 110 -> Some T.UnsupportedExtension
       | _   -> None)) =
  lemma_nat_of_byte_reveal b;
  match WS.nat_of_byte b with
  | 0 -> assert (U8.v b == 0)
  | 10 -> assert (U8.v b == 10)
  | 20 -> assert (U8.v b == 20)
  | 40 -> assert (U8.v b == 40)
  | 46 -> assert (U8.v b == 46)
  | 47 -> assert (U8.v b == 47)
  | 50 -> assert (U8.v b == 50)
  | 51 -> assert (U8.v b == 51)
  | 70 -> assert (U8.v b == 70)
  | 110 -> assert (U8.v b == 110)
  | _ -> ()

let lemma_ptm_alert fragment =
  if B.length fragment == 2 then (
    assert (B.length fragment == 2);
    lemma_alert_description_of_byte_reveal (Seq.index fragment 1)
  ) else (
    assert (not (B.length fragment == 2))
  )
