module YModem.Wire

(**
  Instantiation of the `Common.WireFormat.wire_format` type class for the YMODEM
  wire messages — a single leading-byte-discriminated union of the sender's
  128-byte data/header packet (SOH) and end-of-file marker (EOT), and the
  receiver's single-byte control acknowledgements (ACK, NAK, CAN, 'C').  See
  ymodem.qd.rfc and the generated module YModem.Wire.Generated.Ymodem_message.

  This wraps the EverParse/QuackyDucky-generated LowParse spec parser/serializer
  into the residual-returning `Common.WireFormat` interface and discharges the
  round-trip laws (`wf_parse_serialize_exact`, `wfsl_parse_serialize_prefix`).
  The union parser is variable-size (1..133 bytes) but *strong* (leading-byte
  discriminated — `strong_parser_kind 1 133`), which is exactly what the
  strong-prefix stream law needs; the same bridge as FTPBlock.Wire.fst, now over
  a variable-size union rather than a fixed record.
**)

module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module LP = LowParse.Spec
module TCP = Common.TCP
module WF = Common.WireFormat

open YModem.Wire.Generated.Ymodem_message

let ymodem_serialize (m:ymodem_message) : GTot TCP.bytes =
  LP.serialize ymodem_message_serializer m

let ymodem_parse (input:TCP.bytes) : GTot (WF.parse_result ymodem_message) =
  match LP.parse ymodem_message_parser input with
  | None -> None
  | Some (v, consumed) -> Some (v, Seq.slice input consumed (Seq.length input))

let lemma_ymodem_parse_serialize_exact (m:ymodem_message)
  : Lemma
      (ensures
        exists parsed.
          ymodem_parse (ymodem_serialize m) == Some (parsed, Seq.empty) /\
          parsed == m)
=
  let b = ymodem_serialize m in
  LP.parse_serialize ymodem_message_serializer m;
  Seq.lemma_eq_elim (Seq.slice b (Seq.length b) (Seq.length b)) Seq.empty;
  assert (ymodem_parse (ymodem_serialize m) == Some (m, Seq.empty))

let lemma_ymodem_parse_serialize_prefix (m:ymodem_message) (rest:TCP.bytes)
  : Lemma
      (ensures
        exists parsed.
          ymodem_parse (Seq.append (ymodem_serialize m) rest) == Some (parsed, rest) /\
          parsed == m)
=
  let b = ymodem_serialize m in
  LP.parse_serialize ymodem_message_serializer m;
  SP.append_slices b rest;
  LP.parse_strong_prefix ymodem_message_parser b (Seq.append b rest);
  assert (ymodem_parse (Seq.append b rest) == Some (m, rest))

noextract
let ymodem_wire_format : WF.wire_format ymodem_message =
{
  WF.wf_serialize = ymodem_serialize;
  WF.wf_parse = ymodem_parse;
  WF.wf_parse_serialize_exact = lemma_ymodem_parse_serialize_exact;
}

noextract
let ymodem_wire_format_stream_laws
  : WF.wire_format_stream_laws ymodem_message ymodem_wire_format =
{
  WF.wfsl_parse_serialize_prefix = lemma_ymodem_parse_serialize_prefix;
}
