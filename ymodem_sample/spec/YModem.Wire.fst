module YModem.Wire

(**
  Instantiation of the `Common.WireFormat.wire_format` type class for a YMODEM
  128-byte data-connection packet (see ymodem.qd.rfc and the generated module
  YModem.Wire.Generated.Ymodem_packet).

  This wraps the EverParse/QuackyDucky-generated LowParse spec parser/serializer
  into the residual-returning `Common.WireFormat` interface and discharges the
  round-trip laws (`wf_parse_serialize_exact`, `wfsl_parse_serialize_prefix`),
  using the fact that the generated packet parser has a *strong* (total,
  constant-size) parser kind — the same bridge as FTPBlock.Wire.fst.
**)

module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module LP = LowParse.Spec
module TCP = Common.TCP
module WF = Common.WireFormat

open YModem.Wire.Generated.Ymodem_packet

let ymodem_serialize (m:ymodem_packet) : GTot TCP.bytes =
  LP.serialize ymodem_packet_serializer m

let ymodem_parse (input:TCP.bytes) : GTot (WF.parse_result ymodem_packet) =
  match LP.parse ymodem_packet_parser input with
  | None -> None
  | Some (v, consumed) -> Some (v, Seq.slice input consumed (Seq.length input))

let lemma_ymodem_parse_serialize_exact (m:ymodem_packet)
  : Lemma
      (ensures
        exists parsed.
          ymodem_parse (ymodem_serialize m) == Some (parsed, Seq.empty) /\
          parsed == m)
=
  let b = ymodem_serialize m in
  LP.parse_serialize ymodem_packet_serializer m;
  Seq.lemma_eq_elim (Seq.slice b (Seq.length b) (Seq.length b)) Seq.empty;
  assert (ymodem_parse (ymodem_serialize m) == Some (m, Seq.empty))

let lemma_ymodem_parse_serialize_prefix (m:ymodem_packet) (rest:TCP.bytes)
  : Lemma
      (ensures
        exists parsed.
          ymodem_parse (Seq.append (ymodem_serialize m) rest) == Some (parsed, rest) /\
          parsed == m)
=
  let b = ymodem_serialize m in
  LP.parse_serialize ymodem_packet_serializer m;
  SP.append_slices b rest;
  LP.parse_strong_prefix ymodem_packet_parser b (Seq.append b rest);
  assert (ymodem_parse (Seq.append b rest) == Some (m, rest))

noextract
let ymodem_wire_format : WF.wire_format ymodem_packet =
{
  WF.wf_serialize = ymodem_serialize;
  WF.wf_parse = ymodem_parse;
  WF.wf_parse_serialize_exact = lemma_ymodem_parse_serialize_exact;
}

noextract
let ymodem_wire_format_stream_laws
  : WF.wire_format_stream_laws ymodem_packet ymodem_wire_format =
{
  WF.wfsl_parse_serialize_prefix = lemma_ymodem_parse_serialize_prefix;
}
