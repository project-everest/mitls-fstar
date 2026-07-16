module FTPBlock.Wire

(**
  Instantiation of the `Common.WireFormat.wire_format` type class for the FTP
  block-mode (MODE B) data block, RFC 959 Section 3.4.2.

  The per-message wire format is the EverParse/QuackyDucky-generated parser and
  serializer for the `ftp_block` type (see ftp_block.qd.rfc and the generated
  module FTPBlock.Wire.Generated.Ftp_block).  This module wraps the LowParse
  spec-level parser/serializer into the `Common.WireFormat` interface — which
  expresses parsing as returning the message plus the *residual* input — and
  discharges the round-trip laws:

    * `wf_parse_serialize_exact` — parsing a serialized block yields the block
      and empty residual;
    * `wfsl_parse_serialize_prefix` — parsing a serialized block followed by
      arbitrary trailing bytes yields the block and exactly those trailing bytes
      as residual (the stream law), using the fact that the generated parser has
      a *strong* parser kind.

  These are exactly the obligations `Common.WireFormat` and its stream laws
  require to sequence a byte stream into a list of messages, as consumed by
  `Common.WireFormatStateMachine`.
**)

module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module LP = LowParse.Spec
module TCP = Common.TCP
module WF = Common.WireFormat

open FTPBlock.Wire.Generated.Ftp_block

(* Serialize a block with the generated LowParse serializer.  LowParse's `bytes`
   is `Seq.seq FStar.UInt8.t`, definitionally equal to `Common.TCP.bytes`. *)
let ftp_serialize (m:ftp_block) : GTot TCP.bytes =
  LP.serialize ftp_block_serializer m

(* Parse one block off the front of the input, returning it together with the
   unconsumed residual bytes (the `Common.WireFormat` convention). *)
let ftp_parse (input:TCP.bytes) : GTot (WF.parse_result ftp_block) =
  match LP.parse ftp_block_parser input with
  | None -> None
  | Some (v, consumed) -> Some (v, Seq.slice input consumed (Seq.length input))

(* Round-trip: parsing a freshly serialized block consumes all of it, leaving an
   empty residual. *)
let lemma_ftp_parse_serialize_exact (m:ftp_block)
  : Lemma
      (ensures
        exists parsed.
          ftp_parse (ftp_serialize m) == Some (parsed, Seq.empty) /\
          parsed == m)
=
  let b = ftp_serialize m in
  LP.parse_serialize ftp_block_serializer m;
  Seq.lemma_eq_elim (Seq.slice b (Seq.length b) (Seq.length b)) Seq.empty;
  assert (ftp_parse (ftp_serialize m) == Some (m, Seq.empty))

(* Stream law: parsing a serialized block followed by any trailing bytes yields
   the block and exactly those trailing bytes.  Relies on the generated parser
   having a strong parser kind (LP.strong_parser_kind 3 65538 None). *)
let lemma_ftp_parse_serialize_prefix (m:ftp_block) (rest:TCP.bytes)
  : Lemma
      (ensures
        exists parsed.
          ftp_parse (Seq.append (ftp_serialize m) rest) == Some (parsed, rest) /\
          parsed == m)
=
  let b = ftp_serialize m in
  LP.parse_serialize ftp_block_serializer m;
  SP.append_slices b rest;
  LP.parse_strong_prefix ftp_block_parser b (Seq.append b rest);
  assert (ftp_parse (Seq.append b rest) == Some (m, rest))

noextract
let ftp_block_wire_format : WF.wire_format ftp_block =
{
  WF.wf_serialize = ftp_serialize;
  WF.wf_parse = ftp_parse;
  WF.wf_parse_serialize_exact = lemma_ftp_parse_serialize_exact;
}

noextract
let ftp_block_wire_format_stream_laws
  : WF.wire_format_stream_laws ftp_block ftp_block_wire_format =
{
  WF.wfsl_parse_serialize_prefix = lemma_ftp_parse_serialize_prefix;
}
