module Common.WireFormat

module Seq = FStar.Seq
module TCP = Common.TCP

type parse_result (wire_message:Type0) =
  option (wire_message & TCP.bytes)

noextract
class wire_format (wire_message:Type0) =
{
  wf_serialize:
    wire_message -> GTot TCP.bytes;

  wf_parse:
    TCP.bytes -> GTot (parse_result wire_message);

  wf_parse_serialize_exact:
    msg:wire_message ->
      Lemma
        (ensures wf_parse (wf_serialize msg) == Some (msg, Seq.empty));

  wf_parse_serialize_prefix:
    msg:wire_message ->
    rest:TCP.bytes ->
      Lemma
        (ensures
          wf_parse (Seq.append (wf_serialize msg) rest) == Some (msg, rest));
}

let rec serialize_with_tail
  (#wire_message:Type0)
  (fmt:wire_format wire_message)
  (msgs:list wire_message)
  (tail:TCP.bytes)
  : GTot TCP.bytes
        (decreases msgs)
=
  match msgs with
  | [] -> tail
  | msg :: rest ->
    Seq.append (fmt.wf_serialize msg) (serialize_with_tail fmt rest tail)

let serialize_all
  (#wire_message:Type0)
  (fmt:wire_format wire_message)
  (msgs:list wire_message)
  : GTot TCP.bytes =
  serialize_with_tail fmt msgs Seq.empty

let rec parses_as
  (#wire_message:Type0)
  (fmt:wire_format wire_message)
  (bytes:TCP.bytes)
  (msgs:list wire_message)
  (residual:TCP.bytes)
  : GTot prop
        (decreases msgs)
=
  match msgs with
  | [] ->
    Seq.equal bytes residual
  | msg :: rest ->
    exists bytes_after_msg.
      fmt.wf_parse bytes == Some (msg, bytes_after_msg) /\
      parses_as fmt bytes_after_msg rest residual

let rec lemma_parse_serialize_with_tail_inverse
  (#wire_message:Type0)
  (fmt:wire_format wire_message)
  (msgs:list wire_message)
  (tail:TCP.bytes)
  : Lemma
      (ensures parses_as fmt (serialize_with_tail fmt msgs tail) msgs tail)
      (decreases msgs)
=
  match msgs with
  | [] ->
    assert (Seq.equal tail tail)
  | msg :: rest ->
    fmt.wf_parse_serialize_prefix msg (serialize_with_tail fmt rest tail);
    lemma_parse_serialize_with_tail_inverse fmt rest tail;
    assert (parses_as fmt (serialize_with_tail fmt rest tail) rest tail);
    assert (exists bytes_after_msg.
      fmt.wf_parse (serialize_with_tail fmt (msg :: rest) tail) ==
        Some (msg, bytes_after_msg) /\
      parses_as fmt bytes_after_msg rest tail)

let lemma_parse_serialize_all_inverse
  (#wire_message:Type0)
  (fmt:wire_format wire_message)
  (msgs:list wire_message)
  : Lemma
      (ensures parses_as fmt (serialize_all fmt msgs) msgs Seq.empty)
=
  lemma_parse_serialize_with_tail_inverse fmt msgs Seq.empty
