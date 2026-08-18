module TLS13.ConnectionState.ProtectedWireStream

module B = TLS13.Bytes
module M = TLS13.Messages
module RD = TLS13.Wire.Spec.RevealDecode
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties
module T = TLS13.Types
module W = TLS13.Wire.Spec
module WU = TLS13.Wire.Spec.Reveal.Util

let lemma_append_heads_equal_same_len
  #a
  (left:Seq.seq a)
  (left_tail:Seq.seq a)
  (right:Seq.seq a)
  (right_tail:Seq.seq a)
  : Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.length left == Seq.length right)
    (ensures Seq.equal left right)
=
  let left_full = Seq.append left left_tail in
  let right_full = Seq.append right right_tail in
  WU.lemma_slice_append_left left left_tail;
  WU.lemma_slice_append_left right right_tail;
  Seq.lemma_eq_elim left_full right_full;
  assert (Seq.equal (Seq.slice right_full 0 (Seq.length left)) right);
  assert (Seq.equal (Seq.slice left_full 0 (Seq.length left)) right);
  Seq.lemma_eq_elim (Seq.slice left_full 0 (Seq.length left)) left

let lemma_append_tails_equal_same_len
  #a
  (left:Seq.seq a)
  (left_tail:Seq.seq a)
  (right:Seq.seq a)
  (right_tail:Seq.seq a)
  : Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.length left == Seq.length right)
    (ensures Seq.equal left_tail right_tail)
=
  SeqProps.lemma_append_inj left left_tail right right_tail;
  assert (Seq.equal left_tail right_tail)

let lemma_append_tails_equal_from_equal_heads
  #a
  (left:Seq.seq a)
  (left_tail:Seq.seq a)
  (right:Seq.seq a)
  (right_tail:Seq.seq a)
  : Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.equal left right)
    (ensures Seq.equal left_tail right_tail)
=
  Seq.lemma_eq_elim left right;
  lemma_append_tails_equal_same_len left left_tail right right_tail

let lemma_raw_delta_heads_equal_same_len
  (sender_delta:B.bytes)
  (sender_tail:B.bytes)
  (receiver_delta:B.bytes)
  (receiver_tail:B.bytes)
  : Lemma
    (requires
      Seq.equal
        (B.append sender_delta sender_tail)
        (B.append receiver_delta receiver_tail) /\
      B.length sender_delta == B.length receiver_delta)
    (ensures Seq.equal sender_delta receiver_delta)
=
  lemma_append_heads_equal_same_len
    sender_delta
    sender_tail
    receiver_delta
    receiver_tail

let lemma_equal_streams_skip_empty_left
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (left_tail:B.bytes)
  : Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append B.empty left_tail))
    (ensures Seq.equal left_tail right_stream)
=
  Seq.append_empty_l left_tail;
  Seq.lemma_eq_elim left_stream right_stream;
  Seq.lemma_eq_elim left_stream (B.append B.empty left_tail)

let lemma_equal_streams_skip_empty_right
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (right_tail:B.bytes)
  : Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal right_stream (B.append B.empty right_tail))
    (ensures Seq.equal left_stream right_tail)
=
  Seq.append_empty_l right_tail;
  Seq.lemma_eq_elim left_stream right_stream;
  Seq.lemma_eq_elim right_stream (B.append B.empty right_tail)

let lemma_equal_streams_skip_empty_both
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (left_tail:B.bytes)
  (right_tail:B.bytes)
  : Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append B.empty left_tail) /\
      Seq.equal right_stream (B.append B.empty right_tail))
    (ensures Seq.equal left_tail right_tail)
=
  lemma_equal_streams_skip_empty_left left_stream right_stream left_tail;
  lemma_equal_streams_skip_empty_right left_tail right_stream right_tail

#push-options "--z3rlimit 10"
let lemma_equal_stream_record_head_lengths
  (left_stream:B.bytes)
  (right_stream:B.bytes)
  (left_head:B.bytes)
  (left_tail:B.bytes)
  (right_head:B.bytes)
  (right_tail:B.bytes)
  (left_ct:T.content_type)
  (left_fragment:M.sealed_record)
  (right_ct:T.content_type)
  (right_fragment:M.sealed_record)
  : Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append left_head left_tail) /\
      Seq.equal right_stream (B.append right_head right_tail) /\
      W.parse_record_wire left_head ==
        Some (left_ct, left_fragment, B.length left_head) /\
      W.parse_record_wire right_head ==
        Some (right_ct, right_fragment, B.length right_head))
    (ensures B.length left_head == B.length right_head)
=
  WU.lemma_slice_append_left left_head left_tail;
  WU.lemma_slice_append_left right_head right_tail;
  Seq.lemma_len_append left_head left_tail;
  Seq.lemma_len_append right_head right_tail;
  Seq.lemma_eq_elim left_stream (B.append left_head left_tail);
  assert (Seq.equal (Seq.slice left_stream 0 (B.length left_head)) left_head);
  Seq.lemma_eq_elim (Seq.slice left_stream 0 (B.length left_head)) left_head;
  RD.lemma_parse_record_wire_from_prefix
    left_stream
    left_ct
    left_fragment
    (B.length left_head);
  assert (W.parse_record_wire left_stream ==
    Some (left_ct, left_fragment, B.length left_head));
  Seq.lemma_eq_elim right_stream (B.append right_head right_tail);
  assert (Seq.equal (Seq.slice right_stream 0 (B.length right_head)) right_head);
  Seq.lemma_eq_elim (Seq.slice right_stream 0 (B.length right_head)) right_head;
  RD.lemma_parse_record_wire_from_prefix
    right_stream
    right_ct
    right_fragment
    (B.length right_head);
  assert (W.parse_record_wire right_stream ==
    Some (right_ct, right_fragment, B.length right_head));
  Seq.lemma_eq_elim left_stream right_stream;
  assert (Some (left_ct, left_fragment, B.length left_head) ==
          Some (right_ct, right_fragment, B.length right_head))
#pop-options
