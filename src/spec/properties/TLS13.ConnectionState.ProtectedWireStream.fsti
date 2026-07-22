module TLS13.ConnectionState.ProtectedWireStream

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module W = TLS13.Wire.Spec

val lemma_append_heads_equal_same_len:
  #a:eqtype ->
  left:Seq.seq a ->
  left_tail:Seq.seq a ->
  right:Seq.seq a ->
  right_tail:Seq.seq a ->
  Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.length left == Seq.length right)
    (ensures Seq.equal left right)

val lemma_append_tails_equal_same_len:
  #a:eqtype ->
  left:Seq.seq a ->
  left_tail:Seq.seq a ->
  right:Seq.seq a ->
  right_tail:Seq.seq a ->
  Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.length left == Seq.length right)
    (ensures Seq.equal left_tail right_tail)

val lemma_append_tails_equal_from_equal_heads:
  #a:eqtype ->
  left:Seq.seq a ->
  left_tail:Seq.seq a ->
  right:Seq.seq a ->
  right_tail:Seq.seq a ->
  Lemma
    (requires
      Seq.equal (Seq.append left left_tail) (Seq.append right right_tail) /\
      Seq.equal left right)
    (ensures Seq.equal left_tail right_tail)

val lemma_raw_delta_heads_equal_same_len:
  sender_delta:B.bytes ->
  sender_tail:B.bytes ->
  receiver_delta:B.bytes ->
  receiver_tail:B.bytes ->
  Lemma
    (requires
      Seq.equal
        (B.append sender_delta sender_tail)
        (B.append receiver_delta receiver_tail) /\
      B.length sender_delta == B.length receiver_delta)
    (ensures Seq.equal sender_delta receiver_delta)

val lemma_equal_streams_skip_empty_left:
  left_stream:B.bytes ->
  right_stream:B.bytes ->
  left_tail:B.bytes ->
  Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append B.empty left_tail))
    (ensures Seq.equal left_tail right_stream)

val lemma_equal_streams_skip_empty_right:
  left_stream:B.bytes ->
  right_stream:B.bytes ->
  right_tail:B.bytes ->
  Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal right_stream (B.append B.empty right_tail))
    (ensures Seq.equal left_stream right_tail)

val lemma_equal_streams_skip_empty_both:
  left_stream:B.bytes ->
  right_stream:B.bytes ->
  left_tail:B.bytes ->
  right_tail:B.bytes ->
  Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append B.empty left_tail) /\
      Seq.equal right_stream (B.append B.empty right_tail))
    (ensures Seq.equal left_tail right_tail)

val lemma_equal_stream_record_head_lengths:
  left_stream:B.bytes ->
  right_stream:B.bytes ->
  left_head:B.bytes ->
  left_tail:B.bytes ->
  right_head:B.bytes ->
  right_tail:B.bytes ->
  left_ct:T.content_type ->
  left_fragment:M.sealed_record ->
  right_ct:T.content_type ->
  right_fragment:M.sealed_record ->
  Lemma
    (requires
      Seq.equal left_stream right_stream /\
      Seq.equal left_stream (B.append left_head left_tail) /\
      Seq.equal right_stream (B.append right_head right_tail) /\
      W.parse_record_wire left_head ==
        Some (left_ct, left_fragment, B.length left_head) /\
      W.parse_record_wire right_head ==
        Some (right_ct, right_fragment, B.length right_head))
    (ensures B.length left_head == B.length right_head)
