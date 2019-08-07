module Crypto.Util.IntCast
module I = Lib.IntTypes
module U8 = FStar.UInt8
module Seq = FStar.Seq
module B = LowStar.Buffer
module HS = FStar.HyperStack

noextract
val to_uint8 (x: I.uint8) : Tot (y: U8.t { I.v x == U8.v y })

noextract
val to_seq_uint8 (x: Seq.seq I.uint8) : Tot (y: Seq.seq U8.t { Seq.length y == Seq.length x })

val to_seq_uint8_correct (x: Seq.seq I.uint8) (i: nat { i < Seq.length x }) : Lemma
  (to_uint8 (Seq.index x i) == Seq.index (to_seq_uint8 x) i)

noextract
inline_for_extraction
val to_buf_uint8 (x: B.buffer I.uint8) : Tot (y: B.buffer U8.t {B.length y == B.length x})

val to_buf_uint8_correct (x: B.buffer I.uint8) (h: HS.mem) : Lemma
  (to_seq_uint8 (B.as_seq h x) == B.as_seq h (to_buf_uint8 x))

val live_to_buf_uint8 (x: B.buffer I.uint8) (h: HS.mem) : Lemma
  (B.live h (to_buf_uint8 x) <==> B.live h x)

val loc_buffer_to_buf_uint8 (x: B.buffer I.uint8) : Lemma
  (B.loc_buffer (to_buf_uint8 x) == B.loc_buffer x)

noextract
val to_sec8 (x: U8.t) : Tot (y: I.uint8 { I.v y == U8.v x })

noextract
val to_seq_sec8 (x: Seq.seq U8.t) : Tot (y: Seq.seq I.uint8 { Seq.length y == Seq.length x })

val to_seq_sec8_correct (x: Seq.seq U8.t) (i: nat { i < Seq.length x }) : Lemma
  (to_sec8 (Seq.index x i) == Seq.index (to_seq_sec8 x) i)

let to_seq_sec8_to_seq_uint8 (x: Seq.seq I.uint8) : Lemma
  (to_seq_sec8 (to_seq_uint8 x) `Seq.equal` x)
= Classical.forall_intro (Classical.move_requires (to_seq_uint8_correct x));
  Classical.forall_intro (Classical.move_requires (to_seq_sec8_correct (to_seq_uint8 x)))

let to_seq_uint8_to_seq_sec8 (x: Seq.seq U8.t) : Lemma
  (to_seq_uint8 (to_seq_sec8 x) `Seq.equal` x)
= Classical.forall_intro (Classical.move_requires (to_seq_sec8_correct x));
  Classical.forall_intro (Classical.move_requires (to_seq_uint8_correct (to_seq_sec8 x)))

noextract
inline_for_extraction
val to_buf_sec8
  (x: B.buffer U8.t)
: Tot (y: B.buffer I.uint8 { B.length y == B.length x })

val to_buf_sec8_correct
  (x: B.buffer U8.t)
  (h: HS.mem)
: Lemma
  (to_seq_sec8 (B.as_seq h x) == B.as_seq h (to_buf_sec8 x))

val live_to_buf_sec8 (x: B.buffer I.uint8) (h: HS.mem) : Lemma
  (B.live h (to_buf_uint8 x) <==> B.live h x)

val loc_buffer_to_buf_sec8 (x: B.buffer U8.t) : Lemma
  (B.loc_buffer (to_buf_sec8 x) == B.loc_buffer x)

val to_buf_sec8_to_buf_uint8
  (x: B.buffer I.uint8)
: Lemma
  (to_buf_sec8 (to_buf_uint8 x) == x)

val to_buf_uint8_to_buf_sec8
  (x: B.buffer U8.t)
: Lemma
  (to_buf_uint8 (to_buf_sec8 x) == x)
