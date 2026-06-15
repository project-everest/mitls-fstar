module TLS13.Impl.Server.Driver.Network

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

let pending_after_consumed (buffered_len consumed_len:SZ.t) : SZ.t =
  if SZ.lte consumed_len buffered_len
  then SZ.sub buffered_len consumed_len
  else 0sz

fn compact_buffer_suffix
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires pts_to raw 'raw_bytes **
           pure (B.length 'raw_bytes == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures exists* raw_after.
           pts_to raw raw_after **
           pure (B.length raw_after == SZ.v raw_capacity /\
                 B.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity /\
                 new_len == pending_after_consumed buffered_len consumed_len /\
                 SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
                 SZ.v new_len <= SZ.v buffered_len /\
                 Seq.equal
                   (Seq.slice raw_after 0 (SZ.v new_len))
                   (Seq.slice (Ghost.reveal 'raw_bytes)
                     (SZ.v consumed_len)
                     (SZ.v buffered_len)))
{
  let new_len = SZ.sub buffered_len consumed_len;
  assert (pure (new_len == pending_after_consumed buffered_len consumed_len));
  assert (pure (SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len));
  assert (pure (SZ.v new_len <= SZ.v buffered_len));
  let no_shift = consumed_len = 0sz;
  if no_shift {
    assert (pure (new_len == buffered_len));
    assert (pure (Seq.equal
      (Seq.slice (Ghost.reveal 'raw_bytes) 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes)
        (SZ.v consumed_len)
        (SZ.v buffered_len))));
    new_len
  } else {
    let mut i = 0sz;
    while ((R.read i) `SZ.lt` new_len)
      invariant live i
      invariant exists* raw_loop.
        pts_to raw raw_loop **
        pure (B.length raw_loop == SZ.v raw_capacity /\
              SZ.v (R.read i) <= SZ.v new_len /\
              SZ.v new_len == SZ.v buffered_len - SZ.v consumed_len /\
              SZ.v new_len <= SZ.v buffered_len /\
              SZ.v consumed_len <= SZ.v buffered_len /\
              SZ.v buffered_len <= SZ.v raw_capacity /\
              (forall (k:nat). k < SZ.v (R.read i) ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)) /\
              (forall (k:nat). SZ.v (R.read i) <= k /\ k < SZ.v buffered_len ==>
                Seq.index raw_loop k ==
                Seq.index (Ghost.reveal 'raw_bytes) k))
    {
      let vi = R.read i;
      assert (pure (SZ.v vi < SZ.v new_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v buffered_len));
      assert (pure (SZ.v vi + SZ.v consumed_len < SZ.v raw_capacity));
      SZ.fits_lte (SZ.v vi + SZ.v consumed_len) (SZ.v raw_capacity);
      let src_idx = vi `SZ.add` consumed_len;
      assert (pure (SZ.v src_idx < SZ.v raw_capacity));
      with raw_before_read.
        assert (pts_to raw raw_before_read);
      assert (pure (B.length raw_before_read == SZ.v raw_capacity));
      let b = raw.(src_idx);
      assert (pure (b == Seq.index (Ghost.reveal 'raw_bytes)
        (SZ.v vi + SZ.v consumed_len)));
      assert (pure (SZ.v vi < SZ.v raw_capacity));
      raw.(vi) <- b;
      with raw_after_write.
        assert (pts_to raw raw_after_write);
      assert (pure (B.length raw_after_write == SZ.v raw_capacity));
      assert (pure (forall (k:nat). k < SZ.v vi + 1 ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
      assert (pure (forall (k:nat). SZ.v vi + 1 <= k /\ k < SZ.v buffered_len ==>
        Seq.index raw_after_write k ==
        Seq.index (Ghost.reveal 'raw_bytes) k));
      assert (pure (SZ.v vi + 1 <= SZ.v new_len));
      SZ.fits_lte (SZ.v vi + 1) (SZ.v new_len);
      let next_i = vi `SZ.add` 1sz;
      R.write i next_i;
    };
    with raw_done.
      assert (pts_to raw raw_done);
    assert (pure (B.length raw_done == SZ.v raw_capacity));
    assert (pure (forall (k:nat). k < SZ.v new_len ==>
      Seq.index raw_done k ==
      Seq.index (Ghost.reveal 'raw_bytes) (k + SZ.v consumed_len)));
    Seq.lemma_len_slice raw_done 0 (SZ.v new_len);
    Seq.lemma_len_slice (Ghost.reveal 'raw_bytes)
      (SZ.v consumed_len)
      (SZ.v buffered_len);
    assert (pure (forall (k:nat). k < B.length (Seq.slice raw_done 0 (SZ.v new_len)) ==>
      Seq.index (Seq.slice raw_done 0 (SZ.v new_len)) k ==
      Seq.index
        (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len))
        k));
    Seq.lemma_eq_intro
      (Seq.slice raw_done 0 (SZ.v new_len))
      (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v consumed_len) (SZ.v buffered_len));
    new_len
  }
}
