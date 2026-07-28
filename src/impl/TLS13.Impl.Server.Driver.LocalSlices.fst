module TLS13.Impl.Server.Driver.LocalSlices

module B = TLS13.Bytes
module Seq = FStar.Seq
module U8 = FStar.UInt8

let lemma_exact_prefix_from_indices
  (prefix:B.bytes)
  (bytes:B.bytes)
  (len:nat{
    B.length prefix == len /\
    len <= B.length bytes
  })
  : Lemma
      (requires
        forall (i:nat{i < B.length prefix}).
          Seq.index prefix i == Seq.index bytes i)
      (ensures Seq.equal prefix (Seq.slice bytes 0 len))
=
  Seq.lemma_len_slice bytes 0 len;
  let index_proof (i:nat{i < B.length prefix})
    : Lemma (
        Seq.index prefix i == Seq.index (Seq.slice bytes 0 len) i)
    =
    assert (Seq.index prefix i == Seq.index bytes i);
    Seq.lemma_index_slice bytes 0 len i
  in
  FStar.Classical.forall_intro
    #(i:nat{i < B.length prefix})
    #(fun i ->
      Seq.index prefix i == Seq.index (Seq.slice bytes 0 len) i)
    index_proof;
  Seq.lemma_eq_intro prefix (Seq.slice bytes 0 len)

let lemma_mask_slice_values
  (mask:Seq.seq (option U8.t))
  (bytes:B.bytes)
  (len:nat{
    len <= Seq.length mask /\
    Seq.length mask <= B.length bytes
  })
  : Lemma
      (requires
        forall (i:nat). i < Seq.length mask ==>
          Seq.index mask i == Some (Seq.index bytes i))
      (ensures
        (forall (i:nat{i < len}).
          Seq.index (Seq.slice mask 0 len) i ==
            Some (Seq.index bytes i)) /\
        (forall (i:nat).
          i < Seq.length (Seq.slice mask 0 len) ==>
            Some? (Seq.index (Seq.slice mask 0 len) i)))
=
  let index_proof (i:nat{i < len})
    : Lemma (
        Seq.index (Seq.slice mask 0 len) i ==
          Some (Seq.index bytes i))
    =
    assert (Seq.index mask i == Some (Seq.index bytes i));
    Seq.lemma_index_slice mask 0 len i
  in
  FStar.Classical.forall_intro
    #(i:nat{i < len})
    #(fun i ->
      Seq.index (Seq.slice mask 0 len) i ==
        Some (Seq.index bytes i))
    index_proof;
  Seq.lemma_len_slice mask 0 len;
  let some_proof (i:nat)
    : Lemma (
        i < Seq.length (Seq.slice mask 0 len) ==>
          Some? (Seq.index (Seq.slice mask 0 len) i))
    =
    if i < Seq.length (Seq.slice mask 0 len) then (
      assert (i < len);
      Seq.lemma_index_slice mask 0 len i;
      assert (Seq.index mask i == Some (Seq.index bytes i))
    )
  in
  FStar.Classical.forall_intro
    #(i:nat)
    #(fun i ->
      i < Seq.length (Seq.slice mask 0 len) ==>
        Some? (Seq.index (Seq.slice mask 0 len) i))
    some_proof
