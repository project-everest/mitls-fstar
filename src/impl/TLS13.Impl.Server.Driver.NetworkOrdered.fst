module TLS13.Impl.Server.Driver.NetworkOrdered

#set-options "--split_queries always"

module B = TLS13.Bytes
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CT = TLS13.Impl.Client.Types
module CM = TLS13.Impl.ConnectionState.Model
module ID = FStar.IndefiniteDescription
module M = TLS13.Messages
module Seq = FStar.Seq
module ST = TLS13.Impl.Server.Types
module T = TLS13.Types

open TLS13.Impl.Server.Driver.State

let lemma_slice_mask_matches_bytes
  (mask:Seq.seq (option FStar.UInt8.t))
  (bytes:B.bytes)
  (hi:nat{hi <= Seq.length mask})
  : Lemma
      (requires
        Seq.length mask == B.length bytes /\
        (forall (i:nat). i < Seq.length mask ==>
          Seq.index mask i == Some (Seq.index bytes i)))
      (ensures
        forall (i:nat). i < Seq.length (Seq.slice mask 0 hi) ==>
          Seq.index (Seq.slice mask 0 hi) i ==
            Some (Seq.index bytes i))
=
  Seq.lemma_len_slice mask 0 hi;
  let index_proof
    (i:nat{i < Seq.length (Seq.slice mask 0 hi)})
    : Lemma
        (Seq.index (Seq.slice mask 0 hi) i ==
          Some (Seq.index bytes i))
  =
    Seq.lemma_index_slice mask 0 hi i
  in
  FStar.Classical.forall_intro
    #(i:nat{i < Seq.length (Seq.slice mask 0 hi)})
    #(fun i ->
      Seq.index (Seq.slice mask 0 hi) i ==
        Some (Seq.index bytes i))
    index_proof

let lemma_prefix_mask_matches_bytes
  (prefix:B.bytes)
  (bytes:B.bytes)
  (mask:Seq.seq (option FStar.UInt8.t))
  (hi:nat{hi <= B.length bytes})
  : Lemma
      (requires
        B.length prefix == hi /\
        Seq.length mask == hi /\
        Seq.equal prefix (Seq.slice bytes 0 hi) /\
        (forall (i:nat). i < Seq.length mask ==>
          Seq.index mask i == Some (Seq.index prefix i)))
      (ensures
        forall (i:nat). i < Seq.length mask ==>
          Seq.index mask i == Some (Seq.index bytes i))
=
  Seq.lemma_eq_elim prefix (Seq.slice bytes 0 hi);
  let index_proof
    (i:nat{i < Seq.length mask})
    : Lemma
        (Seq.index mask i == Some (Seq.index bytes i))
  =
    Seq.lemma_index_slice bytes 0 hi i
  in
  FStar.Classical.forall_intro
    #(i:nat{i < Seq.length mask})
    #(fun i ->
      Seq.index mask i == Some (Seq.index bytes i))
    index_proof

let lemma_equal_prefix_of_indexes
  (prefix:B.bytes)
  (bytes:B.bytes)
  (hi:nat{hi <= B.length bytes})
  : Lemma
      (requires
        B.length prefix == hi /\
        (forall (i:nat). i < hi ==>
          Seq.index prefix i == Seq.index bytes i))
      (ensures Seq.equal prefix (Seq.slice bytes 0 hi))
=
  Seq.lemma_len_slice bytes 0 hi;
  let index_proof
    (i:nat{i < B.length (Seq.slice bytes 0 hi)})
    : Lemma
        (Seq.index prefix i == Seq.index (Seq.slice bytes 0 hi) i)
  =
    Seq.lemma_index_slice bytes 0 hi i
  in
  FStar.Classical.forall_intro
    #(i:nat{i < B.length (Seq.slice bytes 0 hi)})
    #(fun i ->
      Seq.index prefix i == Seq.index (Seq.slice bytes 0 hi) i)
    index_proof;
  Seq.lemma_eq_intro prefix (Seq.slice bytes 0 hi)

let lemma_equal_slice_of_prefix
  (prefix:B.bytes)
  (bytes:B.bytes)
  (lo:nat)
  (hi:nat{
    lo <= hi /\
    hi <= B.length prefix /\
    hi <= B.length bytes
  })
  : Lemma
      (requires Seq.equal prefix (Seq.slice bytes 0 hi))
      (ensures
        Seq.equal
          (Seq.slice prefix lo hi)
          (Seq.slice bytes lo hi))
=
  Seq.lemma_eq_elim prefix (Seq.slice bytes 0 hi);
  FStar.Seq.Properties.slice_slice bytes 0 hi lo hi
