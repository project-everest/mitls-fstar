module TLS13.Impl.Parser.CertChain

(**
  Pure (non-Pulse) list/sequence reasoning supporting the Certificate arm of
  TLS13.Impl.Parser.  The Certificate copy loop builds the fixed-size low-level
  [certificate_msg] representation by walking the parsed certificate_list and
  copying each entry's DER blob into a contiguous chain-bytes buffer, recording
  [(offset, length)] pairs.  This module proves the central invariant-extension
  lemma: appending one more entry (whose blob is written just past the current
  running offset, in a buffer whose already-written prefix is preserved) extends
  [IM.certificate_chain_matches] by one chain element.
*)

module B = TLS13.Bytes
module IM = TLS13.Impl.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module L = FStar.List.Tot

(* Re-association used to maintain the loop's prefix-product invariant
   [processed @ synth_chain(drop i) == synth_chain]. *)
let lemma_append_cons (#a:Type) (processed:list a) (x:a) (rest:list a)
  : Lemma (ensures L.append processed (x :: rest) ==
                   L.append (L.append processed [x]) rest)
  = L.append_assoc processed [x] rest

(* Two byte buffers that agree on their first [old_len] bytes agree on every
   slice contained in that prefix. *)
let lemma_slice_agree (s_old s_new:B.bytes) (old_len:nat) (i j:nat)
  : Lemma
    (requires i <= j /\ j <= old_len /\ old_len <= B.length s_old /\
              B.length s_old == B.length s_new /\
              Seq.equal (Seq.slice s_old 0 old_len) (Seq.slice s_new 0 old_len))
    (ensures Seq.slice s_old i j == Seq.slice s_new i j)
  = Seq.slice_slice s_old 0 old_len i j;
    Seq.slice_slice s_new 0 old_len i j;
    Seq.lemma_eq_elim (Seq.slice s_old 0 old_len) (Seq.slice s_new 0 old_len)

(* Invariant extension: if [chain] matches the [count]-entry layout in [s_old]
   ending at byte [old_len], and [s_new] (same length) preserves the prefix
   [0, old_len) while [offsets.[count] == old_len] points at a fresh blob of
   length [lens.[count]] sitting in [s_new] just past [old_len], then appending
   that blob extends the match to [count+1] entries ending at
   [old_len + lens.[count]]. *)
let rec certificate_chain_matches_snoc
  (s_old s_new:B.bytes)
  (offsets lens:Seq.seq SZ.t)
  (count:nat)
  (chain:list B.bytes)
  (old_len:nat)
  : Lemma
    (requires
      IM.certificate_chain_matches s_old old_len offsets lens count chain /\
      B.length s_old == B.length s_new /\
      count < Seq.length offsets /\ count < Seq.length lens /\
      SZ.v (Seq.index offsets count) == old_len /\
      old_len + SZ.v (Seq.index lens count) <= B.length s_new /\
      Seq.equal (Seq.slice s_old 0 old_len) (Seq.slice s_new 0 old_len))
    (ensures
      IM.certificate_chain_matches s_new (old_len + SZ.v (Seq.index lens count))
        offsets lens (count + 1)
        (L.append chain
          [Seq.slice s_new old_len (old_len + SZ.v (Seq.index lens count))]))
    (decreases count)
  =
  match chain with
  | [] -> ()
  | cert :: rest ->
    if count = 0 then ()
    else begin
      let offset0 = SZ.v (Seq.index offsets 0) in
      let certlen0 = SZ.v (Seq.index lens 0) in
      (* the head cert lives in the preserved prefix, so it still matches s_new *)
      lemma_slice_agree s_old s_new old_len offset0 (offset0 + certlen0);
      (* offsets.[count] / lens.[count] are the head of the shifted seqs *)
      Seq.lemma_index_slice offsets 1 (Seq.length offsets) (count - 1);
      Seq.lemma_index_slice lens 1 (Seq.length lens) (count - 1);
      certificate_chain_matches_snoc s_old s_new
        (Seq.slice offsets 1 (Seq.length offsets))
        (Seq.slice lens 1 (Seq.length lens))
        (count - 1) rest old_len
    end

(* [certificate_chain_matches] only inspects offsets/lens indices in [0, count);
   replacing those seqs by ones that agree on that prefix preserves the match.
   Used to "frame past" the in-place write of the [count]-th [(offset,len)] pair
   into the offsets/lens Vecs (which leaves indices < count untouched). *)
let rec certificate_chain_matches_frame
  (s:B.bytes)
  (len:nat)
  (offsets lens offsets' lens':Seq.seq SZ.t)
  (count:nat)
  (chain:list B.bytes)
  : Lemma
    (requires
      IM.certificate_chain_matches s len offsets lens count chain /\
      count <= Seq.length offsets /\ count <= Seq.length lens /\
      count <= Seq.length offsets' /\ count <= Seq.length lens' /\
      (forall (k:nat). k < count ==> Seq.index offsets' k == Seq.index offsets k) /\
      (forall (k:nat). k < count ==> Seq.index lens' k == Seq.index lens k))
    (ensures IM.certificate_chain_matches s len offsets' lens' count chain)
    (decreases count)
  =
  match chain with
  | [] -> ()
  | cert :: rest ->
    if count = 0 then ()
    else begin
      (* head indices agree *)
      assert (Seq.index offsets' 0 == Seq.index offsets 0);
      assert (Seq.index lens' 0 == Seq.index lens 0);
      (* the shifted seqs agree on [0, count-1) *)
      introduce forall (k:nat). k < count - 1 ==>
        Seq.index (Seq.slice offsets' 1 (Seq.length offsets')) k ==
        Seq.index (Seq.slice offsets 1 (Seq.length offsets)) k
      with introduce _ ==> _
      with (
        Seq.lemma_index_slice offsets' 1 (Seq.length offsets') k;
        Seq.lemma_index_slice offsets 1 (Seq.length offsets) k
      );
      introduce forall (k:nat). k < count - 1 ==>
        Seq.index (Seq.slice lens' 1 (Seq.length lens')) k ==
        Seq.index (Seq.slice lens 1 (Seq.length lens)) k
      with introduce _ ==> _
      with (
        Seq.lemma_index_slice lens' 1 (Seq.length lens') k;
        Seq.lemma_index_slice lens 1 (Seq.length lens) k
      );
      certificate_chain_matches_frame s len
        (Seq.slice offsets 1 (Seq.length offsets))
        (Seq.slice lens 1 (Seq.length lens))
        (Seq.slice offsets' 1 (Seq.length offsets'))
        (Seq.slice lens' 1 (Seq.length lens'))
        (count - 1) rest
    end

(* Combined frame + snoc: extend a [count]-entry match by writing the
   [count]-th [(offset,len)] pair (the new offsets'/lens' agree with the old on
   the [0, count) prefix) and copying the new blob just past [old_len]. *)
let certificate_chain_matches_extend
  (s_old s_new:B.bytes)
  (offsets_old lens_old offsets_new lens_new:Seq.seq SZ.t)
  (count:nat)
  (chain:list B.bytes)
  (old_len:nat)
  : Lemma
    (requires
      IM.certificate_chain_matches s_old old_len offsets_old lens_old count chain /\
      B.length s_old == B.length s_new /\
      count <= Seq.length offsets_old /\ count <= Seq.length lens_old /\
      count < Seq.length offsets_new /\ count < Seq.length lens_new /\
      (forall (k:nat). k < count ==> Seq.index offsets_new k == Seq.index offsets_old k) /\
      (forall (k:nat). k < count ==> Seq.index lens_new k == Seq.index lens_old k) /\
      SZ.v (Seq.index offsets_new count) == old_len /\
      old_len + SZ.v (Seq.index lens_new count) <= B.length s_new /\
      Seq.equal (Seq.slice s_old 0 old_len) (Seq.slice s_new 0 old_len))
    (ensures
      IM.certificate_chain_matches s_new (old_len + SZ.v (Seq.index lens_new count))
        offsets_new lens_new (count + 1)
        (L.append chain
          [Seq.slice s_new old_len (old_len + SZ.v (Seq.index lens_new count))]))
  =
  certificate_chain_matches_frame s_old old_len offsets_old lens_old
    offsets_new lens_new count chain;
  certificate_chain_matches_snoc s_old s_new offsets_new lens_new count chain old_len
