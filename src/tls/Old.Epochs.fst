(**
This modules implements the mutable state for the successive StAE epochs which is used by TLS.
Its separation from Handshake and coding is somewhat arbitrary.
An elaboration would ensure that keys in old epochs are erased.
(i.e. we only keep old epoch AE logs for specifying authentication)
*)
module Old.Epochs
module HST = FStar.HyperStack.ST //Added automatically

open FStar.Heap
open FStar.Seq // DO NOT move further below, it would shadow `FStar.HyperStack.mem`
open FStar.HyperStack
open FStar.Monotonic.Seq
open FStar.Bytes

open TLS.Result
open TLSInfo
open TLSConstants
module Range = Range
open Range
open StAE
//open Negotiation
open Mem

module ST = FStar.HyperStack.ST 
module HS = FStar.HyperStack
module MS = FStar.Monotonic.Seq
module Secret = Old.KeySchedule

#set-options "--admit_smt_queries true"

let epoch_region_inv'
  (#i:id)
  (hs_rgn:rgn)
  (r:reader (peerId i))
  (w:writer i)
= epoch_region_inv hs_rgn r w

let epochs_inv' (#r:rgn) (#n:random) (es: seq (epoch r n)) = epochs_inv es

let reveal_epochs_inv' (u:unit)
  : Lemma (forall (r:rgn) (#n:random) (es:seq (epoch r n)). {:pattern (epochs_inv' es)}
         epochs_inv' es
         <==>
         epochs_inv es)
  = ()

#reset-options "--using_facts_from FStar --using_facts_from Prims --using_facts_from Epochs --using_facts_from Parse --admit_smt_queries true"

let alloc_log_and_ctrs #a #p r =
  let init = Seq.empty in
  let is = alloc_mref_iseq p r init in
  HST.mr_witness is (int_at_most (-1) is);
  let c1 : epoch_ctr #a #p r is = HST.ralloc r (-1) in
  let c2 : epoch_ctr #a #p r is = HST.ralloc r (-1) in
  (| is, c1, c2 |)

// #reset-options

let incr_epoch_ctr #a #p #r #is ctr =
  HST.recall ctr;
  let cur = HST.op_Bang ctr in
  MS.int_at_most_is_stable is (cur + 1);
  HST.mr_witness is (int_at_most (cur + 1) is);
  HST.op_Colon_Equals ctr (cur + 1)

let create (r:rgn) (n:random) =
  let (| esref, c1, c2 |) = alloc_log_and_ctrs #(epoch r n) #(epochs_inv #r #n) r in
  let xkr = alloc_mref_iseq (fun s -> Seq.length s <= 2) r Seq.empty in
  assume False; //17-06-30 TODO restore framing with extra field
  MkEpochs esref c1 c2 xkr

let add_epoch #r #n (MkEpochs es _ _ _) e = MS.i_write_at_end es e
let recordInstanceToEpoch #hs_rgn #n hs ri =
  let Secret.StAEInstance #i rd wr pn = ri in
  assume(nonce_of_id i = n); // ADL: KS will need to provove this
  assume(epoch_region_inv' hs_rgn rd wr);
  Epoch #hs_rgn #n #i hs rd wr pn
