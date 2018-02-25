(**
Stateful, agile, length-hiding authenticated encryption with additional data
Implemented by appending a fragment sequence number to the additional data of
the underlying LHAE scheme
*)
module StatefulLHAE
module HS = FStar.HyperStack //Added automatically
module HST = FStar.HyperStack.ST //Added automatically

open FStar.Heap
open FStar.HyperStack
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.Bytes

open Mem
open TLSConstants
open TLSInfo
open AEAD_GCM
open StatefulPlain

module Range = Range

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

// TODO: TEMPORARY, until we add back LHAE
type id = AEAD_GCM.id

let alg (i:id) = AEAD_GCM.alg i

type cipher (i:id) = StatefulPlain.cipher i

(* decrypted plaintexts, within a range computed from the cipher length *)
type dplain (i:id) (ad:adata i) (c:cipher i) =
  StatefulPlain.plain i ad (Range.cipherRangeClass i (length c))

type state (i:id) (rw:rw) =
  AEAD_GCM.state i rw

let region #i #rw s = AEAD_GCM.State?.region #i #rw s

noextract
let log_region #i #rw s = AEAD_GCM.State?.log_region #i #rw s

let log #i #rw s = AEAD_GCM.State?.log #i #rw s

let counter #i #rw s = AEAD_GCM.State?.counter #i #rw s

type reader i = state i Reader
type writer i = state i Writer

val gen: parent:rgn -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))
let gen p i = AEAD_GCM.gen p i

val genReader: parent:rgn -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 ->
    HS.disjoint parent w.region /\
    HS.disjoint parent (AEADProvider.region w.aead)))
  (ensures  (fun h0 (r:reader i) h1 ->
    True //TODO
    ))
let genReader p #i w = AEAD_GCM.genReader p #i w

let coerce parent i kv iv = AEAD_GCM.coerce parent i kv iv
let leak (#i:id{~(authId i)}) (#role:rw) state = AEAD_GCM.leak #i #role state

(*------------------------------------------------------------------*)
#set-options "--z3rlimit 100 --max_ifuel 1 --initial_ifuel 0 --max_fuel 1 --initial_fuel 0"
val encrypt: #i:id -> e:writer i -> ad:adata i
  -> r:Range.range{fst r = snd r /\ snd r <= max_TLSPlaintext_fragment_length}
  -> p:plain i ad r
  -> ST (cipher i)
     (requires (fun h0 ->
       HS.disjoint e.region (AEADProvider.log_region e.aead) /\
       sel h0 (ctr e.counter) < max_ctr (alg i)))
     (ensures  (fun h0 c h1 ->
       modifies (Set.as_set [e.log_region; AEADProvider.log_region e.aead]) h0 h1
       /\ h1 `HS.contains` (ctr e.counter)
       /\ sel h1 (ctr e.counter) === sel h0 (ctr e.counter) + 1
       /\ length c = Range.targetLength i r
       /\ (authId i ==>
	     (let log = ilog e.log in
	      let ilog = sel h0 log in
	      let seqn = sel h0 (ctr e.counter) in
        lemma_repr_bytes_values seqn;
	      let ad' = LHAEPlain.makeAD i seqn ad in
	      let ent = Entry c ad' p in
	      let n   = Seq.length ilog in
	      h1 `HS.contains` log
        /\ witnessed (at_least n ent log)
	      /\ sel h1 log == snoc ilog ent))))

let encrypt #i e ad r p =
  let seqn = HST.op_Bang (ctr e.counter) in
  lemma_repr_bytes_values seqn;
  let ad' = LHAEPlain.makeAD i seqn ad in
  AEAD_GCM.encrypt #i e ad' r p


(*------------------------------------------------------------------*)
val decrypt: #i:id -> d:reader i -> ad:adata i -> c:cipher i
  -> ST (option (dplain i ad c))
  (requires (fun h0 -> sel h0 (ctr d.counter) < max_ctr (alg i)))
  (ensures  (fun h0 res h1 ->
     let j = sel h0 (ctr d.counter) in
     (authId i ==>
       (let log = sel h0 (ilog d.log) in
	let seqn = sel h0 (ctr d.counter) in
        lemma_repr_bytes_values seqn;
        let ad' = LHAEPlain.makeAD i seqn ad in
       if j < Seq.length log && matches c ad' (Seq.index log j)
       then res = Some (Entry?.p (Seq.index log j))
       else res = None))
    /\ (
       match res with
       | None -> modifies Set.empty h0 h1
       | _    -> modifies_one d.region h0 h1
                /\ HS.modifies_ref d.region (Set.singleton (HS.as_addr (ctr d.counter))) h0 h1
	        /\ sel h1 (ctr d.counter) === j + 1)))
let decrypt #i d ad c =
  let seqn = HST.op_Bang (ctr d.counter) in
  lemma_repr_bytes_values seqn;
  let ad' = LHAEPlain.makeAD i seqn ad in
  AEAD_GCM.decrypt d ad' c


(*
   TODO?
   - calling gen/coerce adds i to the log of existing keys;
     gen can only be called when i is not yet in the log;
     we get this precondition from the freshness of the local nonce in i
*)
