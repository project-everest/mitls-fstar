module StatefulLHAE

// Stateful, agile, length-hiding authenticated encryption with additional data
// Implemented by appending a fragment sequence number to the additional data of
// the underlying LHAE scheme

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.Monotonic.RRef
open FStar.Monotonic.Seq

open Platform.Bytes

open TLSConstants
open TLSInfo
open Range
open AEAD_GCM
open StatefulPlain

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

// TODO: TEMPORARY, until we add back LHAE
type id = AEAD_GCM.id

let alg (i:id) = AEAD_GCM.alg i

type cipher (i:id) = StatefulPlain.cipher i

(* decrypted plaintexts, within a range computed from the cipher length *)
type dplain (i:id) (ad:adata i) (c:cipher i) =
  StatefulPlain.plain i ad (cipherRangeClass i (length c))

type state (i:id) (rw:rw) =
  AEAD_GCM.state i rw

let region = AEAD_GCM.State?.region

let log_region = AEAD_GCM.State?.log_region

let log = AEAD_GCM.State?.log

let counter = AEAD_GCM.State?.counter

type reader i = state i Reader
type writer i = state i Writer


(*------------------------------------------------------------------*)
abstract val gen: parent:rid -> i:id -> ST (writer i)
  (requires (fun h -> True))
  (ensures  (genPost parent))
let gen parent i =
  AEAD_GCM.gen parent i

val genReader: parent:rid -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 -> HyperHeap.disjoint parent w.region))
  (ensures  (fun h0 (r:reader i) h1 ->
               modifies Set.empty h0 h1 /\
               r.log_region = w.region /\
               extends r.region parent /\
	       color r.region = color parent /\
               stronger_fresh_region r.region h0 h1 /\
               eq2 #(log_ref w.region i) w.log r.log /\
	       m_contains (ctr r.counter) h1 /\
	       m_sel h1 (ctr r.counter) === 0))
let genReader parent #i w =
  AEAD_GCM.genReader parent #i w


(*------------------------------------------------------------------*)
// Coerce an instance with index i in a fresh sub-region of parent
// (coerced readers can then be obtained by calling genReader)
// TODO: replace (kv,iv) by lbytes
val coerce: parent:rid -> i:id{~(authId i)} -> kv:key i -> iv:iv i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))
let coerce parent i kv iv =
  AEAD_GCM.coerce parent i kv iv


(*------------------------------------------------------------------*)
abstract val leak: #i:id{~(authId i)} -> #role:rw -> state i role -> ST (AEAD_GCM.key i * AEAD_GCM.iv i)
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> modifies Set.empty h0 h1))
let leak #i #role s =
  AEAD_GCM.leak s


(*------------------------------------------------------------------*)
val encrypt: #i:id -> e:writer i -> ad:adata i
  -> r:range{fst r = snd r /\ snd r <= max_TLSPlaintext_fragment_length}
  -> p:plain i ad r
  -> ST (cipher i)
       (requires (fun h0 -> m_sel h0 (ctr e.counter) < max_ctr (alg i)))
       (ensures  (fun h0 c h1 ->
           modifies_one e.region h0 h1
 	 /\ m_contains (ctr e.counter) h1
	 /\ m_sel h1 (ctr e.counter) === m_sel h0 (ctr e.counter) + 1
	 /\ length c = Range.targetLength i r
	 /\ (authId i ==>
	     (let log = ilog e.log in
	      let ilog = m_sel h0 log in
	      let seqn = m_sel h0 (ctr e.counter) in
              lemma_repr_bytes_values seqn;
	      let ad' = LHAEPlain.makeAD i seqn ad in
	      let ent = Entry c ad' p in
	      let n   = Seq.length ilog in
	        m_contains log h1
              /\ witnessed (at_least n ent log)
	      /\ m_sel h1 log == snoc ilog ent))))
let encrypt #i e ad r p =
  let seqn = m_read (ctr e.counter) in
  lemma_repr_bytes_values seqn;
  let ad' = LHAEPlain.makeAD i seqn ad in
  AEAD_GCM.encrypt #i e ad' r p


(*------------------------------------------------------------------*)
val decrypt: #i:id -> d:reader i -> ad:adata i -> c:cipher i
  -> ST (option (dplain i ad c))
  (requires (fun h0 -> m_sel h0 (ctr d.counter) < max_ctr (alg i)))
  (ensures  (fun h0 res h1 ->
     let j = m_sel h0 (ctr d.counter) in
     (authId i ==>
       (let log = m_sel h0 (ilog d.log) in
	let seqn = m_sel h0 (ctr d.counter) in
        lemma_repr_bytes_values seqn;
        let ad' = LHAEPlain.makeAD i seqn ad in
       if j < Seq.length log && matches c ad' (Seq.index log j)
       then res = Some (Entry?.p (Seq.index log j))
       else res = None))
    /\ (
       let ctr_counter_as_hsref = as_hsref (ctr d.counter) in
       match res with
       | None -> modifies Set.empty h0 h1
       | _    -> modifies_one d.region h0 h1
                /\ modifies_rref d.region !{as_ref ctr_counter_as_hsref} h0.h h1.h
	        /\ m_sel h1 (ctr d.counter) === j + 1)))
let decrypt #i d ad c =
  let seqn = m_read (ctr d.counter) in
  lemma_repr_bytes_values seqn;
  let ad' = LHAEPlain.makeAD i seqn ad in
  AEAD_GCM.decrypt d ad' c


(*
   TODO?
   - calling gen/coerce adds i to the log of existing keys;
     gen can only be called when i is not yet in the log;
     we get this precondition from the freshness of the local nonce in i
*)
