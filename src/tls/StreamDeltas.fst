module StreamDeltas
open FStar.Bytes
open FStar.Error

open FStar.HyperHeap
open FStar.HyperStack
open TLSConstants
open TLSInfo

module HH   = FStar.HyperHeap
module HS   = FStar.HyperStack
module MR   = FStar.Monotonic.RRef
module MS   = FStar.Monotonic.Seq
module S    = StAE
module C    = Content
module DS   = DataStream

let deltas i = Seq.seq (DS.delta i) //not yet handling the well-formedness condition of final deltas

let singleton (x:'a) : Tot (Seq.seq 'a) = Seq.create 1 x

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

private type id = i:id{~(PlaintextID? i)}

val project_one_frag: #i:id -> f:C.fragment i -> Tot (Seq.seq (DS.delta i))
let project_one_frag #i = function
    | C.CT_Data rg d -> 
      let d : DS.pre_fragment i = d in //A widening coercion as a proof hint, unpacking (d:fragment i (frange i)) to a pre_fr
      singleton (DataStream.Data d)
    | C.CT_Alert _ ad -> singleton (DataStream.Alert ad)
    | _ -> Seq.createEmpty                 // other fragments are internal to TLS

val project_deltas: #i:id -> fs:S.frags i -> Tot (deltas i)
let project_deltas #i fs = MS.collect project_one_frag fs

val stream_deltas: #i:id -> #rw:rw -> s:StAE.state i rw{authId i} -> mem -> GTot (deltas i)
let stream_deltas #i #rw s h = project_deltas (StAE.fragments s h)

let stream_deltas_snoc (i:id) (frags:StAE.frags i) (f:Content.fragment i)
  : Lemma (project_deltas (Seq.snoc frags f) == Seq.append (project_deltas frags) (project_one_frag f))
  = MS.collect_snoc project_one_frag frags f

//A predicate stating the deltas of s always as ds as a prefix
let deltas_prefix (#i:id) (#rw:rw) (s:S.state i rw{authId i}) (ds:deltas i) (h:mem)
  : GTot Type0 
  = MS.grows ds (project_deltas (S.fragments s h))

val project_fragment_deltas: #i:id -> #rw:rw -> s:S.state i rw -> fs:S.frags i
		  -> Lemma (authId i /\ S.witnessed_ilog s (S.fragments_prefix s fs)
			   ==> S.witnessed_ilog s (deltas_prefix s (project_deltas fs)))
let project_fragment_deltas #i #rw s fs =
  if authId i 
  then let j : i:id{authId i} = i in //re-label for better implicit arg inference below
       let s  : S.state j rw = s in
       let fs : S.frags j = fs in
       let aux : h:mem -> Lemma (S.fragments_prefix s fs h
			    ==> deltas_prefix s (project_deltas fs) h) =
	  fun h -> MS.collect_grows project_one_frag fs (S.fragments s h) in
       let _ = FStar.Classical.forall_intro aux in
       match s with
       | S.Stream u stream -> 
         MR.weaken_witness
           (StreamAE.ilog (StreamAE.State?.log stream))
           (S.fragments_prefix s fs)
           (deltas_prefix s (project_deltas fs))
       | S.StLHAE u stream ->
         MR.weaken_witness
           (AEAD_GCM.ilog (AEAD_GCM.State?.log stream))
           (S.fragments_prefix s fs)
           (deltas_prefix s (project_deltas fs))
  else ()

let stream_deltas_snoc2 (#i:id) (#rw:rw) (s:StAE.state i rw) (h0:mem) (h1:mem) (f:Content.fragment i)
  : Lemma (authId i /\ StAE.fragments s h1 == Seq.snoc (StAE.fragments s h0) f
	   ==> stream_deltas s h1 == Seq.append (stream_deltas s h0) (project_one_frag f))
  = if authId i then stream_deltas_snoc i (StAE.fragments s h0) f else ()

(********************************************************************************)
(* A wrapper for StAE, providing a view in terms of both fragments and deltas   *)
(********************************************************************************)
val encrypt: #i:id -> wr:StAE.writer i -> f:Content.fragment i -> ST (Content.encrypted f)
  (requires (fun h -> StAE.incrementable wr h))
  (ensures (fun h0 c h1 -> 
	      modifies_one (StAE.region wr) h0 h1
	      /\ StAE.seqnT wr h1 = StAE.seqnT wr h0 + 1
	      /\ (authId i ==>
	 	  StAE.fragments wr h1 == Seq.snoc (StAE.fragments wr h0) f
		  /\ StAE.witnessed_ilog wr (StAE.fragments_prefix wr (StAE.fragments wr h1))
		  /\ stream_deltas wr h1 == Seq.append (stream_deltas wr h0) (project_one_frag f)
 		  /\ StAE.witnessed_ilog wr (deltas_prefix wr (stream_deltas wr h1)))))
let encrypt #i wr f = 
  let h0 = get () in
  let res = StAE.encrypt wr f in 
  let h1 = get () in
  stream_deltas_snoc2 wr h0 h1 f;
  if authId i
  then project_fragment_deltas wr (StAE.fragments wr h1);
  res

