module StreamDeltas
open Platform.Bytes
open Platform.Error

open FStar.HyperHeap
open TLSConstants
open TLSInfo

module HH   = FStar.HyperHeap
module MR   = FStar.Monotonic.RRef
module S    = StAE
module MS   = MonotoneSeq
module C    = Content
module DS   = DataStream
module SeqP = FStar.SeqProperties

let deltas i = Seq.seq (DS.delta i) //not yet handling the well-formedness condition of final deltas

let singleton (x:'a) : Tot (Seq.seq 'a) = Seq.create 1 x

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

private type id = i:id{~(is_PlaintextID i)}

val project_one_frag: #i:id -> f:C.fragment i -> Tot (Seq.seq (DS.delta i))
let project_one_frag #i = function
    | C.CT_Data rg d -> 
      let d : DS.pre_fragment i = d in //A widening coercion as a proof hint, unpacking (d:fragment i (frange i)) to a pre_fr
      singleton (DataStream.Data d)
    | C.CT_Alert _ ad -> singleton (DataStream.Alert ad)
    | _ -> Seq.createEmpty                 // other fragments are internal to TLS

val project_deltas: #i:id -> fs:S.frags i -> Tot (deltas i)
let project_deltas #i fs = MS.collect project_one_frag fs

val stream_deltas: #i:id -> #rw:rw -> s:StAE.state i rw{authId i} -> HH.t -> GTot (deltas i)
let stream_deltas #i #rw s h = project_deltas (StAE.fragments s h)

let stream_deltas_snoc (i:id) (frags:StAE.frags i) (f:Content.fragment i)
  : Lemma (project_deltas (SeqP.snoc frags f) == Seq.append (project_deltas frags) (project_one_frag f))
  = MS.collect_snoc project_one_frag frags f

//A predicate stating the deltas of s always as ds as a prefix
let deltas_prefix (#i:id) (#rw:rw) (s:S.state i rw{authId i}) (ds:deltas i) (h:HH.t) 
  : GTot Type0 
  = MS.grows ds (project_deltas (S.fragments s h))

val project_fragment_deltas: #i:id -> #rw:rw -> s:S.state i rw -> fs:S.frags i
		  -> Lemma (authId i /\ MR.witnessed (S.fragments_prefix s fs)
			   ==> MR.witnessed (deltas_prefix s (project_deltas fs)))

let project_fragment_deltas #i #rw s fs =
  if authId i 
  then let j : i:id{authId i} = i in
       let s  : S.state j rw = s in
       let fs : S.frags j = fs in
       let aux : h:HH.t -> Lemma (S.fragments_prefix s fs h
			    ==> deltas_prefix s (project_deltas fs) h) =
	  fun h -> MS.collect_grows project_one_frag fs (S.fragments s h) in
       let _ = qintro aux in
       weaken_witness (S.fragments_prefix s fs) (deltas_prefix s (project_deltas fs))
  else ()
  
(*   else () *)


(* val project_fragment_deltas: #i:id -> #rw:rw -> s:S.state i rw{authId i} -> fs:S.frags i *)
(* 		  -> Lemma (requires (MR.witnessed (S.fragments_prefix s fs))) *)
(* 		          (ensures (MR.witnessed (deltas_prefix s (project_deltas fs)))) *)
(* let project_fragment_deltas #i #rw s fs = *)
(*   let aux : h:HH.t -> Lemma (S.fragments_prefix s fs h *)
(* 			    ==> deltas_prefix s (project_deltas fs) h) = *)
(* 	  fun h -> MS.collect_grows project_one_frag fs (S.fragments s h) in *)
(*   qintro aux; *)
(*   MR.weaken_witness (S.fragments_prefix s fs) (deltas_prefix s (project_deltas fs)) *)

