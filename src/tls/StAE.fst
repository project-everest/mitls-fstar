(*--build-config
options:--use_hints --fstar_home ../../../FStar --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/examples/low-level/crypto/real --include ../../../FStar/examples/low-level/crypto/spartan --include ../../../FStar/examples/low-level/LowCProvider/fst --include ../../../FStar/examples/low-level/crypto --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ideal-flags;
--*)
module StAE

// Authenticated encryptions of streams of TLS fragments (from Content)
// multiplexing StatefulLHAE and StreamAE with (some) length hiding
// (for now, under-specifying ciphertexts lengths and values)

open FStar.HyperHeap
open FStar.HyperStack
open Platform.Bytes

open TLSConstants
open TLSInfo

module HH   = FStar.HyperHeap
module HS   = FStar.HyperStack
module MR   = FStar.Monotonic.RRef
module MS   = FStar.Monotonic.Seq
module C    = Content

module Stream = StreamAE
module StLHAE = StatefulLHAE

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

(* various utilities related to lengths of ciphers and fragments *)

#set-options "--z3rlimit 100"
// CONCRETE KEY MATERIALS, for leaking & coercing.
// (each implementation splits it into encryption keys, IVs, MAC keys, etc)
// ADL: this can now be factored going through the common AEADProvider interface
let aeKeySize (i:stae_id) =
  if is_stream i
  then
    CoreCrypto.aeadKeySize (Stream.alg i) +
    AEADProvider.iv_length i
  else
    CoreCrypto.aeadKeySize (AEAD?._0 (aeAlg_of_id i)) +
    AEADProvider.salt_length i

(* `state i rw`, a sum to cover StreamAE (1.3) and StatefulLHAE (1.2) *)

noeq type state' (i:id) (rw:rw) =
  | Stream: u:unit{is_stream i} -> Stream.state i rw -> state' i rw
  | StLHAE: u:unit{is_stlhae i} -> StLHAE.state i rw -> state' i rw
let state = state' // silly

private let stream_state (#i:id{is_stream i}) (#rw:rw) (s:state i rw)
  : Tot (Stream.state i rw)
  = let Stream _ s = s in s

private let stlhae_state (#i:id{is_stlhae i}) (#rw:rw) (s:state i rw)
  : Tot (StatefulLHAE.state i rw)
  = let StLHAE _ s = s in s

let region (#i:id) (#rw:rw) (s:state i rw): Tot rgn =
  match s with
  | Stream _ x -> Stream.State?.region x
  | StLHAE _ x -> StLHAE.region x

let log_region (#i:id) (#rw:rw) (s:state i rw): Tot rgn =
  match s with
  | Stream _ s -> Stream.State?.log_region s
  | StLHAE _ s -> AEAD_GCM.State?.log_region s

// our view to AE's ideal log (when idealized, ignoring ciphers) and counter
// TODO: write down their joint monotonic specification: both are monotonic,
// and seqn = length log when ideal

////////////////////////////////////////////////////////////////////////////////
//Logs of fragments, defined as projections on the underlying entry logs
////////////////////////////////////////////////////////////////////////////////
// TODO: consider adding constraint on terminator fragments

let ideal_log (r:rgn) (i:id) =
  if is_stream i then
    Stream.ideal_log r i
  else if is_stlhae i then
    AEAD_GCM.ideal_log r i
  else False

let ilog (#i:id) (#rw:rw) (s:state i rw{authId i}): Tot (ideal_log (log_region s) i) =
  match s with
  | Stream u s -> Stream.ilog (Stream.State?.log s)
  | StLHAE u s -> AEAD_GCM.ilog (AEAD_GCM.State?.log s)

let entry (i:id) =
   if is_stream i then
     Stream.entry i
   else if is_stlhae i then
     AEAD_GCM.entry i
   else False

let ptext (#i:id) (ent:entry i): Tot (C.fragment i) =
  if is_stream i then
    Stream.Entry?.p #i ent
  else
    AEAD_GCM.Entry?.p #i ent

//A projection of fragments from Stream.entries
let fragments (#i:id) (#rw:rw) (s:state i rw{authId i}) (h:mem): GTot (frags i) =
  let entries = MR.m_sel #(log_region s) #_ #MS.grows h (ilog s) in
  MS.map ptext entries

val lemma_fragments_snoc_commutes: #i:id -> w:writer i{authId i}
  -> h0:mem -> h1:mem -> e:entry i
  -> Lemma (let log = ilog w in
           MR.m_sel #(log_region w) #_ #MS.grows h1 log ==
	   Seq.snoc (MR.m_sel #(log_region w) #_ #MS.grows h0 log) e ==>
	   fragments w h1 == Seq.snoc (fragments w h0) (ptext e))
let lemma_fragments_snoc_commutes #i w h0 h1 e =
  let log = ilog w in
  MS.map_snoc ptext (MR.m_sel #(log_region w) #_ #MS.grows h0 log) e

//A predicate stating that the fragments have fs as a prefix
let fragments_prefix (#i:id) (#rw:rw) (w:state i rw{authId i}) (fs:frags i) (h:mem) : GTot Type0 =
  MS.map_prefix #_ #_ #(log_region w) (ilog w) ptext fs h

//In order to witness fragments_prefix s fs, we need to prove that it is stable
val fragments_prefix_stable: #i:id -> #rw:rw
  -> w:state i rw{authId i} -> h:mem
  -> Lemma (let fs = fragments w h in
	   MS.grows fs fs
	   /\ MR.stable_on_t #(log_region w) #_ #(MS.grows #(entry i)) (ilog w)
	     (fragments_prefix w fs))
let fragments_prefix_stable #i #rw w h =
  let fs = fragments w h in
  let log = ilog w in
  MS.seq_extension_reflexive fs;
  MS.map_prefix_stable #_ #_ #(log_region w) log ptext fs


//
// (* projecting sequence numbers *) 
//

let seqnT (#i:id) (#rw:rw) (s:state i rw) h : GTot nat =
  match s with
  | Stream _ s -> MR.m_sel h (Stream.ctr (Stream.State?.counter s))
  | StLHAE _ s -> MR.m_sel h (AEAD_GCM.ctr (StLHAE.counter s))


// Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

// We generate first the writer, then the reader (possibly several of them)


//
// (* framing *) 
//
val frame_fragments : #i:id -> #rw:rw -> st:state i rw -> h0:mem -> h1:mem -> s:Set.set rid
  -> Lemma
    (requires modifies s h0 h1
	      /\ Map.contains h0.h (log_region st)
	      /\ not (Set.mem (log_region st) s))
    (ensures authId i ==> fragments st h0 == fragments st h1)
let frame_fragments #i #rw st h0 h1 s = ()

#set-options "--z3rlimit 100 --max_ifuel 1 --initial_ifuel 3 --max_fuel 3 --initial_fuel 3"
val frame_seqnT : #i:id -> #rw:rw -> st:state i rw -> h0:mem -> h1:mem -> s:Set.set rid
	       -> Lemma
    (requires modifies s h0 h1
    	  /\ Map.contains h0.h (region st)
	      /\ not (Set.mem (region st) s))
    (ensures seqnT st h0 = seqnT st h1)
let frame_seqnT #i #rw st h0 h1 s = ()

val frame_seqT_auto: i:id -> rw:rw -> s:state i rw -> h0:mem -> h1:mem ->
  Lemma (requires   HH.equal_on (Set.singleton (region s)) h0.h h1.h
		  /\ Map.contains h0.h (region s))
        (ensures seqnT s h0 = seqnT s h1)
	[SMTPat (seqnT s h0);
	 SMTPat (seqnT s h1)]
//	 SMTPatT (trigger_frame h1)]
let frame_seqT_auto i rw s h0 h1 = ()

val frame_fragments_auto: i:id{authId i} -> rw:rw -> s:state i rw -> h0:mem -> h1:mem ->
  Lemma (requires    HH.equal_on (Set.singleton (log_region s)) h0.h h1.h
		  /\ Map.contains h0.h (log_region s))
        (ensures fragments s h0 == fragments s h1)
	[SMTPat (fragments s h0);
	 SMTPat (fragments s h1)]
	 (* SMTPatT (trigger_frame h1)] *)
let frame_fragments_auto i rw s h0 h1 = ()

(*
////////////////////////////////////////////////////////////////////////////////
//Experimenting with reads clauses: probably unnecessary
////////////////////////////////////////////////////////////////////////////////
let reads (s:Set.set rid) (a:Type) =
    f: (h:mem -> GTot a){forall h1 h2. (HH.equal_on s h1.h h2.h /\ Set.subset s (Map.domain h1.h))
				  ==> f h1 == f h2}

val fragments' : #i:id -> #rw:rw -> s:state i rw{ authId i } -> Tot (reads (Set.singleton (log_region s)) (frags i))
let fragments' #i #rw s = fragments s
*)

(*------------------------------------------------------------------*)

// Generate a fresh instance with index i in a fresh sub-region
#set-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let gen parent i =
  if is_stream i then
    Stream () (Stream.gen parent i)
  else
    StLHAE () (StLHAE.gen parent i)

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let genReader parent #i w =
  match w with
  | Stream _ w ->
      lemma_ID13 i;
      assume(StreamAE.(HyperHeap.disjoint parent (AEADProvider.region #i w.aead)));
      Stream () (Stream.genReader parent #i w)
  | StLHAE _ w ->
      lemma_ID12 i;
      assume(AEAD_GCM.(HyperHeap.disjoint parent (AEADProvider.region #i w.aead)));
      StLHAE () (StLHAE.genReader parent #i w)


(* coerce & leak *)

#set-options "--z3rlimit 100"
let coerce parent i kiv =
  if is_stream i then
    let kv,iv = Platform.Bytes.split kiv (CoreCrypto.aeadKeySize (Stream.alg i)) in
    Stream () (Stream.coerce parent i kv iv)
  else
    let kv,iv = Platform.Bytes.split kiv (CoreCrypto.aeadKeySize (StLHAE.alg i)) in
    StLHAE () (StLHAE.coerce parent i kv iv)

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 2 --max_ifuel 2"
let leak #i #role s =
  match s with
  | Stream _ s -> let kv,iv = Stream.leak s in kv @| iv
  | StLHAE _ s -> let kv,iv = StLHAE.leak s in kv @| iv


// ADL Jan 19. Made some progress on encrypt but need to merge lowlevel now
#set-options "--lax"

(* encryption, recorded in the log; safe instances are idealized *) 

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 3 --max_ifuel 3"
let encrypt #i e f =
  match e with
  | StLHAE u s ->
    begin
    let h0 = ST.get() in
    let ct,rg = C.ct_rg i f in
    let ad = StatefulPlain.makeAD i ct in
    let seqn = MR.m_read (AEAD_GCM.ctr (StLHAE.counter s)) in
    let c = StLHAE.encrypt s ad rg f in
    let h1 = ST.get() in
    if authId i then
      begin
      lemma_repr_bytes_values seqn;
      let ad' = LHAEPlain.makeAD i seqn ad in
      let ent = AEAD_GCM.Entry c ad' f in
      lemma_fragments_snoc_commutes e h0 h1 ent;
      fragments_prefix_stable e h1;
      MR.witness #(log_region e) (AEAD_GCM.ilog (AEAD_GCM.State?.log s))
		 (fragments_prefix e (fragments e h1))
      end;
    c
    end
  | Stream u s ->
    begin
    let h0 = ST.get() in
    let l = frag_plain_len f in
    let c = Stream.encrypt s l f in
    let h1 = ST.get() in
    if authId i then
      begin
      lemma_fragments_snoc_commutes e h0 h1 (Stream.Entry l c f);
      fragments_prefix_stable e h1;
      MR.witness #(log_region e) (Stream.ilog (Stream.State?.log s))
		 (fragments_prefix e (fragments e h1))
      end;
    c
    end


(* decryption, idealized as a lookup for safe instances *)

//17-04-13 move to fsti?
let fragment_at_j (#i:id) (#rw:rw) (s:state i rw{authId i}) (n:nat) (f:Content.fragment i) h =
  MS.map_has_at_index #_ #_ #(log_region s) (ilog s) ptext n f h

let fragment_at_j_stable (#i:id) (#rw:rw) (s:state i rw{authId i}) (n:nat) (f:C.fragment i)
  : Lemma (MR.stable_on_t #(log_region s) #_ #(MS.grows #(entry i)) (ilog s) (fragment_at_j s n f))
  = MS.map_has_at_index_stable #_ #_ #(log_region s) (ilog s) ptext n f

#set-options "--z3rlimit 100"
let decrypt #i d (ct,c) =
  let h0 = ST.get () in
  recall_region (log_region d);
  match d with
  | Stream _ s ->
    begin
    match Stream.decrypt s (Stream.lenCipher i c) c with
    | None -> None
    | Some f ->
      if authId i then
        begin
        fragment_at_j_stable d (seqnT d h0) f;
        MR.witness #(log_region d) #_ #(MS.grows #(entry i))
          (ilog d) (fragment_at_j d (seqnT d h0) f)
        end;
      Some f
    end
  | StLHAE _ s ->
    let ad = StatefulPlain.makeAD i ct in
    match StLHAE.decrypt s ad c with
    | None -> None
    | Some f ->
      if authId i then
        begin
        fragment_at_j_stable d (seqnT d h0) f;
        MR.witness #(log_region d) #_ #(MS.grows #(entry i))
          (ilog d) (fragment_at_j d (seqnT d h0) f)
        end;
      Some f
