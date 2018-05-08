(**
Authenticated encryptions of streams of TLS fragments (from Content)
multiplexing StatefulLHAE and StreamAE with (some) length hiding
(for now, under-specifying ciphertexts lengths and values)
*)
module StAE
module HST = FStar.HyperStack.ST //Added automatically


open FStar.HyperStack
open FStar.Bytes

open TLSConstants
open TLSInfo


module HS   = FStar.HyperStack

module MS   = FStar.Monotonic.Seq
module C    = Content

module Stream = StreamAE
module StLHAE = StatefulLHAE
module Range = Range
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

////////////////////////////////////////////////////////////////////////////////
//Distinguishing the two multiplexing choices of StAE based on the ids
////////////////////////////////////////////////////////////////////////////////
let is_stream i = ID13? i

let is_stlhae i = ID12? i && AEAD? (aeAlg_of_id i) &&
  (AEAD?._0 (aeAlg_of_id i) = CoreCrypto.AES_128_GCM ||
   AEAD?._0 (aeAlg_of_id i) = CoreCrypto.AES_256_GCM)

// type id = i:id {is_stream i \/ is_stlhae i}

// PLAINTEXTS are defined in Content.fragment i
//16-06-08 see also StreamPlain and StatefulPlain.

type stae_id = i:id {is_stream i \/ is_stlhae i}

////////////////////////////////////////////////////////////////////////////////
//Various utilities related to lengths of ciphers and fragments
////////////////////////////////////////////////////////////////////////////////

let frag_plain_len (#i:id{is_stream i}) (f:C.fragment i): StreamPlain.plainLen =
  snd (C.rg i f) + 1

let frag_cipher_len (#i:id{is_stream i}) (f:C.fragment i) =
  frag_plain_len f + Stream.ltag i

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

type keyBytes (i:stae_id) = lbytes (aeKeySize i)


////////////////////////////////////////////////////////////////////////////////
//`state i rw`, a sum to cover StreamAE (1.3) and StatefulLHAE (1.2)
////////////////////////////////////////////////////////////////////////////////
noeq type state (i:id) (rw:rw) =
  | Stream: u:unit{is_stream i} -> Stream.state i rw -> state i rw
  | StLHAE: u:unit{is_stlhae i} -> StLHAE.state i rw -> state i rw

let stream_state (#i:id{is_stream i}) (#rw:rw) (s:state i rw)
  : Tot (Stream.state i rw)
  = let Stream _ s = s in s

let stlhae_state (#i:id{is_stlhae i}) (#rw:rw) (s:state i rw)
  : Tot (StatefulLHAE.state i rw)
  = let StLHAE _ s = s in s

val region: #i:id -> #rw:rw -> state i rw -> Tot rgn
let region (#i:id) (#rw:rw) (s:state i rw): Tot rgn =
  match s with
  | Stream _ x -> Stream.State?.region x
  | StLHAE _ x -> StLHAE.region x

val log_region: #i:id -> #rw:rw -> state i rw -> Tot rgn
let log_region (#i:id) (#rw:rw) (s:state i rw): Tot rgn =
  match s with
  | Stream _ s -> Stream.State?.log_region s
  | StLHAE _ s -> AEAD_GCM.State?.log_region s

type reader i = state i Reader
type writer i = state i Writer

// For 0-RTT: we ignore a failed decryption for the
// handshake traffic key reader if the counter is 0
let tolerate_decrypt_failure (#i:id) (r:reader i)
  : ST bool
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  match r with
  | StLHAE _ _ -> false
  | Stream _ st ->
    let ctr = HST.op_Bang (StreamAE.ctr st.StreamAE.counter) in
    let ID13 (KeyID #li (ExpandedSecret _ t _)) = i in
    0 = ctr && ClientHandshakeTrafficSecret? t

let tolerate_ccs (#i:id) (r:reader i)
  : ST bool
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> modifies_none h0 h1)
  =
  match r with
  | StLHAE _ _ -> false
  | Stream _ st ->
    let ctr = ! (StreamAE.ctr st.StreamAE.counter) in
    let ID13 (KeyID #li (ExpandedSecret _ t _)) = i in
    0 = ctr && (ServerHandshakeTrafficSecret? t ||
      ClientHandshakeTrafficSecret? t || ClientEarlyTrafficSecret? t)

// our view to AE's ideal log (when idealized, ignoring ciphers) and counter
// TODO: write down their joint monotonic specification: both are monotonic,
// and seqn = length log when ideal

////////////////////////////////////////////////////////////////////////////////
//Logs of fragments, defined as projections on the underlying entry logs
////////////////////////////////////////////////////////////////////////////////
// TODO: consider adding constraint on terminator fragments
type frags (i:id{~ (PlaintextID? i)}) = Seq.seq (C.fragment i)

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

private
let ptext (#i:id) (ent:entry i): Tot (C.fragment i) =
  if is_stream i then
    Stream.Entry?.p #i ent
  else
    AEAD_GCM.Entry?.p #i ent

//A projection of fragments from Stream.entries
let fragments (#i:id) (#rw:rw) (s:state i rw{authId i}) (h:mem): GTot (frags i) =
  let entries = HS.sel #_ #MS.grows h (ilog s) in
  MS.map ptext entries

val lemma_fragments_snoc_commutes: #i:id -> w:writer i{authId i}
  -> h0:mem -> h1:mem -> e:entry i
  -> Lemma (let log = ilog w in
           HS.sel #_ #MS.grows h1 log ==
	   Seq.snoc (HS.sel #_ #MS.grows h0 log) e ==>
	   fragments w h1 == Seq.snoc (fragments w h0) (ptext e))
let lemma_fragments_snoc_commutes #i w h0 h1 e =
  let log = ilog w in
  MS.map_snoc ptext (HS.sel #_ #MS.grows h0 log) e

//A predicate stating that the fragments have fs as a prefix
let fragments_prefix (#i:id) (#rw:rw) (w:state i rw{authId i}) (fs:frags i) (h:mem) : GTot Type0 =
  MS.map_prefix #_ #_ #(log_region w) (ilog w) ptext fs h

//In order to witness fragments_prefix s fs, we need to prove that it is stable
val fragments_prefix_stable: #i:id -> #rw:rw
  -> w:state i rw{authId i} -> h:mem
  -> Lemma (let fs = fragments w h in
	   MS.grows fs fs
	   /\ HST.stable_on_t #(log_region w) #_ #(MS.grows #(entry i)) (ilog w)
	     (fragments_prefix w fs))
let fragments_prefix_stable #i #rw w h =
  let fs = fragments w h in
  let log = ilog w in
  // MS.seq_extension_reflexive fs; //NS: seems no longer necessary
  MS.map_prefix_stable #_ #_ #(log_region w) log ptext fs


////////////////////////////////////////////////////////////////////////////////
//Projecting sequence numbers
////////////////////////////////////////////////////////////////////////////////

let seqnT (#i:id) (#rw:rw) (s:state i rw) h : GTot nat =
  match s with
  | Stream _ s -> HS.sel h (Stream.ctr (Stream.State?.counter s))
  | StLHAE _ s -> HS.sel h (AEAD_GCM.ctr (StLHAE.counter s))

//it's incrementable if it doesn't overflow
let incrementable (#i:id) (#rw:rw) (s:state i rw) (h:mem) =
  seqnT s h < 18446744073709551615

// Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

// We generate first the writer, then the reader (possibly several of them)


////////////////////////////////////////////////////////////////////////////////
//Framing
////////////////////////////////////////////////////////////////////////////////
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

let trigger_frame (h:mem) = True

let frame_f (#a:Type) (f:mem -> GTot a) (h0:mem) (s:Set.set rid) =
  forall h1.{:pattern trigger_frame h1}
        trigger_frame h1
        /\ (HS.equal_on s h0.h h1.h ==> f h0 == f h1)

val frame_seqT_auto: i:id -> rw:rw -> s:state i rw -> h0:mem -> h1:mem ->
  Lemma (requires   HS.equal_on (Set.singleton (region s)) h0.h h1.h
		  /\ Map.contains h0.h (region s))
        (ensures seqnT s h0 = seqnT s h1)
	[SMTPat (seqnT s h0);
	 SMTPat (seqnT s h1)]
//	 SMTPatT (trigger_frame h1)]
let frame_seqT_auto i rw s h0 h1 = ()

val frame_fragments_auto: i:id{authId i} -> rw:rw -> s:state i rw -> h0:mem -> h1:mem ->
  Lemma (requires    HS.equal_on (Set.singleton (log_region s)) h0.h h1.h
		  /\ Map.contains h0.h (log_region s))
        (ensures fragments s h0 == fragments s h1)
	[SMTPat (fragments s h0);
	 SMTPat (fragments s h1)]
	 (* SMTPatT (trigger_frame h1)] *)
let frame_fragments_auto i rw s h0 h1 = ()


////////////////////////////////////////////////////////////////////////////////
//Experimenting with reads clauses: probably unnecessary
////////////////////////////////////////////////////////////////////////////////
let reads (s:Set.set rid) (a:Type) =
    f: (h:mem -> GTot a){forall h1 h2. (HS.equal_on s h1.h h2.h /\ Set.subset s (Map.domain h1.h))
				  ==> f h1 == f h2}

(*
val fragments' : #i:id -> #rw:rw -> s:state i rw{ authId i } -> Tot (reads (Set.singleton (log_region s)) (frags i))
let fragments' #i #rw s = fun h -> fragments #i #rw s h
*)

(*------------------------------------------------------------------*)
let genPost (#i:id) parent h0 (w:writer i) h1 =
  let r = region #i #Writer w in
  HS.modifies_transitively Set.empty h0 h1 /\
  HS.extends r parent /\
  HS.fresh_region r h0 h1 /\
  color r = color parent /\
  seqnT #i #Writer w h1 = 0 /\
  (authId i ==> fragments #i #Writer w h1 == Seq.createEmpty) // we need to re-apply #i knowning authId

// Generate a fresh instance with index i in a fresh sub-region
val gen: parent:rgn -> i:stae_id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures (genPost parent))
#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let gen parent i =
  if is_stream i then
    Stream () (Stream.gen parent i)
  else
    StLHAE () (StLHAE.gen parent i)

#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
val genReader: parent:rgn -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 -> HS.disjoint parent (region #i #Writer w))) //16-04-25  we may need w.region's parent instead
  (ensures  (fun h0 (r:reader i) h1 ->
               modifies Set.empty h0 h1 /\
               log_region r = region #i #Writer w /\
               extends (region r) parent /\
	       color (region r) = color parent /\
               HS.fresh_region (region r) h0 h1 /\
               //op_Equality #(log_ref w.region i) w.log r.log /\
               seqnT r h1 = 0))
// encryption, recorded in the log; safe instances are idealized
let genReader parent #i w =
  match w with
  | Stream _ w ->
    lemma_ID13 i;
    assume(StreamAE.(HS.disjoint parent (AEADProvider.region #i w.aead)));
    Stream () (Stream.genReader parent #i w)
  | StLHAE _ w ->
    lemma_ID12 i;
    assume(AEAD_GCM.(HS.disjoint parent (AEADProvider.region #i w.aead)));
    StLHAE () (StLHAE.genReader parent #i w)


////////////////////////////////////////////////////////////////////////////////
//Coerce & Leak
////////////////////////////////////////////////////////////////////////////////

// Coerce a writer with index i in a fresh subregion of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rgn -> i:stae_id{~(authId i)} -> keyBytes i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))
#set-options "--z3rlimit 100"
let coerce parent i kiv =
  if is_stream i then
    let kv,iv = FStar.Bytes.split_ kiv (CoreCrypto.aeadKeySize (Stream.alg i)) in
    Stream () (Stream.coerce parent i kv iv)
  else
    let kv,iv = FStar.Bytes.split_ kiv (CoreCrypto.aeadKeySize (StLHAE.alg i)) in
    StLHAE () (StLHAE.coerce parent i kv iv)

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 2 --max_ifuel 2"
val leak: #i:id{~(authId i)} -> #role:rw -> s:state i role -> ST (keyBytes i) //with 2 units of i_fuel, we can invert s and prove that i must be an stae_id
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1 ))
let leak #i #role s =
  match s with
  | Stream _ s -> let kv,iv = Stream.leak s in kv @| iv
  | StLHAE _ s -> let kv,iv = StLHAE.leak s in kv @| iv


// ADL Jan 19. Made some progress on encrypt but need to merge lowlevel now
#set-options "--lax"

////////////////////////////////////////////////////////////////////////////////
//Encryption
////////////////////////////////////////////////////////////////////////////////
#set-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 3 --max_ifuel 3"
val encrypt: #i:id -> e:writer i -> f:C.fragment i -> ST (C.encrypted f)
  (requires (fun h0 -> incrementable e h0))
  (ensures  (fun h0 c h1 ->
               modifies_one (region e) h0 h1
	       /\ seqnT e h1 = seqnT e h0 + 1
	       /\ frame_f (seqnT e) h1 (Set.singleton (log_region e))
	       /\ (authId i ==>
		  fragments e h1 == Seq.snoc (fragments e h0) f
		  /\ frame_f (fragments e) h1 (Set.singleton (log_region e))
		  /\ HST.witnessed (fragments_prefix e (fragments e h1)))))
let encrypt #i e f =
  match e with
  | StLHAE u s ->
    begin
    let h0 = get() in
    let ct,rg = C.ct_rg i f in
    let ad = StatefulPlain.makeAD i ct in
    let seqn = HST.op_Bang (AEAD_GCM.ctr (StLHAE.counter s)) in
    let c = StLHAE.encrypt s ad rg f in
    let h1 = get() in
    if authId i then
      begin
      lemma_repr_bytes_values seqn;
      let ad' = LHAEPlain.makeAD i seqn ad in
      let ent = AEAD_GCM.Entry c ad' f in
      lemma_fragments_snoc_commutes e h0 h1 ent;
      fragments_prefix_stable e h1;
      HST.mr_witness #(log_region e) (AEAD_GCM.ilog (AEAD_GCM.State?.log s))
		 (fragments_prefix e (fragments e h1))
      end;
    c
    end
  | Stream u s ->
    begin
    let h0 = get() in
    let l = frag_plain_len f in
    let cl = frag_cipher_len f in
    let ad = C.ctBytes C.Application_data @| versionBytes TLS_1p2 @| bytes_of_int 2 cl in
    let c = Stream.encrypt s ad l f in
    let h1 = get() in
    if authId i then
      begin
      lemma_fragments_snoc_commutes e h0 h1 (Stream.Entry l c f);
      fragments_prefix_stable e h1;
      HST.mr_witness #(log_region e) (Stream.ilog (Stream.State?.log s))
		 (fragments_prefix e (fragments e h1))
      end;
    c
    end


////////////////////////////////////////////////////////////////////////////////
//Decryption
////////////////////////////////////////////////////////////////////////////////
// decryption, idealized as a lookup for safe instances
let fragment_at_j (#i:id) (#rw:rw) (s:state i rw{authId i}) (n:nat) (f:C.fragment i) h =
  MS.map_has_at_index #_ #_ #(log_region s) (ilog s) ptext n f h

let fragment_at_j_stable (#i:id) (#rw:rw) (s:state i rw{authId i}) (n:nat) (f:C.fragment i)
  : Lemma (HST.stable_on_t #(log_region s) #_ #(MS.grows #(entry i)) (ilog s) (fragment_at_j s n f))
  = MS.map_has_at_index_stable #_ #_ #(log_region s) (ilog s) ptext n f


val decrypt: #i:id -> d:reader i -> c:C.decrypted i
  -> ST (option (f:C.fragment i))
    (requires (fun h0 -> incrementable d h0))
    (ensures  (fun h0 res h1 ->
   	        match res with
  	        | None -> modifies Set.empty h0 h1
  	        | Some f ->
		  let ct,rg = C.ct_rg i f in
		  let j = seqnT d h0 in
  		  seqnT d h1 = j + 1 /\
    	          (if is_stream i then
		    frag_plain_len #i f <= C.cipherLen i f
		  else
		    ct = fst c /\
		    Range.wider (Range.cipherRangeClass i (length (snd c))) rg) /\
                  modifies_one (region d) h0 h1 /\
  	          (authId i ==>
  	            (let written = fragments d h0 in
   	             j < Seq.length written /\
  	             f = Seq.index written j /\
  	             frame_f (fragments d) h1 (Set.singleton (log_region d)) /\
  	             HST.witnessed (fragment_at_j d j f)))))

#set-options "--z3rlimit 100"

let decrypt #i d (ct,c) =
  let h0 = get () in
  recall_region (log_region d);
  match d with
  | Stream _ s ->
    begin
    let ad = C.ctBytes ct @| versionBytes TLS_1p2 @| bytes_of_int 2 (length c) in
    match Stream.decrypt s ad (Stream.lenCipher i c) c with
    | None -> None
    | Some f ->
      if authId i then
        begin
        fragment_at_j_stable d (seqnT d h0) f;
        HST.mr_witness #(log_region d) #_ #(MS.grows #(entry i))
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
        HST.mr_witness #(log_region d) #_ #(MS.grows #(entry i))
          (ilog d) (fragment_at_j d (seqnT d h0) f)
        end;
      Some f
