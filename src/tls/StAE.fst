module StAE // See StAE.fsti
open FStar.HyperHeap
open FStar.Monotonic.RRef
open FStar.Seq
open Platform.Bytes

open TLSConstants
open TLSInfo
open Content

module HH = HyperHeap
module MR = FStar.Monotonic.RRef
module SeqP = SeqProperties
module S = StreamAE

#reset-options "--z3timeout 10 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

// plaintexts are defined in Content.fragment i

// ciphertexts, ignoring details for now (would be needed for functional correctness)
// the first two should be concretely defined (for now in TLSInfo)
 
let is_stream_ae i = pv_of_id i = TLS_1p3
let is_stateful_lhae i = pv_of_id i <> TLS_1p3 /\ is_AEAD i.aeAlg /\ ~ (authId i)

// NB as a temporary hack, we currently disable AuthId for TLS 1.2.
// so that we can experiment with TLS and StreamAE

assume val validCipherLen: i:id -> l:nat -> Type0 // sufficient to ensure the cipher can be processed without length errors

let frag_plain_len (#i:id) (f:fragment i) : StreamPlain.plainLen = 
  admit();
  snd (Content.rg i f) + 1

val cipherLen: i:id -> fragment i -> Tot (l:nat {validCipherLen i l})
(* val cipherLen: i:id -> fragment i -> Tot nat *)
let cipherLen i f = 
  admit();
  if is_stream_ae i 
  then StreamAE.cipherLen i (frag_plain_len f)
  else 0 //placeholder
  
type encrypted (#i:id) (f:fragment i) = lbytes (cipherLen i f)
type decrypted (i:id) = b:bytes { validCipherLen i (length b) }

// concrete key materials, for leaking & coercing.
// (each implementation splits it into encryption keys, IVs, MAC keys, etc)
let aeKeySize (i:id) = 
  if pv_of_id i = TLS_1p3 
  then CoreCrypto.aeadKeySize (StreamAE.alg i) + CoreCrypto.aeadRealIVSize (StreamAE.alg i)
  else 0 //FIXME!

type keybytes (i:id) = lbytes (aeKeySize i)

// abstract instances
  
type state (i:id) (rw:rw) = 
  | Stream: u:unit{is_stream_ae i}         -> StreamAE.state i rw -> state i rw 
  | StLHAE: u:unit{is_stateful_lhae i} -> StatefulLHAE.state i rw -> state i rw 

val region: #i:id -> #rw:rw -> state i rw -> Tot rgn
let region (#i:id) (#rw:rw) (s:state i rw): Tot rgn = 
  match s with 
  | Stream u x -> StreamAE.State.region x
  | StLHAE u x -> StatefulLHAE.region x

val log_region: #i:id -> #rw:rw -> state i rw -> Tot rgn
let log_region (#i:id) (#rw:rw) (s:state i rw): Tot rgn = 
  match s with 
  | Stream _ s -> StreamAE.State.log_region s
  | StLHAE _ s -> if rw = Writer then StatefulLHAE.region s else StatefulLHAE.peer_region s //FIXME

type reader i = state i Reader
type writer i = state i Writer


// how to specify those two? Their properties are available at creation-time. 


// our view to AE's ideal log (when idealized, ignoring ciphers) and counter
// TODO: write down their joint monotonic specification: both are monotonic, and seqn = length log when ideal

type ideal_log (i:id) = seq (fragment i)  // TODO: consider adding constraint on terminator fragments

// TODO extend library? We need a full spec; NS: nope, no need for a full spec; it is Tot

val un_snoc: #a: Type -> s:seq a {Seq.length s > 0} -> Tot(seq a * a)
let un_snoc #a s =
  let last = Seq.length s - 1 in
  Seq.slice s 0 last, Seq.index s last

val seq_mapT: ('a -> Tot 'b) -> s:seq 'a -> Tot (seq 'b)
    (decreases (Seq.length s))
let rec seq_mapT f s = 
  if Seq.length s = 0 then Seq.createEmpty
  else let prefix, last = un_snoc s in
       SeqProperties.snoc (seq_mapT f prefix) (f last)

val seq_map_snoc: f:('a -> Tot 'b) -> s:seq 'a -> a:'a -> Lemma
  (seq_mapT f (SeqP.snoc s a) = SeqP.snoc (seq_mapT f s) (f a))
#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let seq_map_snoc f s a = 
  let prefix, last = un_snoc (SeqP.snoc s a) in 
  cut (Seq.equal prefix s)

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

val logT: #i:id -> #rw:rw -> s:state i rw{ authId i } -> HH.t -> GTot (ideal_log i)
let logT #i #rw s h = 
  match s with
  | Stream _ s -> let written = m_sel h (StreamAE.ilog (StreamAE.State.log s)) in
                 seq_mapT #(StreamAE.entry i) #(fragment i) StreamAE.Entry.p written

let stream_ae (#i:id{is_stream_ae i}) (#rw:rw) (s:state i rw) 
  : Tot (StreamAE.state i rw)
  = let Stream _ s = s in s

let st_lhae (#i:id{is_stateful_lhae i}) (#rw:rw) (s:state i rw) 
  : Tot (StatefulLHAE.state i rw)
  = let StLHAE _ s = s in s

val lemma_logT_snoc_commutes: #i:id -> w:writer i{is_stream_ae i} 
    -> h0:HH.t -> h1:HH.t -> e:S.entry i
    -> Lemma (authId i 
	     ==>  (let sw = stream_ae w in
                   let log = S.ilog (StreamAE.State.log sw) in
	               MR.m_sel h1 log = SeqP.snoc (MR.m_sel h0 log) e
  	           ==> logT w h1 = SeqP.snoc (logT w h0) (StreamAE.Entry.p e)))
let lemma_logT_snoc_commutes #i w h0 h1 e = 
  if authId i 
  then let sw = stream_ae w in
       let log = S.ilog (StreamAE.State.log sw) in
       seq_map_snoc #(S.entry i) #(fragment i) StreamAE.Entry.p (MR.m_sel h0 log) e
  else ()       
  
val seqnT: #i:id -> #rw:rw -> state i rw -> HH.t -> GTot seqn_t 
let seqnT #i #rw (s:state i rw) h = 
  match s with 
  | Stream _ s -> m_sel h (StreamAE.ctr (StreamAE.State.counter s))
  | StLHAE _ s -> sel h (StatefulLHAE.State.seqn s)

let incrementable (#i:id) (#rw:rw) (s:state i rw) (h:HH.t) = is_seqn (seqnT s h + 1)

let writable_seqn (#i:id) (#rw:rw) (s:state i rw) h = 
    match s with 
    | Stream _ s -> is_seqn (m_sel h (StreamAE.ctr (StreamAE.State.counter s)) + 1)
    | StLHAE _ s -> is_seqn (sel h (StatefulLHAE.State.seqn s) + 1) 

(*

type cipher (i:id) = b:bytes {Range.valid_clen i (length b)}

let cipher_noId b : cipher noId = b 

type entry i = 
  | EStream: u:unit{is_stream_ae i}     -> StreamAE.entry i  -> entry i 
  | EStLHAE: u:unit{is_stateful_lhae i} -> StatefulLHAE.entry i  -> entry i 

val fragment_entry: #i:id -> e: entry i -> Tot (Content.fragment i)

let fragment_entry #i = function 
  | EStream _ (StreamAE.Entry _ _ f) -> f 
  | EStLHAE _ (StatefulLHAE.Entry _ _ f) -> f 

let writer_modifies #i wr h0 h1 = 
  HyperHeap.modifies (Set.singleton (region wr))) h0 h1 
  | StLHAE _ wr -> (
      HyperHeap.modifies (Set.singleton (StatefulLHAE.region wr)) h0 h1 /\
      Heap.modifies (!{ as_ref (StatefulLHAE.log wr), as_ref (StatefulLHAE.seqn wr)}) (Map.sel h0 (StatefulLHAE.region wr)) (Map.sel h1 (StatefulLHAE.region wr)) )

*)



// Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

// We generate first the writer, then the reader (possibly several of them)

let genPost (#i:id) parent h0 (w:writer i) h1 = 
  let r = region w in 
  modifies Set.empty h0 h1 /\
  HH.parent r = parent /\
  fresh_region r h0 h1 /\
  color r = color parent /\
  seqnT w h1 = 0 /\
  (authId i ==> logT w h1 = createEmpty) // we need to re-apply #i knowning authId

// Generate a fresh instance with index i in a fresh sub-region 

val gen: parent:rid -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures (genPost parent))

// Coerce a writer with index i in a fresh subregion of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rid -> i:id{~(authId i)} -> keybytes i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))

val leak: #i:id{~(authId i)} -> #role:rw -> state i role -> ST (keybytes i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1 ))

val genReader: parent:rid -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 -> HyperHeap.disjoint parent (region w))) //16-04-25  we may need w.region's parent instead
  (ensures  (fun h0 (r:reader i) h1 ->
               modifies Set.empty h0 h1 /\
               log_region r = region w /\
               HH.parent (region r) = parent /\
	       color (region r) = color parent /\
               fresh_region (region r ) h0 h1 /\
               //?? op_Equality #(log_ref w.region i) w.log r.log /\
               seqnT r h1 = 0))
// encryption, recorded in the log; safe instances are idealized

val encrypt: #i:id -> e:writer i -> f:fragment i -> ST (encrypted f)
  (requires (fun h0 -> incrementable e h0))
  (ensures  (fun h0 c h1 ->
               modifies_one (region e) h0 h1 /\
               seqnT e h1 = seqnT e h0 + 1   /\
               (authId i ==> logT e h1 = SeqP.snoc (logT e h0) f)))
let encrypt #i e f =
  assume (is_stream_ae i);
  match e with
  | Stream _ s -> 
    let h0 = ST.get() in
    let l = frag_plain_len f in
    let c = StreamAE.encrypt s l f in
    let h1 = ST.get() in
    lemma_logT_snoc_commutes e h0 h1 (S.Entry l c f);
    c

//TODO restore monotonic post; see StreamAE.fsti

// decryption, idealized as a lookup for safe instances
val decrypt: #i:id -> d:reader i -> c:decrypted i -> ST (option (f:fragment i { length c = cipherLen i f}))
  (requires (fun h0 -> incrementable d h0))
  (ensures  (fun h0 res h1 ->
	      match res with
 	     | None   -> modifies Set.empty h0 h1
	     | Some f -> let j = seqnT d h0 in 
                        modifies_one (region d) h0 h1 /\ 
                        seqnT d h1 = j + 1 /\
                        (authId i ==>
                           (let written = logT d h1 in 
                           j < Seq.length written /\
                           f = Seq.index written j)))) 


let gen parent i =  
   assume false;
   // assert(is_stream_ae i);  
   Stream () (StreamAE.gen parent i) 

let coerce parent i kiv = 
    assume false;
   // assert(is_stream_ae i); 
   let kv, iv = Platform.Bytes.split kiv (CoreCrypto.aeadKeySize (StreamAE.alg i)) in 
   Stream () (StreamAE.coerce parent i kv iv) 

let leak #i #role s =  
    assume false;
   // assert(is_stream_ae i); 
   match s with 
   | Stream _ s -> let kv, iv = StreamAE.leak s in kv @| iv

let genReader parent #i w =  
    assume false;
  // assert(is_stream_ae i);  *)
  match w with 
  | Stream _ w -> Stream () (StreamAE.genReader parent w) 

let decrypt #i d c =  
    assume false;
   match d with 
   | Stream _ s -> 
       ( match StreamAE.decrypt s (StreamAE.lenCipher i c) c with 
         | Some x -> Some x 
         | None   -> None)
