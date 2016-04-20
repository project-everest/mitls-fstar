module StreamAE

// Provides authenticated encryption for a stream of variable-length
// plaintexts; concretely, we use AES_GCM but any other algorithm
// would do.

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found
open Platform.Error
open Platform.Bytes
//open CoreCrypto          // for algorithm names, and key, IV, tag lengths

open TLSError
open TLSConstants
open TLSInfo
open StreamPlain
open MonotoneSeq
open FStar.Monotonic.RRef


type id = i:id { pv_of_id i = TLS_1p3 }

assume val alg: i:id -> Tot CoreCrypto.aead_cipher // unclear what to re-use as alg IDs

let ltag i = CoreCrypto.aeadTagSize (alg i)
let cipherLen i (l:plainLen) = l + ltag i

type cipher i (l:plainLen) = lbytes (cipherLen i l)

// we may need some WFness condition, e.g. correct padding
//val make: i:sid { ~(authId i) } -> r:repr i -> p:plain i { length r = plength p } 
//val repr: i:sid { ~(safeId i) } -> p:plain i -> r:repr i { length r = plength p }  

type entry (i:id) = | Entry: l:plainLen -> c:cipher i l -> p:plain i l -> entry i

// key materials 
type key (i:id) = lbytes (CoreCrypto.aeadKeySize (alg i)) 
type iv  (i:id) = lbytes (CoreCrypto.aeadRealIVSize (alg i)) // should it be aeadSaltSize?

(* let is_seq (i:id) : nat -> GTot Type0 =  *)
(*   fun n -> repr_bytes n <= aeadRecordIVSize (alg i) *)
  
(* type seqn i = n:nat { repr_bytes n <= aeadRecordIVSize (alg i)} *)
(* // unused so far *)
(* let seqn_grows i : FStar.Monotonic.RRef.reln (seqn i) = fun x y -> y >= x //CF not usable?  *)
(* let lemma_seqn_grows_monotone i : Lemma (monotonic (seqn i) (fun x y -> y >= x)) = () *)

val max_uint64: n:nat {repr_bytes n <= 8} 
let max_uint64 = 
  //let n = 18446744073709551615 in
  let n = 1073741823 in //2^30-1 4611686018427387903 in // (2^62-1) (* TODO: Fix this *)
  lemma_repr_bytes_values n; n

let is_seqn i n =  repr_bytes n <= aeadRecordIVSize (alg i)
type seqn i = n:nat { is_seqn i n }

let ideal_log (r:rid) (i:id) = MonotoneSeq.log_t r (entry i)

let log_ref (r:rid) (i:id) : Tot Type0 =
  if authId i 
  then ideal_log r i
  else unit

let ideal_ctr (#l:rid) (r:rid) (i:id) (log:ideal_log l i) : Tot Type0 = 
  MonotoneSeq.counter r log (aeadRecordIVSize (alg i)) //we have a counter, that's increasing, at most to the min(length log, 2^
  
let concrete_ctr (r:rid) (i:id) : Tot Type0 = 
  m_rref r (seqn i) increases

let seqn_ref (#l:rid) (r:rid) (i:id) (log:log_ref l i) : Tot Type0 = 
  if authId i   
  then ideal_ctr r i (log <: ideal_log l i)
  else m_rref r (seqn i) increases

type state (i:id) (rw:rw) = 
  | State: #region:rid 
         -> #peer_region:rid{HyperHeap.disjoint region peer_region}
         -> key:key i
         -> iv: iv i
         -> log: log_ref (if rw=Reader then peer_region else region) i // ghost, subject to cryptographic assumption
         -> counter: seqn_ref region i log // types are sufficient to anti-alias log and counter
         -> state i rw
// Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

type writer i = s:state i Writer
type reader i = s:state i Reader


// Generate a fresh instance with index i in a fresh sub-region of r0
// (we might drop this spec, since F* will infer something at least as precise,
// but we keep it for documentation)
val gen: reader_parent:rid -> writer_parent:rid -> i:id -> ST (reader i * writer i)
  (requires (fun h0 -> HyperHeap.disjoint reader_parent writer_parent))
  (ensures  (fun h0 (rw:reader i * writer i) h1 ->
           let r = fst rw in
           let w = snd rw in
               (* let bang = fun x -> sel h1 x in  *)
               modifies Set.empty h0 h1
               /\ w.region = r.peer_region
               /\ r.region = w.peer_region
               /\ extends (w.region) writer_parent
               /\ extends (r.region) reader_parent
               /\ fresh_region w.region h0 h1
               /\ fresh_region r.region h0 h1
               /\ op_Equality #(log_ref w.region i) w.log r.log  //the explicit annotation here *)
	       /\ (if authId i
 	        then let wlog:ideal_log w.region i = w.log in 
		     let wctr:ideal_ctr w.region i wlog = w.counter in
		     let rctr:ideal_ctr r.region i wlog = r.counter in
		     m_contains wlog h1 /\
		     m_contains wctr h1 /\
		     m_contains rctr h1 /\
		     m_sel h1 wctr = 0 /\
		     m_sel h1 rctr = 0 /\
		     m_sel h1 wlog = createEmpty
		else let wctr:concrete_ctr w.region i = w.counter in
		     let rctr:concrete_ctr r.region i = r.counter in
		     m_contains wctr h1 /\
		     m_contains rctr h1 /\
     		     m_sel h1 wctr = 0 /\
		     m_sel h1 rctr = 0)))

assume val gcut : f:(unit -> GTot Type){f ()} -> Tot unit

let gen reader_parent writer_parent i = 
  let kv   = CoreCrypto.random (CoreCrypto.aeadKeySize (alg i)) in
  let iv   = CoreCrypto.random (CoreCrypto.aeadRealIVSize (alg i)) in
  let reader_r = new_region reader_parent in
  let writer_r = new_region writer_parent in
  lemma_repr_bytes_values 0; 
  if authId i
  then let log  : ideal_log writer_r i = alloc_mref_seq writer_r Seq.createEmpty in 
       let ectr : ideal_ctr writer_r i log = MonotoneSeq.new_counter writer_r 0 log in
       let dctr : ideal_ctr reader_r i log = MonotoneSeq.new_counter reader_r 0 log in
       let writer  = State #i #Writer #writer_r #reader_r kv iv log ectr in
       let reader  = State #i #Reader #reader_r #writer_r kv iv log dctr in
       reader, writer
  else let ectr : concrete_ctr writer_r i = m_alloc writer_r 0 in
       let dctr : concrete_ctr reader_r i = m_alloc reader_r 0 in
       let writer  = State #i #Writer #writer_r #reader_r kv iv () ectr in
       let reader  = State #i #Reader #reader_r #writer_r kv iv () dctr in
       reader, writer
      

// Coerce an instance with index i in a fresh sub-region of r0
val coerce: r0:rid -> p0:rid -> i:id{~(authId i)} -> role:rw -> kv:key i -> iv:iv i -> ST (state i role)
  (requires (fun h0 -> disjoint r0 p0))
  (ensures  (fun h0 s h1 ->
                modifies Set.empty h0 h1
              /\ extends s.region r0
              /\ extends s.peer_region p0
              /\ fresh_region s.region h0 h1
              /\ fresh_region s.peer_region h0 h1))
let coerce r0 p0 i role kv iv =
  let r = new_region r0 in
  let p = new_region p0 in
  lemma_repr_bytes_values 0; 
  let ctr : concrete_ctr r i = m_alloc r 0 in
  State #i #role #r #p kv iv () ctr 


val leak: i:id{~(authId i)} -> role:rw -> state i role -> ST (key i * iv i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1 ))
let leak i role s = State.key s, State.iv s



// The per-record nonce for the AEAD construction is formed as follows:
//
// 1. The 64-bit record sequence number is padded to the left with zeroes to iv_length.
//
// 2. The padded sequence number is XORed with the static client_write_iv or server_write_iv,
//    depending on the role.
//
// The XORing is a fixed, ad hoc, random permutation; not sure what is gained;
// we can reason about sequence-number collisions before applying it.
let aeIV i (n:seqn i) (staticIV: iv i) : iv i =
  let l = CoreCrypto.aeadRealIVSize (alg i) in
  let extended: iv i = bytes_of_int l n (* 64 bit counter extended with 0s *) in
  xor l extended staticIV

// not relying on additional data
let noAD = empty_bytes
 
// encryption (on concrete bytes), returns (cipher @| tag)
// Keeps seqn and nonce implicit; requires the counter not to overflow
// encryption of plaintexts; safe instances are idealized
val encrypt:
  i:id -> e:writer i -> l:plainLen -> p:plain i l -> ST (cipher i l)
    (requires (fun h0 -> 
    	  is_seqn i (m_sel h0 e.counter + 1)))
    (ensures  (fun h0 c h1 ->
                           modifies (Set.singleton e.region) h0 h1
                         /\ m_contains e.log h1
                         /\ m_contains e.counter h1
                         /\ m_sel h1 e.counter = m_sel h0 e.counter + 1
			 /\ (let ent = Entry l c p in
			    let n = Seq.length (m_sel h0 e.log) in
   			      witnessed (MonotoneSeq.at_least n ent e.log)
                           /\  m_sel h1 e.log = snoc (m_sel h0 e.log) ent)))

(* we primarily model the ideal functionality, the concrete code that actually
   runs on the network is what remains after dead code elimination when
   safeId i is fixed to false and after removal of the cryptographic ghost log,
   i.e. all idealization is turned off *)
let encrypt i e l p =
  m_recall e.log;  
  m_recall e.counter;
  let text = if safeId i then createBytes l 0z else repr i l p in
  let c =
    let n = m_read e.counter in
    let iv = aeIV i n e.iv in
    CoreCrypto.aead_encrypt (alg i) e.key iv noAD text in
  testify_counter e.counter;    
  MonotoneSeq.write_at_end e.log (Entry l c p); //need to extend the log first, before incrementing the counter for monotonicity; do this only if ideal
  m_recall e.log;
  increment_counter e.counter;
  m_recall e.counter;
  c


// raw decryption (returning concrete bytes)
private val dec:
  i:id{~(authId i)} -> d:reader i -> l:plainLen -> c:cipher i l
  -> ST (option (lbytes l))
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 ->
      modifies (Set.singleton d.region) h0 h1
    /\ modifies_rref d.region !{as_ref (as_rref d.counter)} h0 h1
    /\ m_contains d.counter h1))
let dec i d l c =
  m_recall d.counter;
  let n = m_read d.counter in
  let iv = aeIV i n d.iv  in
  match CoreCrypto.aead_decrypt (alg i) d.key iv noAD c with
  | Some p ->
    if n + 1 < max_uint64 then
    begin
      lemma_repr_bytes_values (n + 1);
      m_write d.counter (n + 1);
      Some p
    end
    else
    begin
      //CF revisit; I'd prefer to statically prevent it.
      // overflow, we don't care
      // lemma_repr_bytes_values 0;
      // m_write d.counter 0;
      None
    end
  | None -> None

//val matches: #i:id -> l:plainLen -> c:cipher i l -> entry i -> Tot bool
let matches #i l (c: cipher i l) (Entry l' c' _) = l = l' && c = c'

// decryption, idealized as a lookup of (c,ad) in the log for safe instances
val decrypt:
  i:id -> d:reader i -> l:plainLen -> c:cipher i l
  -> ST (option (plain i l))
  (requires (fun h0 -> is_seqn i (m_sel h0 d.counter + 1)))
  (ensures  (fun h0 res h1 ->
	      (authId i ==>
                 (let log :seq (entry i) = m_sel h0 d.log in
		  let j = m_sel h0 d.counter in
		  if j < Seq.length log && matches l c (Seq.index log j)
		  then res = Some (Entry.p (Seq.index log j))
		       /\ m_sel h1 d.counter = j + 1
		  else res = None))
	  /\ (match res with
 	     | None -> modifies Set.empty h0 h1
	     | _ -> modifies (Set.singleton d.region) h0 h1
	           /\ modifies_rref d.region !{as_ref (as_rref d.counter)} h0 h1)))

// decryption, idealized as a lookup of (c,ad) in the log for safe instances
let decrypt i d l c =
  m_recall d.log; m_recall d.counter;
  let log = m_read d.log in
  let j = m_read d.counter in
  testify_counter d.counter; //now we know that j is at most the length of the log
  if authId i 
  then if j < Seq.length log && matches l c (Seq.index log j)
       then (increment_counter d.counter;
	     Some (Entry.p (Seq.index log j)))
       else None
  else //concrete
     let iv = aeIV i j d.iv  in
     match CoreCrypto.aead_decrypt (alg i) d.key iv noAD c with
     | None -> None
     | Some pr ->
	 (match mk_plain i l pr with
           | Some p -> 
	     //TODO: WE SHOULD STILL INCREMENT THE COUNTER, but we need conditional idealization first
	     Some p
           | None  -> None)


(* TODO

- Check that decrypt indeed must use authId and not safeId (like in the F7 code)
- How to handle counter overflows?
- Injective allocation table from i to refs

*)

(* another version; we'll probably also need an explicit invariant
val encrypt: #i:sid -> wr:writer i -> p:plain i -> ST (cipher i (plength p))
  (requires (fun h ->
      st_enc_inv wr h /\
      is_seqn (sel h wr.seqn + 1)))
  (ensures  (fun h0 c h1 ->
      st_enc_inv wr h1 /\
      modifies (Set.singleton wr.region) h0 h1 /\
      modifies_rref wr.region (refs_in_e wr) h0 h1 /\
      sel h1 wr.seqn = sel h0 wr.seqn + 1 /\
      sel h1 wr.log = snoc (sel h0 wr.log) (Entry c p)))

val decrypt: i:sid -> d:reader i -> c:bytes -> ST (option (dplain i c))
  (requires (fun h ->
      (authId ==> st_dec_inv rd h) /\
      is_seqn (sel h rd.seqn + 1)))

  (ensures  (fun h0 res h1 ->
               modifies Set.empty h0 h1
             /\ (authId i ==>
                 Let (sel h0 d.log) // no let, as we still need a type annotation
                   (fun (log:seq (entry i)) ->
                       (is_None res ==> (forall (j:nat{j < Seq.length log}).{:pattern (found j)}
                                            found j /\ ~(matches c ad (Seq.index log j))))
                     /\ (is_Some res ==> (exists (j:nat{j < Seq.length log}).{:pattern (found j)}
                                           found j
                                           /\ matches c ad (Seq.index log j)
                                           /\ Entry.p (Seq.index log j) == Some.v res))))))
*)
