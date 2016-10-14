module AEAD_GCM

// AEAD-GCM mode for the TLS record layer, as specified in RFC 5288.
// We support both AES_128_GCM and AES_256_GCM, differing only in their key sizes

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open FStar.SeqProperties
open Platform.Bytes
open CoreCrypto

open TLSConstants
open TLSInfo
open LHAEPlain

open Range
open FStar.Monotonic.Seq
open FStar.Monotonic.RRef

type id = i:id{ is_ID12 i /\ is_AEAD (aeAlg_of_id i) /\
  (AEAD._0 (aeAlg_of_id i) == AES_128_GCM \/
   AEAD._0 (aeAlg_of_id i) == AES_256_GCM) }

let alg (i:id) = AEAD._0 (aeAlg_of_id i)

type cipher (i:id) = c:bytes{ valid_clen i (length c) }

// key materials (TODO: make abstract?)
type key (i:id) = lbytes (aeadKeySize (alg i))
type iv  (i:id) = lbytes (aeadSaltSize (alg i)) // GCMNonce.salt[4]

irreducible let max_ctr (a:aeadAlg) : Tot (n:nat{n = 18446744073709551615}) = 
  assert_norm (pow2 64 - 1 = 18446744073709551615);
  pow2 64 - 1
//pow2 (8 * aeadRecordIVSize a) - 1, but not for CHACHA20_POLY1305
  
// this is the same as a sequence number and in bytes, GCMNonce.nonce_explicit[8]
type counter a = c:nat{c <= max_ctr a} 

type dplain (i:id) (ad:adata i) (c:cipher i) =
  plain i ad (cipherRangeClass i (length c))
 
type entry (i:id) = // records that c is an encryption of p with ad
  | Entry: c:cipher i -> ad:adata i -> p:dplain i ad c -> entry i

let ideal_log (r:rid) (i:id) = log_t r (entry i)

let log_ref (r:rid) (i:id) : Tot Type0 =
  if authId i then ideal_log r i else unit

let ilog (#r:rid) (#i:id) (l:log_ref r i{authId i}) : Tot (ideal_log r i) =
  l

(** we have a counter, that's increasing, at most to the min(length log, 2^64-1) *)
let ideal_ctr (#l:rid) (r:rid) (i:id) (log:ideal_log l i) : Tot Type0 =
  FStar.Monotonic.Seq.seqn r log (max_ctr (alg i))

let concrete_ctr (r:rid) (i:id) : Tot Type0 =
  m_rref r (counter (alg i)) increases

let ctr_ref (#l:rid) (r:rid) (i:id) (log:log_ref l i) : Tot Type0 =
  if authId i
  then ideal_ctr r i (ilog log)
  else m_rref r (counter (alg i)) increases

let ctr (#l:rid) (#r:rid) (#i:id) (#log:log_ref l i) (c:ctr_ref r i log)
  : Tot (m_rref r (if authId i
		   then seqn_val #l #(entry i) r log (max_ctr (alg i))
		   else counter (alg i))
		increases) =
  c

// kept concrete for log and counter, but the key and iv should be private.
noeq type state (i:id) (rw:rw) =
  | State: #region: rgn
         -> #log_region: rgn{if rw = Writer then region = log_region else HyperHeap.disjoint region log_region}
         -> key: key i
         -> iv: iv i
         -> log: log_ref log_region i // ghost subject to cryptographic assumption
         -> counter: ctr_ref region i log // types are sufficient to anti-alias log and counter
         -> state i rw
	 // Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

type writer i = s:state i Writer
type reader i = s:state i Reader

(*
type matching (#i:id) (r:reader i) (w:writer i) =
  r.region = w.peer_region
  /\ w.region = r.peer_region
  /\ r.log == w.log
  /\ disjoint (parent r.region) (parent w.region)
*)

let genPost (#i:id) parent h0 (w:writer i) h1 =
  modifies Set.empty h0 h1 /\
  extends w.region parent /\
  stronger_fresh_region w.region h0 h1 /\
  color w.region = color parent /\
  (authId i ==> (m_contains (ilog w.log) h1 /\ m_sel h1 (ilog w.log) == createEmpty)) /\
  m_contains (ctr w.counter) h1 /\
  m_sel h1 (ctr w.counter) === 0

// Generate a fresh instance with index i in a fresh sub-region of r0
// (we can drop this spec, since F* will infer something at least as precise,
// but we keep it for documentation)
val gen: parent:rid -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))

(*
 * AR: had to add implicits for etcr.
 *)
let gen parent i =
  let kv = CoreCrypto.random (aeadKeySize (alg i)) in
  let iv = CoreCrypto.random (aeadSaltSize (alg i)) in
  let writer_r = new_region parent in
  if authId i then
    let log : ideal_log writer_r i = alloc_mref_seq writer_r Seq.createEmpty in
    let ectr: ideal_ctr #writer_r writer_r i log = new_seqn #writer_r #(entry i) #(max_ctr (alg i)) writer_r 0 log in
    State #i #Writer #writer_r #writer_r kv iv log ectr
  else
    let ectr: concrete_ctr writer_r i = m_alloc writer_r 0 in
    State #i #Writer #writer_r #writer_r kv iv () ectr

val genReader: parent:rid -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 -> HyperHeap.disjoint parent w.region)) //16-04-25  we may need w.region's parent instead
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
  let reader_r = new_region parent in
  if authId i then
    let log : ideal_log w.region i = w.log in
    let dctr: ideal_ctr reader_r i log = new_seqn reader_r 0 log in
    State #i #Reader #reader_r #w.region w.key w.iv w.log dctr
  else
    let dctr: concrete_ctr reader_r i = m_alloc reader_r 0 in
    State #i #Reader #reader_r #w.region w.key w.iv () dctr


// Coerce an instance with index i in a fresh sub-region of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rid -> i:id{~(authId i)} -> kv:key i -> iv:iv i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))
let coerce parent i kv iv =
  let writer_r = new_region parent in
  let ectr: concrete_ctr writer_r i = m_alloc writer_r 0 in
  State #i #Writer #writer_r #writer_r kv iv () ectr


val leak: #i:id{~(authId i)} -> #role:rw -> state i role -> ST (key i * iv i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1))
let leak #i #role s = State.key s, State.iv s


// Encryption of plaintexts; safe instances are idealized
// Returns (nonce_explicit @| cipher @| tag)
// Note that result doesn't include the implicit IV (salt)
// We primarily model the ideal functionality, the concrete code that actually
// runs on the network is what remains after dead code elimination when
// safeId i is fixed to false and after removal of the cryptographic ghost log,
// i.e. all idealization is turned off
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
  	      let ent = Entry c ad p in
  	      let n   = Seq.length (m_sel h0 log) in
  	      m_contains log h1 /\
              witnessed (at_least n ent log) /\
  	      m_sel h1 log == snoc (m_sel h0 log) ent)
  	   )
  ))

#set-options "--z3timeout 100 --max_ifuel 0 --initial_ifuel 0 --max_fuel 0 --initial_fuel 0"

let encrypt #i e ad rg p =
  let ctr = ctr e.counter in
  m_recall ctr;
  let text = if safeId i then createBytes (fst rg) 0z else repr i ad rg p in  
  let n = m_read ctr in      
  lemma_repr_bytes_values n;
  let nonce_explicit = bytes_of_seq n in
  //assert (length nonce_explicit = 8);
  let salt = e.iv in       
  let iv = salt @| nonce_explicit in      
  lemma_repr_bytes_values (length text);
  let ad' = ad @| bytes_of_int 2 (length text) in
  let tlen = targetLength i rg in   
  targetLength_converges i rg;
  cut (within (length text) (cipherRangeClass i tlen));
  targetLength_at_most_max_TLSCiphertext_fragment_length i (cipherRangeClass i tlen);
  let c = nonce_explicit @| aead_encrypt (alg i) e.key iv ad' text in  
  cut (length c == targetLength i rg); 
  if authId i then
    begin
    let log = ilog e.log in
    m_recall log;
    let ictr: ideal_ctr e.region i log = e.counter in
    testify_seqn ictr;
    write_at_end log (Entry c ad p);
    m_recall ictr;
    increment_seqn ictr;
    m_recall ictr
    end
  else
    m_write ctr (n + 1);
  c

val matches: #i:id -> c:cipher i -> adata i -> entry i -> Tot bool
let matches #i c ad (Entry c' ad' _) = c = c' && ad = ad'

// decryption, idealized as a lookup of (c,ad) in the log for safe instances
val decrypt: #i:id -> d:reader i -> ad:adata i -> c:cipher i
  -> ST (option (dplain i ad c))
  (requires (fun h0 -> m_sel h0 (ctr d.counter) + 1 <= max_ctr (alg i)))
  (ensures  (fun h0 res h1 ->
     let ctr_counter_as_hsref = as_hsref (ctr d.counter) in
     let j = m_sel h0 (ctr d.counter) in
     (authId i ==>
       (let log = m_sel h0 (ilog d.log) in
       if j < Seq.length log && matches c ad (Seq.index log j)
       then res = Some (Entry.p (Seq.index log j))
       else res = None))
    /\ (match res with
       | None -> modifies Set.empty h0 h1
       | _    -> modifies_one d.region h0 h1
                /\ modifies_rref d.region !{as_ref ctr_counter_as_hsref} h0.h h1.h
	        /\ m_sel h1 (ctr d.counter) === j + 1)))

#set-options "--z3timeout 100 --max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let decrypt #i d ad c =
  let ctr = ctr d.counter in
  m_recall ctr;
  let j = m_read ctr in
  if authId i then
    let ilog = ilog d.log in
    let log = m_read ilog in
    let ictr: ideal_ctr d.region i ilog = d.counter in
    let _ = testify_seqn ictr in // now we know j <= Seq.length log
    if j < Seq.length log && matches c ad (Seq.index log j) then
      begin
      increment_seqn ictr;
      m_recall ctr;
      Some (Entry.p (Seq.index log j))
      end
    else None
  else // Concrete
    let salt = d.iv in
    let nonce_explicit,c' = split c (aeadRecordIVSize (alg i)) in
    let iv = salt @| nonce_explicit in
    let len = length c' - aeadTagSize (alg i) in
    lemma_repr_bytes_values len;
    let ad' = ad @| bytes_of_int 2 len in
    let p = aead_decrypt (alg i) d.key iv ad' c' in
    match p with
    | None -> None
    | Some text -> 
      let clen = length c in
      let r = cipherRangeClass i clen in
      cipherRangeClass_width i clen;
      // Decryption is probably doing more than it should in checking the content of
      // CCS and Alert fragments
      // TODO: This should be done by StatefulPlain.mk_plain
      if StatefulPlain.parseAD i (LHAEPlain.parseAD ad) = Content.Change_cipher_spec && text <> Content.ccsBytes then
        None
      else if StatefulPlain.parseAD i (LHAEPlain.parseAD ad) = Content.Alert && (length text <> 2 || Platform.Error.is_Error (Alert.parse text)) then
        None
      else
	begin
	m_write ctr (j + 1);
	assert (Range.within (Platform.Bytes.length text) r);
	let plain = mk_plain i ad r text in
        Some plain
	end

(* TODO

- Check that decrypt indeed must use authId and not safeId (like in the F7 code)

- TLS 1.3 simplifies AEAD as follows:
  - the additional data won't include the plaintext length (ad' = ad);
  - there is no "semi-explicit" nonce anymore: we use ctr instead of e.iv @| ctr
    and do not communicate ctr.
*)
