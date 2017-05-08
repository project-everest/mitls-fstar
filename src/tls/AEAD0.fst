module AEAD0

// With arbitrary nonces (as long as they are not repeated)
// multiplexing over the constructions of CoreCrypto.aead_cipher
// handling both TLS 1.2 and TLS 1.3 (with implicit IV and noAD)

//16-09-10 adapted from StreamAE and AEAD_GCM.
//16-09-10 consider sharing some AEAD?.Common.fst

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.Monotonic.RRef
open FStar.Monotonic.Seq

open Platform.Error
open Platform.Bytes

open TLSError
open TLSConstants
open TLSInfo
// open AEADPlain 

let ideal = Flags.ideal_AEAD

// floating
private inline let min (a:int) (b:int) = if a < b then a else b
private inline let max (a:int) (b:int) = if a < b then b else a

// The index is treated abstractly, with
// - a local restriction to ensure this is an AEAD index
// - an `alg` function for algorithmic agility (consider making it private)
type id = i:id{ ~(PlaintextID? i) /\ AEAD? (aeAlg_of_id i) }
let alg (i:id) = AEAD?._0 (aeAlg_of_id i)


(*** Key materials and counters ***)

// concrete representations; consider making them abstact!
type key (i:id) = lbytes (CoreCrypto.aeadKeySize (alg i)) 

let fullIVLen (i:id) = CoreCrypto.aeadRealIVSize (alg i)

// The length of the per-record nonce is set to max(8 bytes, N_MIN)
// for the AEAD algorithm (see [RFC5116] Section 4)
let staticIVLen (i:id) = 
  if ID13? i 
  then max 8 (fullIVLen i)
  else TLSConstants.aeadSaltSize (alg i)
type staticIV (i:id) = lbytes (staticIVLen i)


// Sequence numbers, indexing the stream of encryptions 
irreducible let max_seqn (i:id) : Tot nat = pow2 64 - 1
//pow2 (8 * aeadRecordIVSize a) - 1

assume val max_seqn_value: i:id -> Lemma (max_seqn i = 18446744073709551615)

// this is the same as a sequence number and in bytes, GCMNonce.nonce_explicit[8]
type seqn (i:id) = c:nat{c <= max_seqn i} 


// full IV, embedding the salt/static IV plus the sequence number,
// must be unique across all encryptions, used as log index/ 
type iv (i:id) = lbytes (fullIVLen i)


val ivT: i:id -> siv: staticIV i -> n:seqn i -> Tot (iv i)
let ivT i siv n = 
  lemma_repr_bytes_values n;
  max_seqn_value i;
  if ID13? i || alg i = CoreCrypto.CHACHA20_POLY1305 then
    // The per-record nonce for the AEAD construction is formed as follows:
    //
    // 1. The 64-bit record sequence number is padded to the left with zeroes to iv_length.
    //
    // 2. The padded sequence number is XORed with the static client_write_iv or server_write_iv,
    //    depending on the role.
    //
    // The XORing is a fixed, ad hoc, random permutation; not sure what is gained;
    // we can reason about sequence-number collisions before applying it.
    begin
      let extended = bytes_of_int (fullIVLen i) n in
      xor (fullIVLen i) siv extended (* 12 xor 12 bytes *)
    end
  else 
    // Classic, somewhat worse construction for AES_GCM 1.2
    begin
      let explicit = bytes_of_int 8 n in 
      siv @| explicit (* 4 + 8 bytes *)
    end

(* implicit argument trouble; TODO
//let injective #a #b (f: ('a -> Tot 'b)) = forall (x0:'a) (x1:'a). x0 <> x1 ==> f x0 <> f x1

val lemma_ivT: i:id -> siv: staticIV i -> TLSInfo.injective #(seqn i) #(iv i) (ivT i siv)
let lemma_ivT i siv = ()
*)

(*** Plaintexts and ciphertexts ***)

// Plaintexts TBC, represented as bounded bytestrings.
type plainLen = n:nat { n < 1000 } 
assume type plain (i:id) (l:plainLen) // i = b:bytes{ length b < 1000 } 
assume Plain_hasEq: forall i l. hasEq (plain i l) // needs discussion!
assume val repr: #i:id -> #l:plainLen -> p:plain i l -> Tot (lbytes l)
type adata i = b:bytes { 5 < length b /\ length b < 2000 } 

// Cipher, including the tag suffix, but not any explicit IV
let tagLen i : nat = CoreCrypto.aeadTagSize (alg i)
let cipherLen i (l:plainLen) : nat = l + tagLen i
type cipher i (l:plainLen) = lbytes (cipherLen i l)
// TODO reconcile with 
// type cipher (i:id) = c:bytes{ valid_clen i (length c) }, which supported only TLS 1.2

// Presumed plaintext length when decrypting c
let lenCipher i (c:bytes { tagLen i <= length c }) : nat = length c - tagLen i


//16-09-10 causing a lexing error, why? 
//(* ** Ideal State ***) 

// ideal StreamAE maintains a table from sequence numbers to entries
// (we'll need a separate ideal flag to support dynamic compromise)

// type dplain (i:id) (ad:adata i) (c:cipher i) =
//   plain i (cipherRangeClass i (length c))

// records that c is an encryption of p using n and ad
// we don't relate n, seqn, and staticIV yet (as we don't have seqn)
type entry (i:id) (k:key i) =
  | Entry: 
      nonce:iv i -> 
      ad:adata i -> 
      l:plainLen -> p:plain i l ->
      c:cipher i (length (repr p)) {c = CoreCrypto.aead_encryptT (alg i) k nonce ad (repr p)} -> 
      entry i k

let seq_inv (#r:rid) (#i:id) (k:key i) (siv:staticIV i) (s:seq (entry i k)) =
    let l = Seq.length s in
    l <= max_seqn i + 1 /\                                   // no log overflow
    (forall (n:nat). l < l ==> (Seq.index s n).nonce = ivT i siv n) // correct nonces

//16-09-13  This line causes F* to crash
// let ideal_log (r:rid) (i:id) (k:key i) (siv:staticIV i) = i_seq r (entry i k) (seq_inv siv) 

let ideal_log (r:rid) (i:id) (k:key i) (siv:staticIV i) = i_seq r (entry i k) (seq_inv #r #i k siv)

let maybe_log (r:rid) (i:id) (k:key i) (siv:staticIV i): Tot Type0 =
  if ideal then ideal_log r i k siv else unit

// applied to force generalization (?)
let to_maybe_log (#r:rid) (#i:id) (k:key i) (siv:staticIV i) (l:ideal_log r i k siv {ideal}) : maybe_log r i k siv = l

// applied to force the condition within maybe_log
let ilog (#r:rid) (#i:id) (#k:key i) (#siv:staticIV i) 
  (l:maybe_log r i k siv{ideal}) : Tot (ideal_log r i k siv) = l

// concrete sequence numbers are increasing, at most to the min(length log, 2^64-1)
let ideal_seqn (#l:rid) (r:rid) (i:id) (k:key i) (siv:staticIV i) (log:ideal_log l i k siv) : Tot Type0 =
  FStar.Monotonic.Seq.seqn r log (max_seqn i)

let concrete_seqn (r:rid) (i:id): Tot Type0 = m_rref r (seqn i) increases

let maybe_seqn (#l:rid) (r:rid) (i:id) (k:key i) (siv:staticIV i) (log:maybe_log l i k siv) : Tot Type0 =
  if ideal && authId i 
  then ideal_seqn r i k siv (ilog log)
  else m_rref r (seqn i) increases

let mref_seqn (#l:rid) (#r:rid) (#i:id) (#k:key i) (#siv:staticIV i) (#log:maybe_log l i k siv) (c:maybe_seqn r i k siv log)
  : Tot (m_rref r (if ideal && authId i
		   then seqn_val #l #(entry i k) #(seq_inv #l #i k siv) r log (max_seqn i)
		   else seqn i)
		increases) =
  c

// kept concrete for log and counter, but the key and iv should be private.
noeq type state (i:id) (rw:rw) =
  | State: #region: rgn
         -> #log_region: rgn{if rw = Writer then region = log_region else HyperHeap.disjoint region log_region}
         -> key: key i
         -> siv: staticIV i
         -> log: maybe_log log_region i key siv // kept only when idealizing
         -> seqn: maybe_seqn region i key siv log // types are sufficient to anti-alias log and counter
         -> state i rw

type writer i = s:state i Writer
type reader i = s:state i Reader

// We generate first the writer, then the reader (possibly several of them)
let genPost (#i:id) parent h0 (w:writer i) h1 =
  modifies Set.empty h0 h1 /\
  extends w.region parent /\
  fresh_region w.region h0 h1 /\
  color w.region = color parent /\
  (ideal ==> 
    (m_contains (ilog w.log) h1 /\ 
     m_sel h1 (ilog w.log) == createEmpty)) /\
  m_contains (mref_seqn w.seqn) h1 /\
  m_sel h1 (mref_seqn w.seqn) === 0

// Generate a fresh instance with index i in a fresh sub-region of r0
// (we can drop this spec, since F* will infer something at least as precise,
// but we keep it for documentation)
val gen: parent:rid -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))

val genReader: parent:rid -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 -> HyperHeap.disjoint parent w.region)) //16-04-25  we may need w.region's parent instead
  (ensures  (fun h0 (r:reader i) h1 ->
               modifies Set.empty h0 h1 /\
               r.log_region = w.region /\
               extends r.region parent /\
	       color r.region = color parent /\
               fresh_region r.region h0 h1 /\
               w.key = r.key /\
               w.siv = r.siv /\
               eq2 #(maybe_log w.region i w.key w.siv) w.log r.log /\
               m_contains (mref_seqn r.seqn) h1 /\
               m_sel h1 (mref_seqn r.seqn) === 0 ))


// Coerce an instance with index i in a fresh sub-region of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rid -> i:id{~(authId i)} -> kv:key i -> iv:iv i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))

val leak: #i:id{~(authId i)} -> #role:rw -> state i role -> ST (key i * iv i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1))

#set-options "--z3rlimit 10000"
// Encryption of plaintexts; safe instances are idealized
// Returns (nonce_explicit @| cipher @| tag)
// Note that result doesn't include the implicit IV (salt)
// We primarily model the ideal functionality, the concrete code that actually
// runs on the network is what remains after dead code elimination when
// safeId i is fixed to false and after removal of the cryptographic ghost log,
// i.e. all idealization is turned off
val encrypt: #i:id -> e:writer i -> ad:adata i -> l:plainLen -> p:plain i l -> ST (cipher i l)
  (requires (fun h0 -> m_sel h0 (mref_seqn e.seqn) < max_seqn i))
  (ensures  (fun h0 c h1 ->
           let ms = mref_seqn e.seqn in 
           modifies_one e.region h0 h1
	 /\ m_contains ms h1
	 /\ m_sel h1 ms === m_sel h0 ms + 1
      	 /\ (ideal && authId i ==>
	     (let log = ilog e.log in
	      let n   = Seq.length (m_sel h0 log) in
              let nonce = ivT i e.siv n in 
              c = CoreCrypto.aead_encryptT (alg i) e.key nonce ad (repr p) /\ (
	      let ent = Entry nonce ad l p c in
	      m_contains log h1 /\
              witnessed (i_at_least n ent log) /\
	      m_sel h1 log == snoc (m_sel h0 log) ent)
	   )
  )))

(*
type (FStar.Monotonic.RRef.m_rref (AEAD0.State?.log_region e) (FStar.Seq.seq (AEAD0.entry i (AEAD0.State?.key e))) (FStar.Monotonic.Seq.grows ))
type (AEAD0.ideal_log (AEAD0.State?.log_region e) i (AEAD0.State?.key e) (AEAD0.State?.siv e))
*)

val matches: #i:id -> c:cipher i -> adata i -> entry i -> Tot bool
let matches #i c ad (Entry c' ad' _) = c = c' && ad = ad'

// decryption, idealized as a lookup of (c,ad) in the log for safe instances
val decrypt: #i:id -> d:reader i -> ad:adata i -> c:cipher i
  -> ST (option (dplain i ad c))
  (requires (fun h0 -> m_sel h0 (ctr d.counter) + 1 <= max_ctr (alg i)))
  (ensures  (fun h0 res h1 ->
     let j = m_sel h0 (ctr d.counter) in
     (authId i ==>
       (let log = m_sel h0 (ilog d.log) in
       if j < Seq.length log && matches c ad (Seq.index log j)
       then res = Some (Entry?.p (Seq.index log j))
       else res = None))
    /\ (match res with
       | None -> modifies Set.empty h0 h1
       | _    -> modifies_one d.region h0 h1
                /\ modifies_rref d.region (Set.singleton (Heap.addr_of (as_ref (as_rref (ctr d.counter))))) h0 h1
	        /\ m_sel h1 (ctr d.counter) === j + 1)))

(*
let decrypt #i d ad c =
  let ctr = ctr d.counter in
  m_recall ctr;
  let j = m_read ctr in
  if authId i then
    let ilog = ilog d.log in
    let log = m_read ilog in
    let ictr: ideal_ctr d.region i ilog = d.counter in
    let _ = testify_counter ictr in // now we know j <= Seq.length log
    if j < Seq.length log && matches c ad (Seq.index log j) then
      begin
      increment_counter ictr;
      m_recall ctr;
      Some (Entry?.p (Seq.index log j))
      end
    else None
  else // Concrete
    let salt = d.iv in
    let nonce_explicit,c' = split c (aeadRecordIVSize (alg i)) in
    let iv = salt @| nonce_explicit in
    let len = length c' - aeadTagSize (alg i) in
    lemma_repr_bytes_values len;
    let ad' = ad @| bytes_of_int 2 len in
    let p = CoreCrypto.aead_decrypt (alg i) d.key iv ad' c' in
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
      else if StatefulPlain.parseAD i (LHAEPlain.parseAD ad) = Content.Alert && (length text <> 2 || Platform.Error.Error? (Alert.parse text)) then
        None
      else
	begin
	m_write ctr (j + 1);
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


(*** Implementation ***) 

let gen parent i = 
  let kv = CoreCrypto.random (CoreCrypto.aeadKeySize (alg i)) in
  let iv = CoreCrypto.random (iv_length i) in
  let writer_r = new_region parent in
  if authId i then 
    let log : ideal_log writer_r i = alloc_mref_seq writer_r Seq.createEmpty in
    let ectr: ideal_ctr writer_r i log = new_seqn writer_r 0 log in
    State #i #Writer #writer_r #writer_r kv iv log ectr
  else 
    let ectr: concrete_ctr writer_r i = m_alloc writer_r 0 in
    State #i #Writer #writer_r #writer_r kv iv () ectr 


let genReader parent #i w =
  let reader_r = new_region parent in
  if authId i
  then
    let log : ideal_log w.region i = w.log in
    let dctr: ideal_ctr reader_r i log = new_seqn reader_r 0 log in
    State #i #Reader #reader_r #(w.region) w.key w.iv w.log dctr
  else let dctr : concrete_ctr reader_r i = m_alloc reader_r 0 in
    State #i #Reader #reader_r #(w.region) w.key w.iv () dctr


let coerce parent i kv iv =
  let writer_r = new_region parent in
  let ectr: concrete_ctr writer_r i = m_alloc writer_r 0 in
  State #i #Writer #writer_r #writer_r kv iv () ectr 

let leak #i #role s = State?.key s, State?.iv s


// The per-record nonce for the AEAD construction is formed as follows:
//
// 1. The 64-bit record sequence number is padded to the left with zeroes to iv_length.
//
// 2. The padded sequence number is XORed with the static client_write_iv or server_write_iv,
//    depending on the role.
//
// The XORing is a fixed, ad hoc, random permutation; not sure what is gained;
// we can reason about sequence-number collisions before applying it.
let aeIV i (seqn:seqnum) (staticIV:iv i) : lbytes (iv_length i) =
  lemma_repr_bytes_values seqn;
  max_ctr_value ();
  let extended = bytes_of_int (iv_length i) seqn in
  xor (iv_length i) extended staticIV

// we are not relying on additional data
let noAD = empty_bytes

let genReader parent #i w =
  let reader_r = new_region parent in
  if authId i then
    let log : ideal_log w.region i = w.log in
    let dctr: ideal_ctr reader_r i log = new_seqn reader_r 0 log in
    State #i #Reader #reader_r #w.region w.key w.log dctr
  else
    let dctr: concrete_ctr reader_r i = m_alloc reader_r 0 in
    State #i #Reader #reader_r #w.region w.key () dctr


(* we primarily model the ideal functionality, the concrete code that actually
   runs on the network is what remains after dead code elimination when
   safeId i is fixed to false and after removal of the cryptographic ghost log,
   i.e. all idealization is turned off *)
let encrypt #i e l p =
  let ctr = ctr e.seqn in 
  m_recall ctr;
  let text = if safeId i then createBytes l 0z else repr i l p in
  let n = m_read ctr in
  let iv = aeIV i n e.iv in
  let c = CoreCrypto.aead_encrypt (alg i) e.key iv noAD text in
  if authId i then
    begin
    let ilog = ilog e.log in
    m_recall ilog;
    let ictr: ideal_ctr e.region i ilog = e.seqn in
    testify_seqn ictr;
    write_at_end ilog (Entry l c p); //need to extend the log first, before incrementing the seqn for monotonicity; do this only if ideal
    m_recall ictr;
    increment_seqn ictr;
    m_recall ictr
    end
  else
    m_write ctr (n + 1);
  c

// decryption, idealized as a lookup at index d.seq# in the log for safe instances
let decrypt #i d l c =
  let ctr = ctr d.seqn in 
  m_recall ctr;
  let j = m_read ctr in
  if authId i 
  then 
    let ilog = ilog d.log in
    let log  = m_read ilog in
    let ictr: ideal_ctr d.region i ilog = d.seqn in
    let _ = testify_seqn ictr in //now we know that j <= Seq.length log
    if j < Seq.length log && matches l c (Seq.index log j) then
      begin
      increment_seqn ictr;
      m_recall ctr;
      Some (Entry?.p (Seq.index log j))
      end
    else None
  else //concrete
     let iv = aeIV i j d.iv in
     match CoreCrypto.aead_decrypt (alg i) d.key iv noAD c with
     | None -> None
     | Some pr ->
       begin
       match mk_plain i l pr with
       | Some p -> (m_write ctr (j + 1); Some p)
       | None   -> None
       end
*)
