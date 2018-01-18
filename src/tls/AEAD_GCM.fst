module AEAD_GCM
// AEAD-GCM mode for the TLS record layer, as specified in RFC 5288.
// We support both AES_128_GCM and AES_256_GCM, differing only in their key sizes

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
open Platform.Bytes
open CoreCrypto

open TLSConstants
open TLSInfo
open LHAEPlain

module Range = Range
let range = Range.range
let within = Range.within
let valid_clen = Range.valid_clen
let cipherRangeClass = Range.cipherRangeClass

open FStar.Monotonic.Seq
open FStar.Monotonic.RRef

module AEAD = AEADProvider

type id = i:id{ ID12? i /\ AEAD? (aeAlg_of_id i) }
let alg (i:id) = let AEAD ae _ = aeAlg_of_id i in ae

type cipher (i:id) = c:bytes{ valid_clen i (length c) }

type key (i:id) = AEAD.key i
type iv  (i:id) = AEAD.salt i

irreducible let max_ctr (a:aeadAlg) : Tot (n:nat{n = 18446744073709551615}) =
  assert_norm (pow2 64 - 1 = 18446744073709551615);
  pow2 64 - 1

// this is the same as a sequence number and in bytes, GCMNonce.nonce_explicit[8]
type counter a = c:nat{c <= max_ctr a}

type dplain (i:id) (ad:adata i) (c:cipher i) =
  plain i ad (cipherRangeClass i (length c))

type entry (i:id) = // records that c is an encryption of p with ad
  | Entry: c:cipher i -> ad:adata i -> p:dplain i ad c -> entry i

let ideal_log (r:rgn) (i:id) = log_t r (entry i)

let log_ref (r:rgn) (i:id) : Tot Type0 =
  if authId i then ideal_log r i else unit

let ilog (#r:rgn) (#i:id) (l:log_ref r i{authId i}) : Tot (ideal_log r i) =
  l

(** we have a counter, that's increasing, at most to the min(length log, 2^64-1) *)
let ideal_ctr (#l:rgn) (r:rgn) (i:id) (log:ideal_log l i) : Tot Type0 =
  FStar.Monotonic.Seq.seqn r log (max_ctr (alg i))

let concrete_ctr (r:rgn) (i:id) : Tot Type0 =
  m_rref r (counter (alg i)) increases

let ctr_ref (#l:rgn) (r:rgn) (i:id) (log:log_ref l i) : Tot Type0 =
  if authId i
  then ideal_ctr r i (ilog log)
  else m_rref r (counter (alg i)) increases

#set-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let ctr (#l:rgn) (#r:rgn) (#i:id) (#log:log_ref l i) (c:ctr_ref r i log)
  : Tot (m_rref r (if authId i
		   then seqn_val #l #(entry i) r log (max_ctr (alg i))
		   else counter (alg i))
		increases) =
  c

// kept concrete for log and counter, but the key and iv should be private.
noeq type state (i:id) (rw:rw) =
  | State: #region: rgn
         -> #log_region: rgn{if rw = Writer then region = log_region else HyperHeap.disjoint region log_region}
         -> aead: AEAD.state i rw
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
  disjoint w.region (AEAD.log_region w.aead) /\
  color w.region = color parent /\
  extends (AEAD.region w.aead) parent /\
  stronger_fresh_region (AEAD.region w.aead) h0 h1 /\
  color (AEAD.region w.aead) = color parent /\
  AEAD.empty_log w.aead h1 /\
  (authId i ==> (m_contains (ilog w.log) h1 /\ m_sel h1 (ilog w.log) == createEmpty)) /\
  m_contains (ctr w.counter) h1 /\
  m_sel h1 (ctr w.counter) === 0

// Generate a fresh instance with index i in a fresh sub-region of r0
// (we can drop this spec, since F* will infer something at least as precise,
// but we keep it for documentation)
val gen: parent:rgn -> i:id -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))

(*
 * AR: had to add implicits for etcr.
 *)
let gen parent i =
  let writer_r = new_region parent in
  let aead = AEAD.gen i parent in
  if authId i then
    let log : ideal_log writer_r i = alloc_mref_seq writer_r Seq.createEmpty in
    let ectr: ideal_ctr writer_r i log = new_seqn writer_r 0 log in
    State #i #Writer #writer_r #writer_r aead log ectr
  else
    let ectr: concrete_ctr writer_r i = m_alloc writer_r 0 in
    State #i #Writer #writer_r #writer_r aead () ectr

val genReader: parent:rgn -> #i:id -> w:writer i -> ST (reader i)
  (requires (fun h0 ->
    HyperHeap.disjoint parent w.region /\
    HyperHeap.disjoint parent (AEAD.region w.aead)))
  (ensures  (fun h0 (r:reader i) h1 ->
    modifies Set.empty h0 h1 /\
    r.log_region = w.region /\
    extends r.region parent /\
    color r.region = color parent /\
    stronger_fresh_region r.region h0 h1 /\
    eq2 #(log_ref w.log_region i) w.log r.log /\
    m_contains (ctr r.counter) h1 /\
    m_sel h1 (ctr r.counter) === 0))
let genReader parent #i w =
  let reader_r = new_region parent in
  let wr : rgn = w.region in
  assert(HyperHeap.disjoint wr reader_r);
  let raead = AEAD.genReader parent w.aead in
  if authId i then
    let log : ideal_log w.region i = w.log in
    let dctr: ideal_ctr reader_r i log = new_seqn reader_r 0 log in
    State #i #Reader #reader_r #wr raead w.log dctr
  else
    let dctr: concrete_ctr reader_r i = m_alloc reader_r 0 in
    let wr : rgn = w.log_region in
    State #i #Reader #reader_r #wr raead () dctr


// Coerce an instance with index i in a fresh sub-region of parent
// (coerced readers can then be obtained by calling genReader)
val coerce: parent:rgn -> i:id{~(authId i)} -> kv:key i -> iv:iv i -> ST (writer i)
  (requires (fun h0 -> True))
  (ensures  (genPost parent))
let coerce parent i kv iv =
  assume false; // coerce missing post-condition
  let writer_r = new_region parent in
  let ectr: concrete_ctr writer_r i = m_alloc writer_r 0 in
  let aead = AEAD.coerce i parent kv iv in
  State #i #Writer #writer_r #writer_r aead () ectr


val leak: #i:id{~(authId i)} -> #role:rw -> state i role -> ST (key i * iv i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1))
let leak #i #role s =
  AEAD.leak (State?.aead s)

let lemma_12 (i:id) : Lemma (pv_of_id i <> TLS_1p3) = ()

let concrete_encrypt (#i:id) (e:writer i)
  (n:nat{n <= max_ctr (alg i)}) (ad:adata i)
  (rg:range{fst rg = snd rg /\ snd rg <= max_TLSPlaintext_fragment_length})
  (p:plain i ad rg)
  : ST (cipher i)
  (requires (fun h0 ->
    AEAD.st_inv e.aead h0))
  (ensures (fun h0 c h1 ->
    length c = Range.targetLength i rg /\
    modifies_one (AEAD.log_region e.aead) h0 h1))
  =
  let h = get() in
  let l = fst rg in
  let text = if safeId i then createBytes l 0z else repr i ad rg p in
  lemma_repr_bytes_values n;
  let nb = bytes_of_int (AEAD.noncelen i) n in
  let nonce_explicit, _ = split nb (AEAD.explicit_iv_length i) in
  let iv = AEAD.create_nonce e.aead nb in
  assume(authId i ==> (Flag.prf i /\ AEAD.fresh_iv #i e.aead iv h)); // TODO
  lemma_repr_bytes_values (length text);
  lemma_12 i;
  assert_norm(length ad = 11);
  let ad' = ad @| bytes_of_int 2 (length text) in
  assert(length ad' = 13);
  let tlen = Range.targetLength i rg in
  Range.targetLength_converges i rg;
  cut (within (length text) (cipherRangeClass i tlen));
  Range.targetLength_at_most_max_TLSCiphertext_fragment_length i (cipherRangeClass i tlen);
  nonce_explicit @| AEAD.encrypt #i #l e.aead iv ad' text

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
       (requires (fun h0 ->
         HyperHeap.disjoint e.region (AEAD.log_region e.aead) /\
         m_sel h0 (ctr e.counter) < max_ctr (alg i)))
       (ensures  (fun h0 c h1 ->
        modifies (Set.as_set [e.log_region; AEAD.log_region e.aead]) h0 h1
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

#set-options "--z3rlimit 100 --max_ifuel 1 --initial_ifuel 3 --max_fuel 3 --initial_fuel 3"
let encrypt #i e ad rg p =
  let h0 = get () in
  let ctr = ctr e.counter in
  m_recall ctr;
  let n = m_read ctr in
  assume(AEAD.st_inv e.aead h0);
  let c = concrete_encrypt e n ad rg p in
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
    begin
    m_recall ctr;
    m_write ctr (n + 1)
    end;
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
       then res = Some (Entry?.p (Seq.index log j))
       else res = None))
    /\ (match res with
       | None -> modifies Set.empty h0 h1
       | _    -> modifies_one d.region h0 h1
                /\ modifies_rref d.region (Set.singleton (Heap.addr_of (as_ref ctr_counter_as_hsref))) h0.h h1.h
	        /\ m_sel h1 (ctr d.counter) === j + 1)))

#set-options "--z3rlimit 100 --max_fuel 0 --initial_fuel 1 --initial_ifuel 0 --max_ifuel 1"
let decrypt #i d ad c =
  let ctr = ctr d.counter in
  m_recall ctr;
  if authId i then
    let j = m_read ctr in
    let ilog = ilog d.log in
    let log = m_read ilog in
    let ictr: ideal_ctr d.region i ilog = d.counter in
    let _ = testify_seqn ictr in // now we know j <= Seq.length log
    if j < Seq.length log && matches c ad (Seq.index log j) then
      begin
      increment_seqn ictr;
      m_recall ctr;
      Some (Entry?.p (Seq.index log j))
      end
    else None
  else // Concrete
    // We discard the explicit nonce and use the internal sequence number
    // (ChaCha20 doesn't use the explicit nonce)
    let nb, c' = split c (AEAD.explicit_iv_length i) in
    cut(length nb = AEAD.explicit_iv_length i);
    let j : counter (alg i) = m_read ctr in
    lemma_repr_bytes_values j;
    let iv =
      match AEAD.alg i with
      | CHACHA20_POLY1305 ->
        let nonce = bytes_of_int (AEAD.noncelen i) j in
        AEAD.create_nonce d.aead nonce
      | _ ->
        assume(AEAD.noncelen i = AEAD.explicit_iv_length i); // Should be proved, both = 8
        AEAD.create_nonce d.aead nb in
    let len = length c' - aeadTagSize (alg i) in
    lemma_repr_bytes_values len;
    let ad' = ad @| bytes_of_int 2 len in
    assert(length ad' = 13);
    lemma_ID12 i; // cut(pv_of_id i <> TLS_1p3);
    let ad' : AEAD.adata i = ad' in
    let p = AEAD.decrypt #i #len d.aead iv ad' c' in
    match p with
    | None -> None
    | Some text ->
      let clen = length c in
      let r = cipherRangeClass i clen in
      Range.cipherRangeClass_width i clen;
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
	assert (Range.within (Platform.Bytes.length text) r);
	let plain = mk_plain i ad r text in
        Some plain
	end

(* TODO
- Check that decrypt indeed must use authId and not safeId (like in the F7 code)
*)
