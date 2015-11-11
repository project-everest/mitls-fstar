module AEAD_GCM

// AEAD-GCM mode for the TLS record layer, as specified in RFC 5288.
// We support both AES_128_GCM and AES_256_GCM, differing only in their key sizes

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found

open Platform.Bytes
open CoreCrypto          // for algorithm names, and key, IV, tag lengths

open TLSConstants        // for explicit IV length
open TLSInfo
open Range
open LHAEPlain


(* Kept local as adding it to SeqProperties has a negative impact on verification performance *)
val snoc : #a:Type -> seq a -> a -> Tot (seq a)
let snoc s x = Seq.append s (Seq.create 1 x)

type gid = i:id{ is_AEAD i.aeAlg }

let alg (i:gid) = AEAD._0 i.aeAlg

type cipher (i:gid) =
    c:bytes{0 <= length c - aeadRecordIVSize (alg i) - aeadTagSize (alg i) - fixedPadSize i
            /\ length c - aeadRecordIVSize (alg i) - aeadTagSize (alg i) - fixedPadSize i <= max_TLSPlaintext_fragment_length}

// representation lemma -- unused below
val cipherlen2: i:gid -> c:cipher i -> Lemma (repr_bytes (length c) <= 2)
let cipherlen2 i c = lemma_repr_bytes_values (length c)

// key materials for GCM
private type key (i:gid) = lbytes (aeadKeySize (alg i)) 
private type iv  (i:gid) = lbytes (aeadSaltSize (alg i)) // GCMNonce.salt[4]

// this is the same as a sequence number and in bytes, GCMNonce.nonce_explicit[8]
type counter a = c:nat {repr_bytes c <= aeadRecordIVSize a} 

val max_uint64: n:nat {repr_bytes n <= 8} 
let max_uint64 = 
  //let n = 18446744073709551615 in
  let n = 1073741823 in //2^30-1 4611686018427387903 in // (2^62-1) (* TODO: Fix this *)
  lemma_repr_bytes_values n; n

type dplain (i:gid) (ad:adata i) (c:cipher i) = 
  plain i ad (cipherRangeClass i (length c))

type entry (i:gid) = // records that c is an encryption of p with ad
  | Entry: c:cipher i -> ad:adata i -> p:dplain i ad c -> entry i

type state (i:gid) (rw:rw) =
  | State: #region:rid 
           -> #peer_region:rid{HyperHeap.disjoint region peer_region}
           -> key:key i
           -> iv: iv i
           -> log: rref (if rw=Reader then peer_region else region) (seq (entry i))       // ghost subject to cryptographic assumption
           -> counter: rref region (counter (alg i)) // types are sufficient to anti-alias log and counter
           -> state i rw
// Some invariants:
// - the writer counter is the length of the log; the reader counter is lower or equal
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

type writer i = s:state i Writer
type reader i = s:state i Reader

// Generate a fresh instance with index i in a fresh sub-region of r0
// (we can drop this spec, since F* will infer something at least as precise,
// but we keep it for documentation)
val gen: reader_parent:rid -> writer_parent:rid -> i:gid -> ST (reader i * writer i)
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
         /\ op_Equality #(rref w.region (seq (entry i))) w.log r.log  //the explicit annotation here 
         (* /\ w.log == r.log *) //
         (* /\ bang w.counter = 0 *)
         (* /\ bang r.counter = 0 *)
         (* /\ bang w.log = createEmpty *)
         /\ contains_ref w.counter h1
         /\ contains_ref r.counter h1
         /\ contains_ref w.log h1
         /\ sel h1 w.counter = 0
         /\ sel h1 r.counter = 0
         /\ sel h1 w.log = createEmpty
         ))

let gen reader_parent writer_parent i =
  let kv   = CoreCrypto.random (aeadKeySize (alg i)) in
  let iv   = CoreCrypto.random (aeadSaltSize (alg i)) in
  let reader_r = new_region reader_parent in
  let writer_r = new_region writer_parent in
  lemma_repr_bytes_values 0;
  let ectr = ralloc writer_r 0 in
  let dctr = ralloc reader_r 0 in
  let log  = ralloc writer_r Seq.createEmpty in
  let writer  = State #i #Writer #writer_r #reader_r kv iv log ectr in
  let reader  = State #i #Reader #reader_r #writer_r kv iv log dctr in
  reader, writer

// Coerce an instance with index i in a fresh sub-region of r0
val coerce: r0:rid -> p0:rid -> i:gid{~(safeId i)} -> role:rw -> kv:key i -> iv:iv i -> ST (state i role)
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
  let ctr : rref r _ = ralloc r 0 in
  if role=Reader
  then let log : rref p _ = ralloc p Seq.createEmpty in
       State #i #role #r #p kv iv log ctr
  else let log : rref r _ = ralloc r Seq.createEmpty in 
       State #i #role #r #p kv iv log ctr //NS: worryingly, succeeds with implicit arguments even without the role=Writer

val leak: i:gid{~(safeId i)} -> role:rw -> state i role -> ST bytes
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> modifies Set.empty h0 h1 ))

let leak i role s = State.key s @| State.iv s

type encryptor i = writer i
type decryptor i = reader i

// Raw encryption (on concrete bytes), returns (nonce_explicit @| cipher @| tag)
// Requires the counter not to overflow
val enc:
  i:gid -> e:encryptor i -> ad:adata i 
  -> r:range {fst r = snd r /\ snd r <= max_TLSPlaintext_fragment_length}
  -> p:bytes{Within (length p) r} 
  -> ST (cipher i)
    (requires (fun h -> True))
    (ensures  (fun h0 c h1 -> 
                 modifies (Set.singleton e.region) h0 h1
               /\ modifies_rref e.region !{as_ref e.counter} h0 h1
               /\ length c = Range.targetLength i r
               (* /\ sel h1 e.counter = sel h0 e.counter + 1 *) ))

let enc i e ad r p =
  recall e.counter;
  let salt = e.iv in 
  let nonce_explicit = bytes_of_seq !e.counter in
  assert (length nonce_explicit == aeadRecordIVSize (alg i));
  let iv = salt @| nonce_explicit in
  lemma_repr_bytes_values (length p);
  let ad' = ad @| bytes_of_int 2 (length p) in
  let c = aead_encrypt (alg i) e.key iv ad' p in
  let n = !e.counter in
  if n + 1 < max_uint64 then 
    begin
      lemma_repr_bytes_values (n + 1);
      e.counter := n + 1
    end
  else
    begin
      // overflow, we don't care
      lemma_repr_bytes_values 0;
      e.counter := 0
    end;
   Range.targetLength_at_most_max_TLSCipher_fragment_length i r;
   nonce_explicit @| c


// encryption of plaintexts; safe instances are idealized
val encrypt:
  i:gid -> e:encryptor i -> ad:adata i 
  -> r:range{fst r = snd r /\ snd r <= max_TLSPlaintext_fragment_length} 
  -> p:plain i ad r 
  -> ST (cipher i)
       (requires (fun h0 -> True))
       (ensures  (fun h0 c h1 ->
                           modifies (Set.singleton e.region) h0 h1
                         /\ modifies_rref e.region !{as_ref e.counter, as_ref e.log} h0 h1
                         /\ contains_ref e.log h1
                         /\ contains_ref e.counter h1
                         /\ length c = Range.targetLength i r
                         (* /\ sel h1 e.counter = sel h0 e.counter + 1 *)
                         /\ sel h1 e.log = snoc (sel h0 e.log) (Entry c ad p)))

(* we primarily model the ideal functionality, the concrete code that actually
   runs on the network is what remains after dead code elimination when
   safeId i is fixed to false and after removal of the cryptographic ghost log,
   i.e. all idealization is turned off *)
let encrypt i e ad rg p =
  recall e.counter; recall e.log;
  let tlen = targetLength i rg in
  let text = 
    if safeId i then createBytes (fst rg) 0uy
    else repr i ad rg p in
  targetLength_converges i rg;
  let c = enc i e ad (cipherRangeClass i tlen) text in
  e.log := snoc !e.log (Entry c ad p);
  c

// raw decryption (returning concrete bytes)
private val dec: 
  i:gid{~(authId i)} -> d:decryptor i -> ad:adata i -> c:cipher i
  -> ST (option (dplain i ad c))
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> modifies Set.empty h0 h1))

let dec i (d:decryptor i) (ad:adata i) c =
  let k = d.key in
  let salt = d.iv in
  let nonce_explicit,c' = split c (aeadRecordIVSize (alg i)) in 
  let iv = salt @| nonce_explicit in
  let len = length c' - aeadTagSize (alg i) in
  lemma_repr_bytes_values len;
  let ad' = ad @| bytes_of_int 2 len in
  let p = aead_decrypt (alg i) k iv ad' c' in
  match p with
  | None -> None
  | Some text ->
    let clen = length c in
    let r = cipherRangeClass i clen in
    cipherRangeClass_width i clen;
    if StatefulPlain.parseAD i (LHAEPlain.parseAD ad) = Change_cipher_spec && 0 < snd r then
      None
    else
      let plain = mk_plain i ad r text in
      Some plain


val matches: #i:gid -> c:cipher i -> adata i -> entry i -> Tot bool
let matches i c ad (Entry c' ad' _) = c = c' && ad = ad'

// decryption, idealized as a lookup of (c,ad) in the log for safe instances
val decrypt: 
  i:gid -> d:decryptor i -> ad:adata i -> c:cipher i 
  -> ST (option (dplain i ad c))
  (requires (fun h0 -> True))
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


let decrypt i d ad c =
  recall d.log;
  let log = !d.log in
  if authId i then 
    match seq_find (matches c ad) log with
    | None -> None
    | Some e -> Some (Entry.p e)
  else dec i d ad c


(* TODO 

- Check that decrypt indeed must use authId and not safeId (like in the F7 code)

- Decryption doesn't modify the counter (at least in the F7 code), does it? 
  Old specs here suggested so.

- How to handle counter overflows?

- Injective allocation table from i to refs

- Extended padding

- TLS 1.3 simplifies AEAD as follows:
  - the additional data won't include the plaintext length (ad' = ad);
  - there is no "semi-explicit" nonce anymore: we use ctr instead of e.iv @| ctr
    and do not communicate ctr.
*)
