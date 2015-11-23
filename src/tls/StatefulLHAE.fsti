module StatefulLHAE
// Stateful, agile, length-hiding authenticated encryption with additional data
// (implemented by appending a fragment sequence number to the additional data)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found

open Platform.Bytes

open TLSError
open TLSInfo
open Range
open LHAEPlain
open AEAD_GCM
open StatefulPlain

type id = AEAD_GCM.gid //TODO: TEMPORARY, until we add back LHAE 

let snoc = Content.snoc //why can't it go in the library!?
//type cipher = StatefulPlain.cipher
//TODO: this is a workaround for #383 in F* (eta expansion needed for type abbreviations)
type cipher (i:id) = StatefulPlain.cipher i

(* decrypted plaintexts, within a range computed from the cipher length *)
type dplain (i:id) (ad:adata i) (c:cipher i) =
  StatefulPlain.plain i ad (cipherRangeClass i (length c))

type entry (i:id) = (* records that c is an encryption of p with ad *)
  | Entry: c:cipher i -> ad:adata i -> p:dplain i ad c -> entry i

type is_seqn (n:nat) = repr_bytes n <= 8
type seqn_t = n:nat { repr_bytes n <= 8 } 

(* typing the log that specifies StatefulLHAE *)
type st_log_t (r:rid) (i:id) = rref r (s:seq (entry i))

(* typing the private log that specifies LHAE's implementation of StLHAE *)
type gcm_log_t (r:rid) (i:gid) = rref r (s:seq (AEAD_GCM.entry i))
 
type state (i:gid) (rw:rw) 
type reader i = state i Reader
type writer i = state i Writer
val region        : #i:id -> #rw:rw -> state i rw -> Tot rid
val peer_region   : #i:id -> #rw:rw -> state i rw -> Tot rid
let log_region    = fun (#i:id) (#rw:rw) (s:state i rw) -> if rw=Reader then peer_region s else region s
val log           : #i:id -> #rw:rw -> s:state i rw -> Tot (st_log_t (log_region s) i)
val seqn          : #i:id -> #rw:rw -> s:state i rw -> Tot (rref (region s) seqn_t)

opaque type matching (#i:gid) (r:reader i) (w:writer i)

val unfold_matching: #i:id -> r:reader i -> w:writer i ->
  Lemma ( matching r w ==> (
            region r = peer_region w
          /\ region w = peer_region r
          /\ disjoint (region r) (region w)
          /\ log r = log w))

type both (i:gid) = rw:(reader i * writer i){matching (fst rw) (snd rw)}

opaque type st_inv (#i:gid) (r:reader i) (w:writer i) (h:HyperHeap.t) 

val unfold_st_inv: #i:id -> r:reader i -> w:writer i -> h:HyperHeap.t ->
  Lemma ( st_inv r w h ==> (
       matching r w
    /\ Map.contains h (region r)  
    /\ Map.contains h (region w)
    /\ (let log = sel h (log w) in
       let rctr = sel h (seqn r) in 
       let wctr = sel h (seqn w) in 
       wctr = Seq.length log
       /\ rctr <= wctr )))

let regions_of (#i:id) (#rw:rw) (s:state i rw) = 
    Set.union (Set.singleton (region s))
              (Set.singleton (peer_region s))

let refs_in_w (#i:gid) (e:writer i) =
  !{ as_ref (log e), as_ref (seqn e) }

val frame_st_inv: #i:id -> r:reader i -> w:writer i ->  h0:_ -> h1:_ ->
  Lemma (requires st_inv r w h0
                  /\ equal_on (regions_of w) h0 h1)
        (ensures st_inv r w h1)

val gen: reader_parent:rid -> writer_parent:rid -> i:gid -> ST (both i)
  (requires (fun h -> disjoint reader_parent writer_parent))
  (ensures  (fun h0 (rw:both i) h1 ->
      modifies Set.empty h0 h1
    /\ (let r = fst rw in
       let w = snd rw in
      fresh_region (region r) h0 h1
    /\ fresh_region (region w) h0 h1
    /\ extends (region r) reader_parent
    /\ extends (region w) writer_parent
    /\ st_inv r w h1
    /\ sel h1 (log w) = Seq.createEmpty
    /\ sel h1 (seqn r) = 0)))
    
val leak_reader: i:gid{~(safeId i)} -> reader i -> ST bytes
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> modifies Set.empty h0 h1 ))

val leak_writer: i:gid{~(safeId i)} -> writer i -> ST bytes
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> modifies Set.empty h0 h1 ))

val coerce: r0:rid -> p0:rid {disjoint r0 p0} -> role:rw -> i:gid{~(safeId i)} -> kv:key i -> iv:iv i
  -> ST (state i role)
        (requires (fun h -> True))
        (ensures  (fun h0 s h1 ->
          modifies Set.empty h0 h1
          /\ extends (region s) r0
          /\ extends (peer_region s) p0
          /\ fresh_region (region s) h0 h1
          /\ fresh_region (peer_region s) h0 h1
          /\ sel h1 (log s) = Seq.createEmpty
          /\ sel h1 (seqn s) = 0))

opaque type st_enc_inv (#i:gid) (w:writer i) (h:HyperHeap.t) =
  exists (r:reader i).{:pattern (matching r w)} st_inv r w h

val frame_st_enc_inv: #i:id -> w:writer i ->  h0:_ -> h1:_ ->
  Lemma (requires st_enc_inv w h0
                  /\ equal_on (regions_of w) h0 h1)
        (ensures st_enc_inv w h1)

val encrypt: #i:gid -> #ad:adata i
  -> #rg:range{fst rg = snd rg /\ snd rg <= max_TLSPlaintext_fragment_length}
  -> wr:writer i -> f:plain i ad rg -> ST (cipher i)
  (requires (fun h -> st_enc_inv wr h /\ is_seqn (sel h (seqn wr) + 1)))
  (ensures  (fun h0 (c:cipher i) h1 ->
                  st_enc_inv wr h1
                /\ modifies (Set.singleton (region wr)) h0 h1
                /\ modifies_rref (region wr) (refs_in_w wr) h0 h1
                /\ sel h1 (seqn wr) = sel h0 (seqn wr) + 1
                /\ Wider (Range.cipherRangeClass i (length c)) rg
                /\ sel h1 (log wr) = snoc (sel h0 (log wr)) (Entry c ad f)))

opaque type st_dec_inv (#i:gid) (r:reader i) (h:HyperHeap.t) =
  exists (w:writer i).{:pattern (matching r w)} st_inv r w h

val frame_decrypt: #i:id -> rd:reader i -> h0:_ -> h1:_ ->
  Lemma (requires (st_dec_inv rd h0 /\ 
                   equal_on (regions_of rd) h0 h1))
        (ensures st_dec_inv rd h1)
 
(* (\* TODO: Replace Let in prims.fst with this definition? *\) *)
type Let (#a:Type) (=x:a) (body:(y:a{y=x}) -> Type) = body x

val decrypt: #i:gid -> #ad:adata i -> rd:reader i 
  -> c:cipher i{length c > CoreCrypto.aeadTagSize (alg i)} 
  -> ST (option (dplain i ad c))
  (requires (fun h ->
             (authId i ==> st_dec_inv rd h)
           /\ is_seqn (sel h (seqn rd) + 1)))
  (ensures (fun h0 (res:option (dplain i ad c)) h1 ->
               modifies (Set.singleton (region rd)) h0 h1
             /\ modifies_rref (region rd) !{as_ref (seqn rd)} h0 h1
             /\ is_seqn (sel h0 (seqn rd) + 1)
             /\ contains_ref (log rd) h0
             /\ (Let (sel h0 (log rd))  (fun (lg:seq (entry i){lg=sel h0 (log rd)}) -> 
                Let (sel h0 (seqn rd)) (fun (rctr:nat{rctr=sel h0 (seqn rd)}) ->
               authId i
               ==> st_dec_inv rd h0
                /\ st_dec_inv rd h1
                /\ rctr < Seq.length lg
                /\ (if is_Some res
                   then
                    (sel h1 (seqn rd) = rctr + 1
                     /\ Some.v res == Entry.p (Seq.index lg rctr))
                   else
                      Seq.length lg = rctr                 // no more ciphers
                    \/ c <> Entry.c (Seq.index lg rctr)      // wrong cipher
                    \/ ad =!= Entry.ad (Seq.index lg rctr)) // wrong ad
             ))
    )))
