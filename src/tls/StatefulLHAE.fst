module StatefulLHAE
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

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

//type cipher = StatefulPlain.cipher
//TODO: this is a workaround for #383 in F* (eta expansion needed for type abbreviations)
type cipher (i:id) = StatefulPlain.cipher i

(* decrypted plaintexts, within a range computed from the cipher length *)
type dplain (i:id) (ad:adata i) (c:cipher i) =
  StatefulPlain.plain i ad (cipherRangeClass i (length c))

type entry (i:id) = (* records that c is an encryption of p with ad *)
  | Entry: c:cipher i -> ad:adata i -> p:dplain i ad c -> entry i

type is_seqn (n:nat) = repr_bytes n <= 8
type seqn_t = n:nat { repr_bytes n <= 8 } (* NS: REMOVING THIS LINE TRIGGERS A FATAL ERROR WHEN CHECKING writer_seqn *)

(* typing the log that specifies StatefulLHAE *)
type st_log_t (r:rid) (i:id) = rref r (s:seq (entry i))

(* typing the private log that specifies LHAE's implementation of StLHAE *)
type gcm_log_t (r:rid) (i:gid) = rref r (s:seq (AEAD_GCM.entry i))
 
(* CF we might merge those types into State id role *)
abstract type state (i:gid) (rw:rw) = 
  | State :
      #region:rid{region<>root}
    -> peer_region:rid{peer_region <> root 
                        /\ HyperHeap.disjoint region peer_region}
    -> log:  st_log_t (if rw=Reader then peer_region else region) i (* shared ghost spec *)
    -> seqn: rref region seqn_t                                       (* concrete, local sequence number *)
    -> key:  AEAD_GCM.state i rw{extends key.region region /\ extends key.peer_region peer_region} (* gcm in a distinct sub-region *)
    -> state i rw

type reader i = state i Reader
type writer i = state i Writer

abstract val region: #i:id -> #rw:rw -> state i rw -> Tot (r:rid{r<>root})
let region #i #rw s = State.region s

abstract val peer_region: #i:id -> #rw:rw -> state i rw -> Tot (r:rid{r<>root})
let peer_region #i #wr s = s.peer_region

let log_region    = fun (#i:id) (#rw:rw) (s:state i rw) -> if rw=Reader then peer_region s else region s

abstract val log: #i:id -> #rw:rw -> s:state i rw -> Tot (st_log_t (log_region s) i)
let log #i #rw s = s.log

abstract val seqn: #i:id -> #rw:rw -> s:state i rw -> Tot (rref (region s) seqn_t)
let seqn #i #rw s = s.seqn

abstract opaque type matching (#i:gid) (r:reader i) (w:writer i) =
  r.region = w.peer_region
  /\ w.region = r.peer_region
  /\ r.log == w.log
  /\ AEAD_GCM.State.log r.key == AEAD_GCM.State.log w.key //gcmlogs are equal; package this along with pairing of regions one-level lower into another invariant

assume val unfold_matching: #i:id -> r:reader i -> w:writer i ->
  Lemma ( matching r w ==> (
            region r = peer_region w
          /\ region w = peer_region r
          /\ region r <> root
          /\ region w <> root
          /\ disjoint (parent (region r)) (parent (region w))
          /\ log r = log w))

(* CF could we instead compute the derived state? let st i d e h = ... *)
type both (i:gid) = rw:(reader i * writer i){matching (fst rw) (snd rw)}

abstract opaque type st_inv (#i:gid) (r:reader i) (w:writer i) (h:HyperHeap.t) =
    matching r w
  /\ contains_ref w.log h
  /\ contains_ref w.seqn h
  /\ contains_ref r.seqn h
  /\ contains_ref (AEAD_GCM.State.log w.key) h //should get this from an invariant packaged up one level lower
  /\ (let aead = sel h (AEAD_GCM.State.log w.key) in
     let st = sel h w.log in 
     let rseq = sel h r.seqn in 
     let wseq = sel h w.seqn in 
        Seq.length st = Seq.length aead
      /\ wseq = Seq.length st
      /\ rseq <= wseq 
      /\ (forall (j:nat{j < wseq}).{:pattern (found j)}
          Let (Seq.index st j) (fun (st_en:entry i) ->
          found j ==>
            repr_bytes j <= 8 
             /\ Seq.index aead j 
              == AEAD_GCM.Entry st_en.c 
				(LHAEPlain.makeAD i j st_en.ad)
                                st_en.p)))

assume val unfold_st_inv: #i:id -> r:reader i -> w:writer i -> h:HyperHeap.t ->
  Lemma ( st_inv r w h ==> (
       matching r w
    /\ Map.contains h (region r)  
    /\ Map.contains h (region w)
    /\ (let log = sel h (log w) in
       let rctr = sel h (seqn r) in 
       let wctr = sel h (seqn w) in 
       wctr = Seq.length log
       /\ rctr <= wctr )))

private val test_gcm_log_inv: h:HyperHeap.t -> i:gid -> r:reader i -> w:writer i{st_inv r w h} -> n:nat -> j:nat -> c:cipher i -> ad:adata i ->
  Lemma (requires (let gcm_log = sel h (AEAD_GCM.State.log w.key) in
		   j < Seq.length gcm_log
		   /\ repr_bytes n <= 8
		   /\ matches c (LHAEPlain.makeAD i n ad) (Seq.index gcm_log j)))
        (ensures (j = n))
let test_gcm_log_inv h i r w n j c ad = cut(found j)

let regions_of (#i:id) (#rw:rw) (s:state i rw) = 
    Set.union (Set.singleton (region s))
              (Set.singleton (peer_region s))

let refs_in_w (#i:gid) (e:writer i) =
  !{ as_ref (log e), as_ref (seqn e) }

abstract val frame_st_inv: #i:id -> r:reader i -> w:writer i ->  h0:_ -> h1:_ ->
  Lemma (requires st_inv r w h0
                  /\ equal_on (regions_of w) h0 h1)
        (ensures st_inv r w h1)
let frame_st_inv i r w h0 h1 = ()

abstract val gen: reader_parent:rid -> writer_parent:rid -> i:gid -> ST (both i)
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
let gen reader_parent writer_parent i =
  lemma_repr_bytes_values 0;
  ST.recall_region reader_parent;
  ST.recall_region writer_parent;
  let m0 = ST.get() in
  let reader_region = new_region reader_parent in
  let writer_region = new_region writer_parent in
  let m1 = ST.get() in
  lemma_extends_fresh_disjoint reader_region writer_region reader_parent writer_parent m0 m1;
  let r,w = AEAD_GCM.gen reader_region writer_region i in
  let log = ralloc writer_region Seq.createEmpty in
  let r (* : reader i *) = State #i #Reader #reader_region writer_region log (ralloc reader_region 0) r in
  let w (* : writer i *) = State #i #Writer #writer_region reader_region log (ralloc writer_region 0) w in
  r, w

abstract val leak_reader: i:gid{~(safeId i)} -> reader i -> ST bytes
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> modifies Set.empty h0 h1 ))

let leak_reader i rd = AEAD_GCM.leak i Reader rd.key

abstract val leak_writer: i:gid{~(safeId i)} -> writer i -> ST bytes
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> modifies Set.empty h0 h1 ))

let leak_writer i wr = AEAD_GCM.leak i Writer wr.key

abstract val coerce: r0:rid -> p0:rid {disjoint r0 p0} -> role:rw -> i:gid{~(safeId i)} -> kv:key i -> iv:iv i
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
let coerce r0 p0 role i kv iv =
  lemma_repr_bytes_values 0;
  let r = new_region r0 in
  let p = new_region p0 in
  let key = AEAD_GCM.coerce r p i role kv iv in
  let log_region = if role=Reader then p else r in
  let log = ralloc log_region Seq.createEmpty in
  State #i #role #r p log (ralloc r 0) key

opaque type st_enc_inv (#i:gid) (w:writer i) (h:HyperHeap.t) =
  exists (r:reader i).{:pattern (matching r w)} st_inv r w h

abstract val frame_st_enc_inv: #i:id -> w:writer i ->  h0:_ -> h1:_ ->
  Lemma (requires st_enc_inv w h0
                  /\ equal_on (regions_of w) h0 h1)
        (ensures st_enc_inv w h1)
let frame_st_enc_inv i w h0 h1 = ()

abstract val encrypt: #i:gid -> #ad:adata i
  -> #rg:range{fst rg = snd rg /\ snd rg <= max_TLSPlaintext_fragment_length}
  -> wr:writer i -> f:plain i ad rg -> ST (cipher i)
  (requires (fun h -> 
     st_enc_inv wr h /\ 
     is_seqn (sel h (seqn wr) + 1)))
  (ensures  (fun h0 (c:cipher i) h1 ->
                  st_enc_inv wr h1
                /\ modifies (Set.singleton (region wr)) h0 h1
                /\ modifies_rref (region wr) (refs_in_w wr) h0 h1
                /\ sel h1 (seqn wr) = sel h0 (seqn wr) + 1
                /\ Wider (Range.cipherRangeClass i (length c)) rg
                /\ sel h1 (log wr) = snoc (sel h0 (log wr)) (Entry c ad f)))
let encrypt i ad rg (State _ log seqn key) f =
  let n = !seqn in
  let l= !log in
  let ad' = LHAEPlain.makeAD i n ad in
  let c = AEAD_GCM.encrypt i key ad' rg f in
  log := snoc l (Entry c ad f);
  seqn := n + 1;
  c

opaque type st_dec_inv (#i:gid) (r:reader i) (h:HyperHeap.t) =
  exists (w:writer i).{:pattern (matching r w)} st_inv r w h

abstract val frame_st_dec_inv: #i:id -> rd:reader i -> h0:_ -> h1:_ ->
  Lemma (requires (st_dec_inv rd h0 /\ 
                   equal_on (regions_of rd) h0 h1))
        (ensures st_dec_inv rd h1)
let frame_st_dec_inv i rd h0 h1 = ()

(* TODO: Replace Let in prims.fst with this definition? *)
type Let (#a:Type) (=x:a) (body:(y:a{y=x}) -> Type) = body x

abstract val decrypt: #i:gid -> #ad:adata i -> rd:reader i 
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
               ==> 
                  st_dec_inv rd h0
                /\ st_dec_inv rd h1
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

let decrypt i ad (State _ log seqn key) c = 
  recall log; recall seqn; recall (AEAD_GCM.State.log key);
  let h0 = get () in   
  let n = !seqn in
  let ad' = LHAEPlain.makeAD i n ad in
  match AEAD_GCM.decrypt i key ad' c with
     | Some p ->
       seqn := n + 1; 
       Some p
     | None   -> 
       cut (found n);
       None

(*** TODO ***)
(* 
   - calling gen/coerce adds i to the log of existing keys;
     gen can only be called when i is not yet in the log;
     we get this precondition from the freshness of the local nonce in i

   - add overflow protection {is_seqn (length s)})
*)
