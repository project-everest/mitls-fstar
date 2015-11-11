module StatefulLHAE

// Stateful, agile, length-hiding authenticated encryption with additional data
// (implemented by appending a fragment sequence number to the additional data)

// this interface separates the TLS machinery from its authenticated-encryption schemes
// it also experiments with predicate abstraction (not so clear with heap accesses)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties // for e.g. found

open Platform.Bytes

open TLSError
open TLSInfo
open Range
open StatefulPlain

type id = AEAD_GCM.gid //TODO: TEMPORARY, until we add back LHAE 

type cipher (i:id) = StatefulPlain.cipher i
let snoc = Content.snoc // why can't it go in the library!?

(* decrypted plaintexts, within a range computed from the cipher length *)
type dplain (i:id) (ad:adata i) (c:cipher i) =
    plain i ad (Range.cipherRangeClass i (length c))

type entry (i:id) = (* records that c is an encryption of p with ad *)
  | Entry: c: cipher i -> ad:adata i -> p:dplain i ad c -> entry i

// relocate?
type is_seqn (n:nat) = repr_bytes n <= 8
type seqn = n:nat { repr_bytes n <= 8 }

(* typing the log that specifies StatefulLHAE *)
type st_log_t (r:rid) (i:id) = rref r (s:seq (entry i))

(* CF we might merge those types into State id role *)
type writer (i:id)
val writer_region : #i:id -> writer i   -> Tot rid
val writer_log    : #i:id -> w:writer i -> Tot (st_log_t (writer_region w) i)
val writer_seqn   : #i:id -> w:writer i -> Tot (rref (writer_region w) seqn)

type reader (i:id)
val reader_region : #i:id -> reader i   -> Tot rid
val reader_log    : #i:id -> r:reader i -> Tot (st_log_t (reader_region r) i)
val reader_seqn   : #i:id -> r:reader i -> Tot (rref (reader_region r) seqn)

opaque type matching (#i:id) (r:reader i) (w:writer i)

val public_matching: #i:id -> r:reader i -> w:writer i ->
  Lemma ( matching r w ==> (
            reader_region r = writer_region w
         /\ reader_log r    = writer_log w
         /\ reader_seqn r  <> writer_seqn w ))

type both (i:id) = rw:(reader i * writer i){matching (fst rw) (snd rw)}

opaque type st_inv (#i:id) (d:reader i) (e:writer i) (h:HyperHeap.t)

val public_st_inv: #i:id -> d:reader i -> e:writer i -> h:HyperHeap.t ->
  Lemma ( st_inv d e h ==> (
       matching d e
    /\ Map.contains h (reader_region d)
    /\ Let (sel h (writer_log e)) (fun st ->
       Let (sel h (reader_seqn d)) (fun r ->
       Let (sel h (writer_seqn e)) (fun w ->
         w = Seq.length st /\ r <= w )))))


val gen: r0:rid -> i:id ->
         ST (both i)
            (requires (fun h -> True))
            (ensures (fun h0 (rw:both i) h1 ->
                 modifies Set.empty h0 h1
              /\ fresh_region (reader_region (fst rw)) h0 h1
              /\ extends (reader_region (fst rw)) r0
              /\ st_inv (fst rw) (snd rw) h1
              /\ sel h1 (writer_log (snd rw)) = Seq.createEmpty
              /\ sel h1 (reader_seqn (fst rw)) = 0
              ))

val leak_reader: i:id{~(safeId i)} -> reader i ->
                 ST (bytes)
                    (requires (fun h -> True))
                    (ensures (fun h0 s h1 ->
                         modifies Set.empty h0 h1 ))

val leak_writer: i:id{~(safeId i)} -> writer i ->
                 ST (bytes)
                    (requires (fun h -> True))
                    (ensures (fun h0 s h1 ->
                         modifies Set.empty h0 h1 ))

(*
val coerce_reader: r0:rid -> i:id{~(safeId i)} -> kv:key i -> iv: iv i->
                   ST (reader i)
                      (requires (fun h -> True))
                      (ensures (fun h0 s h1 ->
                           modifies Set.empty h0 h1
                          /\ extends (reader_region s) r0
                          /\ fresh_region (State.region (reader_key s)) h0 h1
                          /\ sel h1 (reader_log s) = Seq.createEmpty
                          /\ sel h1 (reader_seqn s) = 0))

val coerce_writer: r0:rid -> i:id{~(safeId i)} -> kv:key i -> iv: iv i->
                     ST (writer i)
                        (requires (fun h -> True))
                        (ensures (fun h0 s h1 ->
                             modifies Set.empty h0 h1
                            /\ extends (writer_region s) r0
                            /\ fresh_region (State.region (writer_key s)) h0 h1
                            /\ sel h1 (writer_log s) = Seq.createEmpty
                            /\ sel h1 (writer_seqn s) = 0))
*)
opaque type st_enc_inv (#i:id) (e:writer i) (h:HyperHeap.t) = exists (d:reader i). st_inv d e h

val public_st_enc_inv: #i:id -> e:writer i -> h:HyperHeap.t ->
  Lemma ( st_enc_inv e h ==> (
       Let (sel h (writer_log e)) (fun st ->
       Let (sel h (writer_seqn e)) (fun w ->
         w == Seq.length st ))))

let refs_in_e (#i:id) (e:writer i) = !{ as_ref (writer_log e), as_ref (writer_seqn e) }

// let widen #i #ad r0 (r1:_ { Wider r1 r0 }) (f:plain i ad r0) : plain i ad r1 = f 
let widen #i #ad #rg (c:cipher i) (f:plain i ad rg { Wider (Range.cipherRangeClass i (length c)) rg}) : dplain i ad c = 
//  admit();
  f
 

val encrypt:
  #i:id -> #ad:adata i -> #rg:range
  -> wr:writer i
  -> f:plain i ad rg
  -> ST (cipher i)
     (requires (fun h -> st_enc_inv wr h))
//FIXME     (requires (fun h -> st_enc_inv wr h /\ is_seqn (sel h (writer_seqn wr) + 1)))
     (ensures (fun h0 (c:cipher i) h1 ->
                    st_enc_inv wr h1
                /\  HyperHeap.modifies (Set.singleton (writer_region wr)) h0 h1
                /\  Heap.modifies (refs_in_e wr) (Map.sel h0 (writer_region wr))
                                                 (Map.sel h1 (writer_region wr))
                /\  sel h1 (writer_seqn wr) = sel h0 (writer_seqn wr) + 1
                /\  Wider  (Range.cipherRangeClass i (length c)) rg
                /\  sel h1 (writer_log wr)  = snoc (sel h0 (writer_log wr)) (Entry c ad f)))


(* // should be provable from st_enc_inv's footprint *)
(* val frame_encrypt: #i:id -> wr:writer i -> h0:_ -> h1:_ -> *)
(*   Lemma (requires st_enc_inv wr h0 /\  *)
(*                   Map.Equal (restrict (Set.singleton (writer_region wr)) h0) *)
(*                             (restrict (Set.singleton (writer_region wr)) h1)) *)
(*         (ensures st_enc_inv wr h1) *)

opaque type st_dec_inv (#i:id) (d:reader i) (h:HyperHeap.t) = exists (e:writer i). st_inv d e h

(* val frame_decrypt: #i:id -> rd:reader i -> h0:_ -> h1:_ -> *)
(*   Lemma (requires st_dec_inv rd h0 /\  *)
(*                   Map.Equal (restrict (Set.singleton (reader_region rd)) h0) *)
(*                             (restrict (Set.singleton (reader_region rd)) h1)) *)
(*         (ensures st_dec_inv rd h1) *)


//type Let (#a:Type) (=x:a) (body:(y:a{y=x}) -> Type) = body x

val decrypt:
   #i:id
   -> #ad:adata i
   -> rd:reader i
   -> c:cipher i //should be embedded in cipher i : {((length c) > (TLSConstants.aeadTagSize (alg i)))}
   -> ST (option (dplain i ad c))
         (requires (fun h ->
              (safeId i ==> st_dec_inv rd h)
           /\ is_seqn (sel h (reader_seqn rd) + 1)))
         (ensures (fun h0 (res:option (dplain i ad c)) h1 -> True
(* TODO
                 HyperHeap.modifies (Set.singleton (reader_region rd)) h0 h1
              /\ Heap.modifies !{as_ref (reader_seqn rd)} (Map.sel h0 (reader_region rd))
                                                          (Map.sel h1 (reader_region rd))
              /\ is_seqn (sel h0 (reader_seqn rd) + 1)
              /\ Heap.contains (Map.sel h0 (reader_region rd)) (as_ref (reader_log rd))
              /\ Let (sel h0 (reader_log rd))  (fun (log:seq (entry i){log=sel h0 (reader_log rd)}) ->
                 Let (sel h0 (reader_seqn rd)) (fun (rctr:nat{rctr=sel h0 (reader_seqn rd)}) ->
                   (safeId i
                    ==>
                      st_dec_inv rd h0
                      /\ st_dec_inv rd h1
                      /\  (if is_Some res
                           then (sel h1 (reader_seqn rd) = rctr + 1
                                /\ Some.v res == Entry.p (Seq.index log rctr))
                           else ((Seq.length log=rctr                              // no more ciphers
                                  \/ c <> Entry.c (Seq.index log rctr)             // wrong cipher
                                  \/ ad =!= Entry.ad (Seq.index log rctr)))))))
*)
))  // wrong ad
