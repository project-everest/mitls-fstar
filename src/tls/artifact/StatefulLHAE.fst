(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module StatefulLHAE
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

// Stateful, agile, length-hiding authenticated encryption with additional data
// (implemented by appending a fragment sequence number to the additional data)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
 // for e.g. found

open Platform.Bytes

open TLSError
open TLSInfo
open Range
open LHAEPlain
open AEAD_GCM
open StatefulPlain

type cipher (i:id) = StatefulPlain.cipher i

(* decrypted plaintexts, within a range computed from the cipher length *)
type dplain (i:id) (ad:adata i) (c:cipher i) =
  StatefulPlain.plain i ad (cipherRangeClass i (length c))

type entry (i:id) = (* records that c is an encryption of p with ad *)
  | Entry: c:cipher i -> ad:adata i -> p:dplain i ad c -> entry i

type is_seqn (n:nat) = repr_bytes n <= 8

(* typing the log that specifies StatefulLHAE *)
type st_log_t (r:rid) (i:id) = rref r (s:seq (entry i))

type writer (i:gid) =
  | StWriter:
      #region:rid
    -> log:  st_log_t region i (* shared ghost spec *)
    -> seqn: rref region seqn  (* concrete, local sequence number *)
    -> key:  AEAD_GCM.encryptor i{extends (AEAD_GCM.State?.region key) region} (* gcm in a distinct sub-region *)
    -> writer i

type reader (i:gid) =
  | StReader:
      #region:rid
    -> log:  st_log_t region i (* shared ghost spec *)
    -> seqn: rref region seqn  (* concrete, local sequence number *)
    -> key:  AEAD_GCM.decryptor i{extends (AEAD_GCM.State?.region key) region} (* gcm in a distinct sub-region *)
    -> reader i

opaque type matching (#i:gid) (r:reader i) (w:writer i) =
    StReader.region r = StWriter.region w
  /\ AEAD_GCM.State?.region (StReader.key r) = AEAD_GCM.State?.region (StWriter.key w) // the gcm sub-region is shared
  /\ StReader.log r = StWriter.log w //stlogs are equal
  /\ AEAD_GCM.State?.log (StReader.key r) = AEAD_GCM.State?.log (StWriter.key w) //gcmlogs are equal
  /\ StReader.seqn r <> StWriter.seqn w //read/write sequence counters are distinct

type both (i:gid) = rw:(reader i * writer i){matching (fst rw) (snd rw)}

type st_inv (#i:gid) (d:reader i) (e:writer i) (h:HyperHeap.t) =
    matching d e
  /\ Map.contains h (StReader.region d)
  /\ Let (sel h (AEAD_GCM.State?.log (StWriter.key e))) (fun aead ->
    Let (sel h (StWriter.log e)) (fun st ->
    Let (sel h (StReader.seqn d)) (fun r ->
    Let (sel h (StWriter.seqn e)) (fun w ->
        Seq.length st = Seq.length aead
      /\ w = Seq.length st
      /\ r <= w
      /\ (forall (j:nat{j < w}).
          Let (Seq.index st j) (fun (st_en:entry i) ->
          repr_bytes j <= 8
          /\ Seq.index aead j
            == AEAD_GCM.Entry (Entry?.c st_en) (LHAEPlain.makeAD i j (Entry?.ad st_en))
                              (Entry?.p st_en)))))))

val gen: r0:rid -> i:gid -> ST (both i)
  (requires (fun h -> True))
  (ensures  (fun h0 (rw:both i) h1 ->
      modifies Set.empty h0 h1
    /\ fresh_region (StReader.region (fst rw)) h0 h1
    /\ extends (StReader.region (fst rw)) r0
    /\ st_inv (fst rw) (snd rw) h1
    /\ sel h1 (StWriter.log (snd rw)) = Seq.createEmpty
    /\ sel h1 (StReader.seqn (fst rw)) = 0))

let gen r0 i =
  lemma_repr_bytes_values 0;
  let r = new_region r0 in
  let enc,dec = AEAD_GCM.gen r i in
  let log = ralloc r Seq.createEmpty in
  let rd = StReader log (ralloc r 0) dec in
  let wr = StWriter log (ralloc r 0) enc in
  rd, wr

val leak_reader: i:gid{~(safeId i)} -> reader i -> ST bytes
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> modifies Set.empty h0 h1 ))

let leak_reader i rd = AEAD_GCM.leak i Reader (StReader.key rd)

val leak_writer: i:gid{~(safeId i)} -> writer i -> ST bytes
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 -> modifies Set.empty h0 h1 ))

let leak_writer i wr = AEAD_GCM.leak i Writer (StWriter.key wr)

val coerce_reader: r0:rid -> i:gid{~(safeId i)} -> kv:key i -> iv:iv i -> ST (reader i)
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 ->
      modifies Set.empty h0 h1
    /\ extends (StReader.region s) r0
    /\ fresh_region (State?.region (StReader.key s)) h0 h1
    /\ sel h1 (StReader.log s) = Seq.createEmpty
    /\ sel h1 (StReader.seqn s) = 0))

let coerce_reader r0 i kv iv =
  lemma_repr_bytes_values 0;
  let r = new_region r0 in
  let dec = AEAD_GCM.coerce r i Reader kv iv in
  let log = ralloc r Seq.createEmpty in
  StReader log (ralloc r 0) dec

val coerce_writer: r0:rid -> i:gid{~(safeId i)} -> kv:key i -> iv:iv i -> ST (writer i)
  (requires (fun h -> True))
  (ensures  (fun h0 s h1 ->
      modifies Set.empty h0 h1
    /\ extends (StWriter.region s) r0
    /\ fresh_region (State?.region (StWriter.key s)) h0 h1
    /\ sel h1 (StWriter.log s) = Seq.createEmpty
    /\ sel h1 (StWriter.seqn s) = 0))

let coerce_writer r0 i kv iv =
  lemma_repr_bytes_values 0;
  let r = new_region r0 in
  let enc = AEAD_GCM.coerce r i Writer kv iv in
  let log = ralloc r Seq.createEmpty in
  StWriter log (ralloc r 0) enc

type st_enc_inv (#i:gid) (e:writer i) (h:HyperHeap.t) =
  exists (d:reader i). st_inv d e h

let refs_in_e (#i:gid) (e:writer i) =
  !{ as_ref (StWriter.log e),
     as_ref (StWriter.seqn e) }

val encrypt: #i:gid -> #ad:adata i
  -> #rg:range{fst rg = snd rg /\ snd rg <= max_TLSPlaintext_fragment_length}
  -> wr:writer i -> f:plain i ad rg -> ST (cipher i)
  (requires (fun h -> st_enc_inv wr h /\ is_seqn (sel h (StWriter.seqn wr) + 1)))
  (ensures  (fun h0 (c:cipher i) h1 ->
              st_enc_inv wr h1
            /\ modifies (Set.singleton (StWriter.region wr)) h0 h1
            /\ modifies_rref (StWriter.region wr) (refs_in_e wr) h0 h1
            /\ sel h1 (StWriter.seqn wr) = sel h0 (StWriter.seqn wr) + 1
            /\ wider  (Range.cipherRangeClass i (length c)) rg
            /\ sel h1 (StWriter.log wr) = snoc (sel h0 (StWriter.log wr)) (Entry c ad f)))
let encrypt i ad rg (StWriter #ii #r log seqn key) f =
  let n = !seqn in
  let l= !log in
  let ad' = LHAEPlain.makeAD i n ad in
  let c = AEAD_GCM.encrypt i key ad' rg f in
  log := snoc l (Entry c ad f);
  seqn := n + 1;
  c

type st_dec_inv (#i:gid) (d:reader i) (h:HyperHeap.t) =
  exists (e:writer i). st_inv d e h

type Let (#a:Type) (=x:a) (body:(y:a{y=x}) -> Type) = body x

val decrypt: #i:gid -> #ad:adata i -> rd:reader i
  -> c:cipher i{length c > CoreCrypto.aeadTagSize (alg i)}
  -> ST (option (dplain i ad c))
  (requires (fun h ->
             (authId i ==> st_dec_inv rd h)
           /\ is_seqn (sel h (StReader.seqn rd) + 1)))
  (ensures (fun h0 (res:option (dplain i ad c)) h1 ->
               modifies (Set.singleton (StReader.region rd)) h0 h1
             /\ modifies_rref (StReader.region rd) !{as_ref (StReader.seqn rd)} h0 h1
             /\ is_seqn (sel h0 (StReader.seqn rd) + 1)
             /\ Heap.contains (Map.sel h0 (StReader.region rd)) (as_ref (StReader.log rd))
             /\ Let (sel h0 (StReader.log rd))  (fun (log:seq (entry i){log=sel h0 (StReader.log rd)}) ->
               Let (sel h0 (StReader.seqn rd)) (fun (rctr:nat{rctr=sel h0 (StReader.seqn rd)}) ->
               authId i
               ==> st_dec_inv rd h0
                /\ st_dec_inv rd h1
                /\ (if Some? res
                  then
                    (sel h1 (StReader.seqn rd) = rctr + 1
                     /\ Some?.v res == Entry?.p (Seq.index log rctr))
                  else
                      Seq.length log = rctr                 // no more ciphers
                    \/ c <> Entry?.c (Seq.index log rctr)      // wrong cipher
                    \/ ad =!= Entry?.ad (Seq.index log rctr)) // wrong ad
             ))
    ))

let decrypt i ad rd c =
   let StReader log seqn key = rd in
   recall log; recall seqn; recall (AEAD_GCM.State?.log key);
   let n = !seqn in
   cut (found n);
   let ad' = LHAEPlain.makeAD i n ad in
   match AEAD_GCM.decrypt i key ad' c with
     | Some p -> seqn := n + 1; Some p
     | None   -> None
