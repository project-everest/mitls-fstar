(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module AEAD_GCM
#set-options "--max_fuel 1 --initial_fuel 1"
open Platform.Bytes
open Range
open TLSInfo
open FStar.Heap
open FStar.ST

//TODO: require that i.aeAlg is AEAD(aealg,_) ? Note that only AES_128_GCM is supported.

type cipher     = b:bytes{length b <= max_TLSCipher_fragment_length}
(* private *) type key (i:id) = bytes
(* private *) type iv  (i:id) = bytes
type counter    = nat //should be a long

type dplain (i:id) (ad:LHAEPlain.adata i) (c:cipher) =
    LHAEPlain.plain i ad (Range.cipherRangeClass i (length c))

type entry (i:id) =
    | Entry : c:cipher -> ad:LHAEPlain.adata i -> p:dplain i ad c -> entry

type state (i:id) (r:rw) =
    {key     : key i;
     iv      : iv i;
     log     : ref (list (entry id)); // ghost
     counter : ref counter }
// some invariant:
// - the writer counter is the length of the log; the reader counter is lower
// - gen is called at most once for each (i:id), generating distinct refs for each (i:id)
// - the log is monotonic

type encryptor (i:id) = state i Writer
type decryptor (i:id) = state i Reader

// todo: injective allocation table from i to refs
val gen: i:id -> ST (encryptor i * decryptor i)
                (requires (fun h0 -> true))
                (ensures  (fun h0 r h1 -> let (e,d) = r in
                                          Heap.contains h1 e.counter /\ heap.sel h1 e.counter = 0
                                       /\ Heap.contains h1 d.counter /\ heap.sel h1 d.counter = 0
                                       /\ Heap.contains h1 e.log /\ heap.sel h1 e.log = [] /\ e.log = d.log))
                (modifies no_refs)

assume val gen0: i:id -> key i * iv i

let gen i =
  let log = ref [] in
  let kv, iv = gen0 in
  { key = kv; iv = iv; log = log; counter = ref 0 },
  { key = kv; iv = iv; log = log; counter = ref 0 }

// todo:
// assume val coerce: i:id{~(authId i)} -> rw:rw -> bytes -> bytes -> state i (fun _ -> true) rw
// val LEAK:   i:id{not AuthId(i)} -> rw:rw -> (;i,rw)state -> bytes


assume val enc0:
  i:id -> e:encryptor i -> ad:LHAEPlain.adata i -> r:range ->
  p:bytes{Within (length p) r} -> ST cipher
  (requires (fun h -> Heap.contains h e.counter))
  (ensures (fun h0 c h1 -> length c = Range.targetLength i r
                        /\ Heap.contains h1 e.counter
                        /\ Heap.sel h1 e.counter = Heap.sel h0 e.counter + 1)) // do something about overflows
  (modifies (a_ref e.counter))

val enc:
  i:id -> e:encryptor i -> ad:LHAEPlain.adata i -> r:range ->
  p:LHAEPlain.plain i ad r -> ST cipher
  (requires (fun h0 -> Heap.contains h0 e.counter /\ Heap.contains h0 log))
  (ensures  (fun h0 c h1 -> Seq.length c = Range.targetLength i r
                         /\ (safeId i ==> Encrypted i ad c p h1)
                         /\ Heap.contains h1 e.counter /\ Heap.sel h1 e.counter = Heap.sel h0 e.counter + 1
                         /\ Heap.contains h1 e.log) /\ Heap.sel h1 e.log = Entry i c ad p:: Heap.sel h0 e.log)
  (modifies (SomeRefs (Set.union (Set.singleton (Ref e.counter))
                                 (Set.singleton (Ref log)))))

(* only doing ideal stuff for now *)
let enc i state ad rg p =
  if safeId i then
    begin let tlen = targetLength i rg in
          let text = createBytes tlen 0uy in
          lemma_targetLength_converges i rg;
          let c = enc_int i state ad (cipherRangeClass i tlen) text in
          ST.write log (Entry i ad c p::(ST.read log));
          c
    end
  else
    begin let text = LHAEPlain.repr id adata rg p in
          enc_int id state adata rg text
    end

assume val dec_int: i:id -> d:decryptor i -> ad:LHAEPlain.adata i -> c:cipher
                    -> ST (option (dplain i ad c))
                          (requires (fun h -> Heap.contains h d.counter))
                          (ensures (fun h0 dp h1 -> True))
                          (modifies (a_ref d.counter))

(*

// CoreCiphers implicitly supports both values of aealg,
// which only influences the size of the AES key to use.

// NB TLS 1.3 simplifies AEAD as follows:
// - the additional data won't include the plaintext length (ad'=ad);
// - there is no "semi-explicit" nonce anymore: we use ctr instead of e.iv @| ctr
//   and do not communicate ctr.

// failing, why?
let enc_int i e ad r p =
  let ctr = bytes_of_int 8 !e.counter in
  let ad' = ad @| bytes_of_int 2 (length p) in
  let c = ad' @| p in
  //TODO: CoreCiphers_aes_gcm_encrypt e.key (e.iv @| ctr) ad' p in
  e.counter := !e.counter + 1;
  ctr @| c

let dec_int (i:id) d (adata:LHAEPlain.adata) (rg:range) cipher =
    match i.aeAlg with
    | AEAD(aealg,_) ->
       // broken? we should probably use the trusted local state!
       // there is actually no reason to send ctr
       let (ctr,cipher) = split cipher (aeadRecordIVSize aealg) in
       let len = length cipher - aeadTagSize aealg in
       let ad  = adata @| bytes_of_int 2 len in

       match CoreCiphers.aes_gcm_decrypt d.key (d.iv @| ctr) ad cipher with
       | None ->
#if DEBUG
           let reason = perror __SOURCE_FILE__ __LINE__ "" in
#else
           let reason = "" in
#endif
           Error(AD_bad_record_mac, reason)
       | Some p ->
            let plain = LHAEPlain.mk_plain id adata rg p in
            match LHAEPlain.parseExtPad id adata rg plain with
            | Error(x) ->
#if DEBUG
                let reason = perror __SOURCE_FILE__ __LINE__ "" in
#else
                let reason = "" in
#endif
                Error(AD_bad_record_mac, reason)
            | Correct(p) -> Correct(p)
 *)


(* TODO: this one is not currently in the list library ... we should add it there *)
assume val find_mem: #a:Type -> f:(a -> Tot bool) -> l:list a ->
                     Pure (option a)
                          (requires True)
                          (ensures (fun o -> (is_None o ==> (forall x. List.mem x l ==> not (f x)))
                                          /\ (is_Some o ==> (List.mem (Some.v o) l /\ f (Some.v o)))))

val dec:
  i:id -> d:decryptor i -> ad:LHAEPlain.adata i ->
  c:cipher-> ST (option (dplain i ad c))
  (requires (fun h0 -> Heap.contains h0 d.counter /\ Heap.contains h0 d.log))
  (ensures (fun h0 res h1 ->
                         (safeId i ==>
                            ((is_None res ==> (forall p. ~(Encrypted i ad c p h1)))
                          /\ (is_Some res ==> Encrypted i ad c (Some.v res) h1)))))
               (modifies (a_ref d.counter))
let dec i d ad c =
  let res = dec_int i d ad c in
  if safeId i
  then match find_mem (fun (Entry i' ad' c' _) -> i=i' && c=c' && ad=ad') !log with
       | None -> None
       | Some (Entry _ _ _ p) ->  Some p
  else res
