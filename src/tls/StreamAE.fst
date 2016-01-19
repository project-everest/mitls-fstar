
module StreamAE

// Provides authenticated encryption for a stream of variable-length
// plaintexts; concretely, we use AES_GCM but any other algorithm
// would do.

type sid = i:id { isStreamAE i }

val plainRange: sid -> Range.t  // the range of concrete plaintext lengths supported by (alg i)
type plainLen (i:sid) = l:nat { Within l (plainRange i) }  // considered public
type plain (i:sid) 
val plength: i:sid -> plain i -> Tot(plainLen i)
type repr (i:id) (l:plainLen i) = lbytes l  // independent of i, for simplicity

// we may need some WFness condition, e.g. correct padding
val make: i:sid { ~(authId i) } -> r:repr i -> p:plain i { length r = plength p } 
val repr: i:sid { ~(safeId i) } -> p:plain i -> r:repr i { length r = plength p }  

val cipherLen: i:sid -> l:plainLen i -> Tot (cl:nat { cl <= l + 16 })
type cipher (i:id) (l:plainLen i) = lbytes (cipherLen l)

type dplain i (c:bytes) = p:plain i { length c = cipherLen i (plength p) }
type entry (i:id) = | Entry: c:bytes -> dplain i c -> entry i

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

// decryption, idealized as a lookup of (c,ad) in the log for safe instances

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


let decrypt i d ad c =
  recall d.log;
  let log = !d.log in
  if authId i then 
    match seq_find (matches c ad) log with
    | None -> None
    | Some e -> Some (Entry.p e)
  else dec i d ad c





(*
let encrypt i (State #ii #r #region #peer_region log seqn key) p =
  let n = !seqn in
  let l = !log in
  let c = enc AEAD_GCM.encrypt i key empty_bytes (0g f in
  log := snoc l (Entry c p);
  seqn := n + 1;
  c
*)

(* consider turning it into a functor *)

