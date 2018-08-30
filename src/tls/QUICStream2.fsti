module QUICStream2
module HS = FStar.HyperStack 

module I = Crypto.Indexing
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module Plain = Crypto.Plain


open FStar.Bytes
open FStar.UInt32
open Mem
open Pkg


let safeQUIC (k:I.id) = Flag.safeQUIC k

type plainLen = l:nat{l + v AEAD.taglen <= pow2 32 - 1}

type safeid = i:I.id{Flag.safeId i}

let safeId (i:I.id) = AEAD.safeId i

let safePNE (j:I.id) = PNE.safePNE j

type qid = I.id*I.id*I.id
  
let safeqid ((i,j,k):qid) = safeId i && safePNE j && safeQUIC k


(* plain pkg *)
val plain: i:I.id -> l:plainLen -> t:Type0{hasEq t}

val plain_as_bytes : i:I.id -> l:plainLen -> p:plain i l -> GTot (lbytes l)

val mk_plain: i:I.id -> l:plainLen -> b:lbytes l -> p:plain i l{~(AEAD.safeId i) ==> plain_as_bytes i l p == b}

val plain_repr : i:I.id{~(AEAD.safeId i)} -> l:plainLen -> p:plain i l -> b:lbytes l{b == plain_as_bytes i l p}

let aead_plain_pkg = AEAD.PlainPkg 0 plain plain_as_bytes plain_repr

(* nonce pkg *)
let pnlen = n:nat{n=1 \/ n=2 \/ n=4}

val nonce (i:I.id) (nl:pnlen) : (t:Type0{hasEq t}) //= AEAD.iv (I.cipherAlg_of_id i)

val nonce_as_bytes (i:I.id) (nl:pnlen) (n:nonce i nl) : GTot (AEAD.iv (I.cipherAlg_of_id i)) //= n

val nonce_repr (i:I.id{~(safeId i)}) (nl:pnlen) (n:nonce i nl) :
  Tot (b:AEAD.iv (I.cipherAlg_of_id i){b == nonce_as_bytes i nl n}) //= n

let aead_nonce_pkg =
  AEAD.NoncePkg pnlen nonce nonce_as_bytes nonce_repr


type cipher (i:I.id) (l:plainLen) = lbytes (l + v AEAD.taglen)


type ciphersample = lbytes 16

let max_ctr = pow2 62 - 1


(* pn pkg *)
val npn: k:I.id -> l:pnlen -> t:Type0{hasEq t}

//val npn_as_bytes : j:I.id -> l:pnlen -> n:npn j l -> GTot (lbytes l)

//val mk_npn: j:I.id -> l:pnlen -> b:lbytes l -> n:npn j l{~(PNE2.safePNE j) ==> npn_as_bytes j l n == b}

//val npn_repr : j:I.id{~(PNE2.safePNE j)} -> l:pnlen -> n:npn j l -> b:lbytes l{b == npn_as_bytes j l n}

//val npn_from_bytes : j:I.id -> l:pnlen -> b:lbytes l -> GTot (n:npn j l{npn_as_bytes j l n == b}) 

//val npn_abs : j:I.id{~(PNE2.safePNE j)} -> l:pnlen -> b:lbytes l -> Tot (n:npn j l{n == npn_from_bytes j l b})
  
//let npn_pkg = PNE.PNPkg npn npn_as_bytes npn_repr npn_from_bytes npn_abs

type epn (l:pnlen) = lbytes l

type rpn = n:U64.t{U64.v n <= max_ctr}

let rpn_of_nat (j:nat{j<= max_ctr}) : rpn =
  U64.uint_to_t j


type epncipher = b:bytes{length b >= 17}

val pre_split_epncipher (nec:epncipher) : b:bytes{length b >= 16}

let concat_epn_cipher
  (#i:I.id) (#nl:pnlen) (ne:epn nl)
  (#l:plainLen{l + v AEAD.taglen + nl <= pow2 32 - 1})
  (c:cipher i l) : 
  nec:epncipher{length nec = l + v AEAD.taglen + nl} =
  Bytes.append ne c

val split_epncipher
  (i:I.id)
  (nl:pnlen)
  (nec:epncipher{length nec >= nl + v AEAD.taglen /\ length nec - nl <= pow2 32 - 1})
  : epn nl * cipher i (length nec - nl - v AEAD.taglen)

(*
val lemma_split_concat (c:ciphil i l) (ne:epn nl) : Lemma
  (split_epncipher i nl (concat_epn_cipher ne c) = (ne,c))
*)

val npn_encode : (k:I.id) -> (r:rpn) -> (l:pnlen) -> (n:npn k l)

val npn_decode : (#k:I.id) -> (#nl:pnlen) -> (n:npn k nl) -> (expected_pn:rpn) -> rpn
// encode (decode n) = n

val encode_decode : (k:I.id) -> (nl:pnlen) -> (npn:npn k nl) -> (expected_pn:rpn) ->
  Lemma
    (requires True)
    (ensures npn_encode k (npn_decode #k #nl npn expected_pn) nl = npn)


val create_nonce : #i:I.id -> #alg:I.cipherAlg{alg == I.cipherAlg_of_id i} ->
  iv: AEAD.iv alg -> nl:pnlen -> r:rpn -> Tot (nonce i nl)


type pne_entry (i:I.id) (k:I.id) =
  | Entry :
    #l:plainLen ->
    c:cipher i l ->
    #nl:pnlen -> 
    ne:epn nl ->
    n:npn k nl ->
    pne_entry i k



val stream_writer: (i:I.id) -> (j:I.id) -> (k:I.id) -> Type0
val stream_reader: #i:I.id -> #j:I.id -> #k:I.id ->  w:stream_writer i j k -> Type0


val writer_aead_state : #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k ->
  aw:AEAD.aead_writer i
  {(AEAD.wgetinfo aw).AEAD.plain == aead_plain_pkg /\
  (AEAD.wgetinfo aw).AEAD.nonce == aead_nonce_pkg} 

val reader_aead_state : #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w ->
  ar:AEAD.aead_reader (writer_aead_state w)
  {(AEAD.rgetinfo ar).AEAD.plain == aead_plain_pkg /\
  (AEAD.rgetinfo ar).AEAD.nonce == aead_nonce_pkg} 

val writer_pne_state : #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> PNE2.pne_state j

val reader_pne_state : #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w -> PNE2.pne_state j

val writer_pne_table: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> h:mem ->
  GTot (Seq.seq (pne_entry i k))

val reader_pne_table: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k ->
  r:stream_reader w -> h:mem -> GTot (s:(Seq.seq (pne_entry i k)){s == writer_pne_table w h})

let cipher_filter (i:I.id) (k:I.id) (l:plainLen) (c:cipher i l) (e:pne_entry i k) : bool =
  Entry?.l e = l && Entry?.c e = c

let entry_for_cipher (#i:I.id) (#j:I.id) (#k:I.id) (#l:plainLen) (c:cipher i l) (w:stream_writer i j k) (h:mem) :
  GTot (option (pne_entry i k)) =
  Seq.find_l (cipher_filter i k l c) (writer_pne_table w h)
  
let fresh_cipher (#i:I.id) (#j:I.id) (#k:I.id) (#l:plainLen) (c:cipher i l) (w:stream_writer i j k) (h:mem) :
  GTot bool =
  None? (entry_for_cipher c w h)

let find_cipher (#i:I.id) (#j:I.id) (#k:I.id) (#l:plainLen) (c:cipher i l) (w:stream_writer i j k) (h:mem) :
  GTot bool =
  Some? (entry_for_cipher c w h)

let cipher_npn_filter (i:I.id) (k:I.id) (l:plainLen) (c:cipher i l) (#nl:pnlen) (n:npn k nl) (e:pne_entry i k) : bool =
  Entry?.l e = l && Entry?.c e = c && Entry?.nl e = nl && Entry?.n e = n

let entry_for_cipher_npn (#i:I.id) (#j:I.id) (#k:I.id) (#l:plainLen) (c:cipher i l) (#nl:pnlen) (n:npn k nl) (w:stream_writer i j k) (h:mem) :
  GTot (option (pne_entry i k)) =
  Seq.find_l (cipher_npn_filter i k l c #nl n) (writer_pne_table w h)
  
let find_cipher_npn (#i:I.id) (#j:I.id) (#k:I.id) (#l:plainLen) (c:cipher i l) (#nl:pnlen) (n:npn k nl) (w:stream_writer i j k) (h:mem) :
  GTot bool =
  Some? (entry_for_cipher_npn c n w h)


let cipher_epn_filter (i:I.id) (k:I.id) (l:plainLen) (c:cipher i l) (#nl:pnlen) (ne:epn nl) (e:pne_entry i k) : bool =
  Entry?.l e = l && Entry?.c e = c && Entry?.nl e = nl && Entry?.ne e = ne

let entry_for_cipher_epn (#i:I.id) (#j:I.id) (#k:I.id) (#l:plainLen) (c:cipher i l) (#nl:pnlen) (ne:epn nl) (w:stream_writer i j k) (h:mem) :
  GTot (option (pne_entry i k)) =
  Seq.find_l (cipher_epn_filter i k l c #nl ne) (writer_pne_table w h)
  
let find_cipher_epn (#i:I.id) (#j:I.id) (#k:I.id) (#l:plainLen) (c:cipher i l) (#nl:pnlen) (ne:epn nl) (w:stream_writer i j k) (h:mem) :
  GTot bool =
  Some? (entry_for_cipher_epn c ne w h)

let epncipher_filter (i:I.id) (k:I.id) (nec:epncipher) (e:pne_entry i k) : bool =
  (Entry?.l e) + (Entry?.nl e) + v AEAD.taglen <= pow2 32 - 1 &&
  nec = concat_epn_cipher (Entry?.ne e) (Entry?.c e)

let entry_for_epncipher (#i:I.id) (#j:I.id) (#k:I.id) (nec:epncipher) (w:stream_writer i j k) (h:mem) :
  GTot (option (pne_entry i k)) =
  Seq.find_l (epncipher_filter i k nec) (writer_pne_table w h)
  
let find_epncipher (#i:I.id) (#j:I.id) (#k:I.id) (nec:epncipher) (w:stream_writer i j k) (h:mem) :
  GTot bool =
  Some? (entry_for_epncipher nec w h)

let sample_cipher c = PNE2.sample_cipher c

val invariant: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> h:mem ->
  t:Type0{t ==> AEAD.winvariant (writer_aead_state w) h} 
val rinvariant: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w -> h:mem ->
  t:Type0{t ==> AEAD.winvariant (writer_aead_state w) h} 

val wctrT: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> mem -> GTot (n:nat{n<=max_ctr})
val wctr: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> ST rpn
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\ UInt64.v c = wctrT w h1)

val writer_iv: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> AEAD.iv (I.cipherAlg_of_id i)
val reader_iv: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w ->
  iv:AEAD.iv (I.cipherAlg_of_id i){iv = writer_iv w}

val expected_pnT: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w -> h:mem ->
  GTot rpn        

val expected_pn: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w -> ST rpn
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\
    (c == expected_pnT #i #j #k #w r h0))

(*let highest_pn_or_zero (#i:I.id) (#j:I.id) (#w:stream_writer i j) (r:stream_reader w) (h:mem) : GTot rpn =
  match highest_pnT r h with
    | None -> U64.uint_to_t 0
    | Some x -> x
*)

(*let pn_filter (i:I.id) (j:I.id) (ns:Seq.seq rpn) (e:stream_entry i j) : bool =
  let n = Entry?.pn e in
  Seq.mem n ns

let epn_filter (i:I.id) (j:I.id) (l:pnlen) (ne:epn l) (e:stream_entry i j) : bool =
  Entry?.nl e = l && Entry?.ne e = ne
  
let seq_filter (#a:Type) (f:a -> bool) (s:Seq.seq a) : Seq.seq a =
  Seq.seq_of_list #a (List.Tot.filter #a f (Seq.seq_to_list #a s))

let log_filter (#i:safeid) (#j:I.id) (w:stream_writer i j) (h:mem{invariant w h}) (ns:Seq.seq rpn) =
  seq_filter (pn_filter i j ns) (wlog w h)

val rlog: #i:safeid -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> h:mem{invariant w h /\ rinvariant r h} ->
  GTot (s:Seq.seq (stream_entry i j)
    {s == log_filter w h (pnlog r h)})
*)

let wincrementable (#i:I.id) (#j:I.id) (#k:I.id) (w:stream_writer i j k) (h:mem) =
  wctrT w h < max_ctr

type info' = {
  alg: I.aeadAlg;
  shared: subrgn tls_tables_region;
  local: subrgn tls_tables_region;
  parent: subrgn tls_tables_region;
}

type info (i:I.id) (j:I.id) (k:I.id) =
  info:info'{I.aeadAlg_of_id i == info.alg}

val shared_footprint: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> GTot rset

val footprint: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> GTot (s:rset{Set.disjoint s (shared_footprint w)})

let rshared_footprint (#i:I.id) (#j:I.id) (#k:I.id) (#w:stream_writer i j k) (r:stream_reader w): GTot rset =
  shared_footprint w

val rfootprint: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w -> GTot (s:rset{Set.disjoint s (rshared_footprint r)})
 

val frame_invariant: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> h0:mem -> s: Set.set rid -> h1:mem ->
  Lemma
  (requires
    (invariant w h0 /\
    modifies s h0 h1 /\
    Set.disjoint s (footprint w) /\
    Set.disjoint s (shared_footprint w)))
  (ensures invariant w h1)

val rframe_invariant: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w -> h0:mem -> s:Set.set rid -> h1:mem ->
  Lemma
  (requires
    (rinvariant r h0 /\
    modifies s h0 h1 /\
    Set.disjoint s (rfootprint r) /\
    Set.disjoint s (shared_footprint w)))
  (ensures rinvariant r h1)


val wframe_log: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> l:Seq.seq (AEAD.entry i (AEAD.wgetinfo (writer_aead_state w))) ->
  h0:mem -> s:Set.set rid -> h1:mem ->
  Lemma
  (requires
    safeId i /\
    invariant w h0 /\
    AEAD.wlog (writer_aead_state w) h0 == l /\
    modifies s h0 h1 /\
    Set.disjoint s (footprint w) /\
    Set.disjoint s (shared_footprint w))
  (ensures invariant w h1 ==> AEAD.wlog (writer_aead_state w) h1 == l)

val rframe_log: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w -> l:Seq.seq (AEAD.entry i (AEAD.rgetinfo (reader_aead_state r))) ->
  h0:mem -> s:Set.set rid -> h1:mem ->
  Lemma
  (requires
    safeId i /\
    invariant w h0 /\
    AEAD.rlog (reader_aead_state r) h0 == l /\
    modifies s h0 h1 /\
    Set.disjoint s (footprint w) /\
    Set.disjoint s (shared_footprint w))
  (ensures invariant w h1 ==> AEAD.rlog (reader_aead_state r) h1 == l)



val wframe_pnlog: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> l:Seq.seq (PNE2.entry j) ->
  h0:mem -> s:Set.set rid -> h1:mem ->
  Lemma
  (requires
    safePNE j /\
    PNE2.table (writer_pne_state w) h0 == l /\
    modifies s h0 h1 /\
    Set.disjoint s (footprint w) /\
    Set.disjoint s (shared_footprint w))
  (ensures PNE2.table (writer_pne_state w) h1 == l)

val rframe_pnlog: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w -> l:Seq.seq (PNE2.entry j) ->
  h0:mem -> s:Set.set rid -> h1:mem ->
  Lemma
  (requires
    safePNE j /\
    PNE2.table (reader_pne_state r) h0 == l /\
    modifies s h0 h1 /\
    Set.disjoint s (rfootprint r) /\
    Set.disjoint s (shared_footprint w))
  (ensures PNE2.table (reader_pne_state r) h1 == l)


val wframe_pnetable: #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k -> l:Seq.seq (pne_entry i k) ->
  h0:mem -> s:Set.set rid -> h1:mem ->
  Lemma
  (requires
    safeQUIC k /\
    invariant w h0 /\
    writer_pne_table w h0 == l /\
    modifies s h0 h1 /\
    Set.disjoint s (footprint w) /\
    Set.disjoint s (shared_footprint w))
  (ensures invariant w h1 ==> writer_pne_table w h1 == l)

val rframe_pnetable: #i:I.id -> #j:I.id -> #k:I.id -> #w:stream_writer i j k -> r:stream_reader w -> l:Seq.seq (pne_entry i k) ->
  h0:mem -> s:Set.set rid -> h1:mem ->
  Lemma
  (requires
    safeQUIC k /\
    invariant w h0 /\
    reader_pne_table r h0 == l /\
    modifies s h0 h1 /\
    Set.disjoint s (footprint w) /\
    Set.disjoint s (shared_footprint w))
  (ensures invariant w h1 ==> reader_pne_table r h1 == l)

val create: i:I.id -> j:I.id -> k:I.id -> u:info i j k ->
  ST (stream_writer i j k)
  (requires fun h0 -> 
    disjoint u.shared u.local)
  (ensures fun h0 w h1 ->
    invariant w h1 /\
//    footprint w == Set.union (Set.singleton u.local) (Set.singleton u.parent) /\
    shared_footprint w == Set.singleton u.shared /\
    modifies_none h0 h1 /\
    (safeqid (i,j,k) ==>
    (AEAD.wlog (writer_aead_state w) h1 == Seq.empty /\
    PNE2.table (writer_pne_state w) h1 == Seq.empty /\
    writer_pne_table w h1 == Seq.empty /\
    wctrT w h1 == 0))
  )

(*val coerce: i:I.id -> u:info i ->
  ST (stream_writer i)
  (requires fun h0 -> 
    ~ (Flag.safeId i) /\ disjoint u.shared u.local)
  (ensures fun h0 w h1 ->
    invariant w h1 /\
    footprint w == Set.singleton u.local /\
    shared_footprint w == Set.singleton u.shared /\
    modifies_none h0 h1)
*)
 
val createReader: parent:rgn -> #i:I.id -> #j:I.id -> #k:I.id -> w:stream_writer i j k ->
  ST (stream_reader w)
  (requires fun h0 -> invariant w h0)
  (ensures fun h0 r h1 ->
    invariant w h1 /\
    rinvariant r h1 /\
    modifies_none h0 h1 /\
    (safeqid (i,j,k) ==>
//      (AEAD.rlog (reader_aead_state r) h1 == Seq.empty /\
 //     PNE2.table (reader_pne_state r) h1 == Seq.empty /\
      expected_pnT r h1 == U64.uint_to_t 0)
 )
  //)



//val rincrementable: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> h:mem -> Type0

(*
pne_table_invariant: all (ne || c) are unique
the invariant is broken when encrypting a new PN which creates a collision
we have to assume this doesn't happen

In implementation:
  if safeQUIC k then
    let ne = random () in
    match find_encipher (concat ne c) with
    | Some _ -> unique_pne_encrypt p h rn ... (*implies pne_table_invariant h1*)
    | None -> (ne, c) (* ne||c is fresh *)

val encrypt_pn:
  (#i:I.id) ->
  (#j:I.id) ->
  (#k:I.id) -> 
  (w:stream_writer i j k) ->
  (#l:plainLen) ->
  (c:cipher i l) ->
  (nl:pnlen) ->
  (n:npn k nl) ->
  ST (epn nl)
  (requires fun h0 -> invariant w h0 /\ fresh_cipher c w h0)
  (ensures fun h0 ne h1 ->
    modifies (footprint w) h0 h1 /\
    invariant w h1 /\
    (safeQUIC k ==> writer_pne_table w h1 == Seq.snoc (writer_pne_table w h0) (Entry c ne n)))



val decrypt_pn :
  (#i:I.id) ->
  (#j:I.id) ->
  (#k:I.id) -> 
  (#w:stream_writer i j k) ->
  (r:stream_reader w) ->
  (nec:epncipher) ->
  ST
    (nl:pnlen{length nec >= nl + v AEAD.taglen} & 
    (npn k nl) * cipher i (length nec - nl - v AEAD.taglen))
  (requires fun h0 ->
    rinvariant r h0 /\
    (safeQUIC k ==> find_epncipher #i #j #k nec w h0))
  (ensures fun h0 (|nl, (n,c)|) h1 -> 
    modifies (Set.singleton (PNE2.footprint (writer_pne_state w))) h0 h1 /\
    rinvariant r h1 /\
    ((safePNE j /\ safeQUIC k)==>
     (match entry_for_epncipher nec w h0 with
       | Some (Entry #_ #_ #l c' #nl' _ n') ->
         nl'=nl /\ n = n' /\
         l = length nec - nl - v AEAD.taglen /\ c' = c)))

*)


val encrypt
  (#i:I.id)
  (#j:I.id)
  (#k:I.id)
  (w:stream_writer i j k)
  (nl:pnlen)
  (l:plainLen)
  (p:plain i l):
  ST ((epn j nl) * (cipher i l))
  (requires fun h0 -> wincrementable w h0 /\ invariant w h0)
  (ensures fun h0 (ne, c) h1 ->
    let aw = writer_aead_state w in
    invariant w h1 /\
    wctrT w h1 == wctrT w h0 + 1 /\ 
    ((Flag.safeQUIC k /\ Flag.safeId i) ==> (
      let rpn = rpn_of_nat (wctrT w h0) in
      let npn' = npn_encode k rpn nl in
      //let s = PNE2.sample_cipher c in
      let alg' = I.cipherAlg_of_aeadAlg ((AEAD.wgetinfo aw).AEAD.alg) in
      let n = create_nonce #i #alg' (writer_iv w) nl rpn in
      let ad = Bytes.empty_bytes in
      AEAD.wlog aw h1 == Seq.snoc (AEAD.wlog aw h0) (AEAD.Entry #i #(AEAD.wgetinfo aw) #nl n ad p c) /\
      writer_pne_table w h1 == Seq.snoc (writer_pne_table w h0) (Entry c ne npn'))) /\
    modifies (Set.union (footprint w) (shared_footprint w)) h0 h1)

(*
Does not work
leak (#nl) (i:I.id) (j:I.id) (e:epn j nl) (c:cipher i) : ST (npn j nl)
  (requires fun h0 -> safeQUIC (i,j) ==> None? (find_pnetable e c))
  =
  if safeQUIC (i,j) then
    let npn = sample () in
    extend npn_table (c, e, npn); npn
  else
    real_decrypt e c
*)

//val adata_of_entry: #i:I.id -> stream_entry i -> GTot AEAD.adata

//val cipher_of_entry: #i:I.id -> stream_entry i -> GTot //(lmax:AEAD.plainLen & c:cipher i lmax)

//let matches (#i:I.id) (e:stream_entry i) (ad:AEAD.adata) (lmax:AEAD.plainLen) (c:cipher i lmax) : GTot bool =
//  let (|lmax', c'|) = cipher_of_entry e in
 //   adata_of_entry e = ad && lmax' = lmax && c' = c


#reset-options "--z3rlimit 50"

val decrypt
  (#i:I.id)
  (#j:I.id)
  (#k:I.id)
  (#w:stream_writer i j k)
  (r:stream_reader w)
//  (ad:AEAD.adata)
  (nec:epncipher):
  ST (option (l:plainLen & plain i l))
  (requires fun h0 -> rinvariant r h0 /\ invariant w h0)
  (ensures fun h0 res h1 ->
    let ar = reader_aead_state r in
    let aw = writer_aead_state w in
 //   let ps = reader_pne_state r in
    rinvariant r h1 /\
    modifies (Set.union (rfootprint r) (rshared_footprint r)) h0 h1 /\
    (None? res ==> expected_pnT r h1 == expected_pnT r h0) /\    
    ((Flag.safeQUIC k /\ Flag.safeId i) ==> 
      (//let s = PNE2.sample_cipher c in
      match entry_for_epncipher nec w h0 with
        | None -> None? res
        | Some (Entry #_ #_ #l c #nl ne npn) ->
	  let rpn = npn_decode #k #nl npn (expected_pnT r h0) in
          let alg' = I.cipherAlg_of_aeadAlg ((AEAD.rgetinfo ar).AEAD.alg) in
          let n = create_nonce #i #alg' (reader_iv r) nl rpn in
          match AEAD.wentry_for_nonce aw #nl n h0 with
	    | None -> None? res
	    | Some (AEAD.Entry _  ad' #l' p' c')  -> 
	      if ad' = Bytes.empty_bytes && l' = l && c' = c then 
	         (res = Some (|l', p'|) /\
                 (if U64.v rpn >= U64.v (expected_pnT r h0) && U64.v rpn < max_ctr then
                   expected_pnT r h1 = rpn_of_nat (U64.v rpn + 1)
                 else
                   expected_pnT r h1 = expected_pnT r h0))                  
	      else None? res
      )
    )
  )

(*)


 (*   (None? res ==> pnlog r h1 == pnlog r h0) /\    
    (Flag.safeId i ==> (
      let lg = wlog w h0 in
      match (Seq.find_l (epn_filter i j nl ne) lg) with
        | None -> res = None
        | Some (Entry _ rpn ad' #l' p _ c') ->
	  let npn = npn_encode j rpn nl in
          if (ad' = ad && l' = l && c' = c then
              (res = Some p /\ pnlog r h1 == Seq.snoc (pnlog r h0) rpn)
          else
            res = None)))
*)
(*
  (Flag.safePNE j ==>
    match entry_for_ne r ne h0 with
    | None -> None? res
    | Some (Entry nl' rpn' ad' l' p' _ c') ->
      if c' = c then
        let npn = 
      else None? res
  | Entry:
    nl:pnlen ->
    pn:rpn ->
    ad:AEAD.adata ->
    #l:plainLen ->
    p:plain i l ->
    ne:epn nl ->
    c:cipher i l ->
    stream_entry i j
*)
(*)
    (Flag.safePNE j ==>
      let s = PNE2.sample_cipher c in
      match PNE2.entry_for_sample s (pne_state r) h0 with
      | None -> None? res
      | Some (Entry _ nl' ne' npn) ->
        if nl = nl' && ne = ne' then
	  let rpn = npn_decode #nl npn (highest_pn_or_zero r h0) in
	  let n = encode_nonce rpn nl static_iv in
	  match AEAD.entry_for_nonce (aead_state r) n h0 with
	  | None -> None? res
	  | Some (_, ad', l', p', c')  ->
	    if ad' = empty_bytes && l' = l && c' = c then
	      res = Some p'
	    else None? res
	else None? res

(*      let npn = 'find nl ne in pnetable' in
      let rpn = 'decode npn maxpn' in
      match 'find rpn in enctable' with
        ne' -> ne' =? ne

      let rpn = 'find nl ne in enctable' in
        rpn =? decode (encode rpn nl) maxpn
*)

(*
N(nl, rpn) = encode(nl)<<62 + rpn

N(nl1, rpn1) = N(nl2, rpn2) ==> nl1 = nl2 /\ rpn1 = rpn2

decode(npn, nl, highest_pn) = (highest_pn & ~nl) | npn

y-2^(8*len(x)-1) < decode x y < y + 2^(8*len(x)-1)
