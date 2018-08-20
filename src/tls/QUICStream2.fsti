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


type plainLen = l:nat{l + v AEAD.taglen <= pow2 32 - 1 /\ l + v AEAD.taglen >= 16}

type safeid = i:I.id{Flag.safeId i}

let safeId (i:I.id) = AEAD.safeId i

let safePNE (j:I.id) = PNE.safePNE j

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

let max_ctr = pow2 62 - 1


(* pn pkg *)
val npn: j:I.id -> l:pnlen -> t:Type0{hasEq t}

val npn_as_bytes : j:I.id -> l:pnlen -> n:npn j l -> GTot (lbytes l)

val mk_npn: j:I.id -> l:pnlen -> b:lbytes l -> n:npn j l{~(PNE.safePNE j) ==> npn_as_bytes j l n == b}

val npn_repr : j:I.id{~(PNE.safePNE j)} -> l:pnlen -> n:npn j l -> b:lbytes l{b == npn_as_bytes j l n}

val npn_from_bytes : j:I.id -> l:pnlen -> b:lbytes l -> GTot (n:npn j l{npn_as_bytes j l n == b}) 

val npn_abs : j:I.id{~(PNE.safePNE j)} -> l:pnlen -> b:lbytes l -> Tot (n:npn j l{n == npn_from_bytes j l b})
  
//let npn_pkg = PNE.PNPkg npn npn_as_bytes npn_repr npn_from_bytes npn_abs

type epn (l:pnlen) = lbytes l

type rpn = n:U64.t{U64.v n <= max_ctr}

let rpn_of_nat (j:nat{j<= max_ctr}) : rpn =
  U64.uint_to_t j


val npn_encode : (j:I.id) -> (r:rpn) -> (l:pnlen) -> (n:npn j l)

val npn_decode : (#j:I.id) -> (#nl:pnlen) -> (n:npn j nl) -> (expected_pn:rpn) -> rpn


val create_nonce : #i:I.id -> #alg:I.cipherAlg{alg == I.cipherAlg_of_id i} ->
  iv: AEAD.iv alg -> nl:pnlen -> r:rpn -> Tot (nonce i nl)


val stream_writer: (i:I.id) -> (j:I.id) -> Type0
val stream_reader: #i:I.id -> #j:I.id -> w:stream_writer i j -> Type0

val writer_aead_state : #i:I.id -> #j:I.id -> w:stream_writer i j ->
  aw:AEAD.aead_writer i
  {(AEAD.wgetinfo aw).AEAD.plain == aead_plain_pkg /\
  (AEAD.wgetinfo aw).AEAD.nonce == aead_nonce_pkg} 

val reader_aead_state : #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w ->
  ar:AEAD.aead_reader (writer_aead_state w)
  {(AEAD.rgetinfo ar).AEAD.plain == aead_plain_pkg /\
  (AEAD.rgetinfo ar).AEAD.nonce == aead_nonce_pkg} 

val writer_pne_state : #i:I.id -> #j:I.id -> w:stream_writer i j -> PNE.pne_state j

val reader_pne_state : #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> PNE.pne_state j

val invariant: #i:I.id -> #j:I.id -> w:stream_writer i j -> h:mem ->
  t:Type0{t ==> AEAD.winvariant (writer_aead_state w) h} 
val rinvariant: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> h:mem ->
  t:Type0{t ==> AEAD.winvariant (writer_aead_state w) h} 

val wctrT: #i:I.id -> #j:I.id -> w:stream_writer i j -> mem -> GTot (n:nat{n<=max_ctr})
val wctr: #i:I.id -> #j:I.id -> w:stream_writer i j -> ST rpn
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\ UInt64.v c = wctrT w h1)

val writer_iv: #i:I.id -> #j:I.id -> w:stream_writer i j -> AEAD.iv (I.cipherAlg_of_id i)
val reader_iv: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w ->
  iv:AEAD.iv (I.cipherAlg_of_id i){iv = writer_iv w}

val expected_pnT: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> h:mem ->
  GTot rpn        

val expected_pn: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> ST rpn
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\
    (c == expected_pnT #i #j #w r h0))

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

let wincrementable (#i:I.id) (#j:I.id) (w:stream_writer i j) (h:mem) =
  wctrT w h < max_ctr

type info' = {
  alg: I.aeadAlg;
  shared: subrgn tls_tables_region;
  local: subrgn tls_tables_region;
  parent: subrgn tls_tables_region;
}

type info (i:I.id) (j:I.id) =
  info:info'{I.aeadAlg_of_id i == info.alg}

val shared_footprint: #i:I.id -> #j:I.id -> w:stream_writer i j -> GTot rset

val footprint: #i:I.id -> #j:I.id -> w:stream_writer i j -> GTot (s:rset{Set.disjoint s (shared_footprint w)})

let rshared_footprint (#i:I.id) (#j:I.id) (#w:stream_writer i j) (r:stream_reader w): GTot rset =
  shared_footprint w

val rfootprint: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> GTot (s:rset{Set.disjoint s (rshared_footprint r)})
 

val frame_invariant: #i:I.id -> #j:I.id -> w:stream_writer i j -> h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    (invariant w h0 /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w))))
  (ensures invariant w h1)

val rframe_invariant: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    (rinvariant r h0 /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (rfootprint r))) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures rinvariant r h1)


val wframe_log: #i:safeid -> #j:I.id -> w:stream_writer i j -> l:Seq.seq (AEAD.entry i (AEAD.wgetinfo (writer_aead_state w))) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    Flag.safeId i /\
    invariant w h0 /\
    AEAD.wlog (writer_aead_state w) h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures invariant w h1 ==> AEAD.wlog (writer_aead_state w) h1 == l)

val rframe_log: #i:safeid -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> l:Seq.seq (AEAD.entry i (AEAD.rgetinfo (reader_aead_state r))) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    Flag.safeId i /\
    invariant w h0 /\
    AEAD.rlog (reader_aead_state r) h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures invariant w h1 ==> AEAD.rlog (reader_aead_state r) h1 == l)


val wframe_pnlog: #i:I.id -> #j:I.id -> w:stream_writer i j -> l:Seq.seq (PNE.entry j) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    Flag.safePNE j /\
    PNE.table (writer_pne_state w) h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures PNE.table (writer_pne_state w) h1 == l)

val rframe_pnlog: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> l:Seq.seq (PNE.entry j) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    Flag.safePNE j /\
    PNE.table (reader_pne_state r) h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (rfootprint r)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures PNE.table (reader_pne_state r) h1 == l)


val create: i:I.id -> j:I.id -> u:info i j ->
  ST (stream_writer i j)
  (requires fun h0 -> 
    disjoint u.shared u.local)
  (ensures fun h0 w h1 ->
    invariant w h1 /\
//    footprint w == Set.union (Set.singleton u.local) (Set.singleton u.parent) /\
    shared_footprint w == Set.singleton u.shared /\
    modifies_none h0 h1 /\
    (Flag.safeId i /\ Flag.safePNE j) ==>
    (AEAD.wlog (writer_aead_state w) h1 == Seq.empty /\
    PNE.table (writer_pne_state w) h1 == Seq.empty /\
    wctrT w h1 == 0)
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

val createReader: parent:rgn -> #i:I.id -> #j:I.id -> w:stream_writer i j ->
  ST (stream_reader w)
  (requires fun h0 -> invariant w h0)
  (ensures fun h0 r h1 ->
    invariant w h1 /\
    rinvariant r h1 /\
    modifies_none h0 h1 /\
    (Flag.safeId i /\ Flag.safePNE j) ==>
//      (AEAD.rlog (reader_aead_state r) h1 == Seq.empty /\
 //     PNE.table (reader_pne_state r) h1 == Seq.empty /\
      expected_pnT r h1 == U64.uint_to_t 0)
  //)



//val rincrementable: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> h:mem -> Type0



val encrypt_pn
  (#i:I.id)
  (#j:I.id)
  (w:stream_writer i j)
  (#l:plainLen)
  (c:cipher i l)
  (nl:pnlen)
  ST (epn nl)
  (requires fun h0 -> wincrementable w h0 /\ invariant w h0)
  (ensures fun h0 ne h1 ->
  
  
    


val encrypt
  (#i:I.id)
  (#j:I.id)
  (w:stream_writer i j)
//  (ad:AEAD.adata)
  (nl:pnlen)
  (l:plainLen)
  (p:plain i l):
  ST ((epn nl) * (cipher i l))
  (requires fun h0 -> wincrementable w h0 /\ invariant w h0)
  (ensures fun h0 res h1 ->
    let ((ne:epn nl),(c:cipher i l)) = res in
    let aw = writer_aead_state w in
    let ps = writer_pne_state w in
    invariant w h1 /\
    wctrT w h1 == wctrT w h0 + 1 /\ 
    ((Flag.safePNE j /\ Flag.safeId i) ==> (
      let rpn = rpn_of_nat (wctrT w h0) in
      let npn = npn_encode j rpn nl in
      let s = PNE.sample_cipher c in
      let alg' = I.cipherAlg_of_aeadAlg ((AEAD.wgetinfo aw).AEAD.alg) in
      let n = create_nonce #i #alg' (writer_iv w) nl rpn in
      let ad = Bytes.empty_bytes in
      AEAD.wlog aw h1 == Seq.snoc (AEAD.wlog aw h0) (AEAD.Entry #i #(AEAD.wgetinfo aw) #nl n ad p c) /\
      PNE.table ps h1 == Seq.snoc (PNE.table ps h0) (PNE.Entry #j s ))) /\
    modifies (Set.union (footprint w) (shared_footprint w)) h0 h1)


//val adata_of_entry: #i:I.id -> stream_entry i -> GTot AEAD.adata

//val cipher_of_entry: #i:I.id -> stream_entry i -> GTot //(lmax:AEAD.plainLen & c:cipher i lmax)

//let matches (#i:I.id) (e:stream_entry i) (ad:AEAD.adata) (lmax:AEAD.plainLen) (c:cipher i lmax) : GTot bool =
//  let (|lmax', c'|) = cipher_of_entry e in
 //   adata_of_entry e = ad && lmax' = lmax && c' = c


#reset-options "--z3rlimit 50"

val decrypt
  (#i:I.id)
  (#j:I.id)
  (#w:stream_writer i j)
  (r:stream_reader w)
//  (ad:AEAD.adata)
  (#nl:pnlen)
  (ne:epn nl)
  (l:plainLen)
  (c:cipher i l):
  ST (option (plain i l))
  (requires fun h0 -> rinvariant r h0 /\ invariant w h0)
  (ensures fun h0 res h1 ->
    let ar = reader_aead_state r in
    let aw = writer_aead_state w in
    let ps = reader_pne_state r in
    rinvariant r h1 /\
    modifies (Set.union (rfootprint r) (rshared_footprint r)) h0 h1 /\
    (None? res ==> expected_pnT r h1 == expected_pnT r h0) /\    
    ((Flag.safePNE j /\ Flag.safeId i) ==> 
      (let s = PNE.sample_cipher c in
      match PNE.entry_for_sample s ps h0 with
        | None -> None? res
        | Some (PNE.Entry _ #nl' ne' npn) ->
          if nl = nl' && ne = ne' then
	    let rpn = npn_decode #j #nl npn (expected_pnT r h0) in
            let alg' = I.cipherAlg_of_aeadAlg ((AEAD.rgetinfo ar).AEAD.alg) in
            let n = create_nonce #i #alg' (reader_iv r) nl rpn in
            match AEAD.wentry_for_nonce aw #nl n h0 with
	      | None -> None? res
	      | Some (AEAD.Entry _  ad' #l' p' c')  -> 
	        if ad' = Bytes.empty_bytes && l' = l && c' = c then 
	          (res = Some p' /\
                  (if U64.v rpn >= U64.v (expected_pnT r h0) && U64.v rpn < max_ctr then
                    expected_pnT r h1 = rpn_of_nat (U64.v rpn + 1)
                  else
                    expected_pnT r h1 = expected_pnT r h0))                  
	        else None? res
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
      let s = PNE.sample_cipher c in
      match PNE.entry_for_sample s (pne_state r) h0 with
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
