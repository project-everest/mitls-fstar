module QUICStream
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




type plainLen = l:nat{l + v AEAD.taglen <= pow2 32 - 1}

type safeid = i:I.id{Flag.safeId i}

let safeId (i:I.id) = AEAD.safeId i

let safePNE (j:I.id) = PNE.safePNE j

val plain: i:I.id -> l:plainLen -> t:Type0{hasEq t}

val plain_as_bytes : i:I.id -> l:plainLen -> p:plain i l -> GTot (lbytes l)

val mk_plain: i:I.id -> l:plainLen -> b:lbytes l -> p:plain i l{~(AEAD.safeId i) ==> plain_as_bytes i l p == b}

val plain_repr : i:I.id{~(AEAD.safeId i)} -> l:plainLen -> p:plain i l -> b:lbytes l{b == plain_as_bytes i l p}

type cipher (i:I.id) (l:plainLen) = lbytes (l + v AEAD.taglen)

let max_ctr = pow2 62 - 1

let pnlen = n:nat{n=1 \/ n=2 \/ n=4}

val npn: j:I.id -> l:pnlen -> t:Type0{hasEq t}

val npn_as_bytes : j:I.id -> l:pnlen -> n:npn j l -> GTot (lbytes l)

val mk_npn: j:I.id -> l:pnlen -> b:lbytes l -> n:npn j l{~(PNE.safePNE j) ==> npn_as_bytes j l n == b}

val npn_repr : j:I.id{~(PNE.safePNE j)} -> l:pnlen -> n:npn j l -> b:lbytes l{b == npn_as_bytes j l n}

let epn = PNE.epn

type rpn = n:U64.t{U64.v n <= max_ctr}

(*let rpn_of_u32 (j:U32.t) : rpn =
  let jj:nat = U32.v j in
  U64.uint_to_t jj
*)

val npn_encode : (j:I.id) -> (r:rpn) -> (l:pnlen) -> (n:npn j l)

val npn_decode : (#j:I.id) -> (#l:pnlen) -> (n:npn j l) -> (maxpn:rpn) -> rpn


//val npn_inj
//npn_decode



type stream_entry (i:I.id) (j:I.id) =
  | Entry:
    nl:pnlen ->
    pn: rpn ->
    ad:AEAD.adata ->
    #l:plainLen ->
    p:plain i l ->
    ne: epn nl ->
    c:cipher i l ->
    stream_entry i j


val stream_writer: (i:I.id) -> (j:I.id) -> Type0
val stream_reader: #i:I.id -> #j:I.id -> w:stream_writer i j -> Type0

val invariant: #i:I.id -> #j:I.id -> w:stream_writer i j -> mem -> Type0
val rinvariant: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> h:mem -> Type0

val wctrT: #i:I.id -> #j:I.id -> w:stream_writer i j -> mem -> GTot (n:nat{n<=max_ctr})
val wctr: #i:I.id -> #j:I.id -> w:stream_writer i j -> ST rpn
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\ UInt64.v c = wctrT w h1)


val pnlog: #i:I.id -> #j:I.id -> #w: stream_writer i j -> r:stream_reader w -> h:mem ->
  GTot (s:Seq.seq rpn{rinvariant r h /\ safeId i ==> (forall (k:rpn). Seq.mem k s ==> U64.v k <= wctrT w h)})
  
val wlog: #i:safeid -> #j:I.id -> w:stream_writer i j -> h:mem{invariant w h} -> GTot (s:Seq.seq (stream_entry i j)
  {wctrT w h == Seq.length s})

val highest_pnT: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> h:mem ->
  Ghost (option rpn)
  (requires True)
  (ensures fun o ->  
    Some? o ==> 
    (let n:rpn = Some?.v o in
      (rinvariant r h ==> 
        (Seq.mem n (pnlog r h) /\
        (forall (k:rpn). Seq.mem k (pnlog r h) ==> U64.v k <= U64.v n)))))
        
#reset-options "--z3rlimit 50"

val highest_pn: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> ST (option rpn)
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\
    (c == highest_pnT #i #j #w r h0))

let highest_pn_or_zero (#i:I.id) (#j:I.id) (#w:stream_writer i j) (r:stream_reader w) (h:mem) : GTot rpn =
  match highest_pnT r h with
    | None -> U64.uint_to_t 0
    | Some x -> x

let pn_filter (i:I.id) (j:I.id) (ns:Seq.seq rpn) (e:stream_entry i j) : bool =
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


val frame_log: #i:safeid -> #j:I.id -> w:stream_writer i j -> l:Seq.seq (stream_entry i j) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    Flag.safeId i /\
    invariant w h0 /\
    wlog w h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures invariant w h1 ==> wlog w h1 == l)

val frame_pnlog: #i:safeid -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> l:Seq.seq rpn ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    Flag.safeId i /\
    pnlog r h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (rfootprint r)) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures pnlog r h1 == l)

val create: i:I.id -> j:I.id -> u:info i j ->
  ST (stream_writer i j)
  (requires fun h0 -> 
    disjoint u.shared u.local)
  (ensures fun h0 w h1 ->
    invariant w h1 /\
//    footprint w == Set.union (Set.singleton u.local) (Set.singleton u.parent) /\
    shared_footprint w == Set.singleton u.shared /\
    modifies_none h0 h1 /\
    Flag.safeId i ==>
      (wlog w h1 == Seq.empty /\
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
    Flag.safeId i ==>
      (rlog r h1 == Seq.empty /\
      pnlog r h1 == Seq.empty /\
      highest_pnT r h1 == None)
  )



//val rincrementable: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> h:mem -> Type0


val encrypt
  (#i:I.id)
  (#j:I.id)
  (w:stream_writer i j)
  (ad:AEAD.adata)
  (nl:pnlen)
  (l:plainLen)
  (p:plain i l):
  ST ((epn nl) * (cipher i l))
  (requires fun h0 -> wincrementable w h0 /\ invariant w h0)
  (ensures fun h0 (ne,c) h1 ->
    invariant w h1 /\
    wctrT w h1 == wctrT w h0 + 1 /\ 
    (Flag.safeId i ==> (
      let n = U64.uint_to_t (wctrT w h0) in
      wlog w h1 == Seq.snoc (wlog w h0) (Entry nl n ad p ne c))) /\
    modifies (Set.union (footprint w) (shared_footprint w)) h0 h1)

//val adata_of_entry: #i:I.id -> stream_entry i -> GTot AEAD.adata

//val cipher_of_entry: #i:I.id -> stream_entry i -> GTot //(lmax:AEAD.plainLen & c:cipher i lmax)

//let matches (#i:I.id) (e:stream_entry i) (ad:AEAD.adata) (lmax:AEAD.plainLen) (c:cipher i lmax) : GTot bool =
//  let (|lmax', c'|) = cipher_of_entry e in
 //   adata_of_entry e = ad && lmax' = lmax && c' = c


val decrypt
  (#i:I.id)
  (#j:I.id)
  (#w:stream_writer i j)
  (r:stream_reader w)
  (ad:AEAD.adata)
  (#nl:pnlen)
  (ne:epn nl)
  (l:plainLen)
  (c:cipher i l):
  ST (option (plain i l))
  (requires fun h0 -> rinvariant r h0 /\ invariant w h0)
  (ensures fun h0 res h1 ->
    rinvariant r h1 /\
    modifies (Set.union (rfootprint r) (rshared_footprint r)) h0 h1 /\
    (None? res ==> pnlog r h1 == pnlog r h0) /\
    (Flag.safeId i ==> (
      let lg = wlog w h0 in
      match (Seq.find_l (epn_filter i j nl ne) lg) with
        | None -> res = None
        | Some (Entry _ rpn ad' #l' p _ c') ->
          if rpn = npn_decode (npn_encode j rpn nl) (highest_pn_or_zero r h0)
            && ad' = ad && l' = l && c' = c then
              (res = Some p /\ pnlog r h1 == Seq.snoc (pnlog r h0) rpn)
          else
            res = None)))


(*      let npn = 'find nl ne in pnetable' in
      let rpn = 'decode npn maxpn' in
      match 'find rpn in enctable' with
        ne' -> ne' =? ne

      let rpn = 'find nl ne in enctable' in
        rpn =? decode (encode rpn nl) maxpn
*)
