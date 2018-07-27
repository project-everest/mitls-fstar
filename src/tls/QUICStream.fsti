module QUICStream
module HS = FStar.HyperStack 

module I = Crypto.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128
module Plain = Crypto.Plain


open FStar.Bytes
open FStar.UInt32
open Mem
open Pkg




type plainLen = l:nat{l + v AEAD.taglen <= pow2 32 - 1}

type safeid = i:I.id{Flag.safeId i}

let safeId (i:I.id) = AEAD.safeId i

val plain: i:I.id -> l:plainLen -> t:Type0{hasEq t}

val plain_as_bytes : i:I.id -> l:plainLen -> p:plain i l -> GTot (lbytes l)

val mk_plain: i:I.id -> l:plainLen -> b:lbytes l -> p:plain i l{~(AEAD.safeId i) ==> plain_as_bytes i l p == b}

val plain_repr : i:I.id{~(AEAD.safeId i)} -> l:plainLen -> p:plain i l -> b:lbytes l{b == plain_as_bytes i l p}

type cipher (i:I.id) (l:plainLen) = lbytes l

let max_ctr = pow2 32 - 1

let pnlen = PNE.pnlen

val pn: j:I.id -> t:Type0{hasEq t}

val pn_as_bytes : j:I.id -> n:pn j -> GTot (lbytes pnlen)

val mk_pn: j:I.id -> b:lbytes pnlen -> n:pn j{~(PNE.safePNE j) ==> pn_as_bytes j n == b}

val pn_repr : j:I.id{~(PNE.safePNE j)} -> n:pn j -> b:lbytes pnlen{b == pn_as_bytes j n}

type epn = PNE.epn

let pn_as_nat (j:I.id) (n:pn j) : GTot (n:nat{n < pow2 32}) =
  int_of_bytes (pn_as_bytes j n)

type stream_entry (i:I.id) (j:I.id) =
  | Entry:
    pn: pn j ->
    ad:AEAD.adata ->
    #l:plainLen ->
    p:plain i l ->
    ne: epn ->
    c:cipher i l ->
    stream_entry i j


val stream_writer: (i:I.id) -> (j:I.id) -> Type0
val stream_reader: #i:I.id -> #j:I.id -> w:stream_writer i j -> Type0

val invariant: #i:I.id -> #j:I.id -> w:stream_writer i j -> mem -> Type0
val rinvariant: #i:I.id -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> h:mem -> Type0

val wctrT: #i:I.id -> #j:I.id -> w:stream_writer i j -> mem -> GTot nat
val wctr: #i:I.id -> #j:I.id -> w:stream_writer i j -> ST UInt32.t
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\ UInt32.v c = wctrT w h1)

val read_pnT: #i:I.id -> #j:I.id -> #w: stream_writer i j -> r:stream_reader w -> h:mem ->
  GTot (s:Seq.seq (pn j){rinvariant r h /\ safeId i ==> (forall (k:pn j). Seq.mem k s ==> pn_as_nat j k <= wctrT w h)})
  
val read_pn: #i:I.id -> #j:I.id -> #w: stream_writer i j -> r:stream_reader w -> ST (Seq.seq (pn j))
  (requires fun h0 -> True)
  (ensures fun h0 s h1 -> h0 == h1 /\ s == read_pnT r h0)

val wlog: #i:safeid -> #j:I.id -> w:stream_writer i j -> h:mem -> GTot (s:Seq.seq (stream_entry i j)
  {invariant w h ==> wctrT w h == Seq.length s})

let pn_filter (i:I.id) (j:I.id) (ns:Seq.seq (pn j)) (e:stream_entry i j) : bool =
  let n = Entry?.pn e in
  Seq.mem n ns

let epn_filter (i:I.id) (j:I.id) (ne:epn) (e:stream_entry i j) : bool =
  Entry?.ne e = ne
  
let seq_filter (#a:Type) (f:a -> bool) (s:Seq.seq a) : Seq.seq a =
  Seq.seq_of_list #a (List.Tot.filter #a f (Seq.seq_to_list #a s))

let log_filter (#i:safeid) (#j:I.id) (w:stream_writer i j) (h:mem{invariant w h}) (ns:Seq.seq (pn j)) =
  seq_filter (pn_filter i j ns) (wlog w h)

val rlog: #i:safeid -> #j:I.id -> #w:stream_writer i j -> r:stream_reader w -> h:mem{invariant w h /\ rinvariant r h} ->
  GTot (s:Seq.seq (stream_entry i j)
    {s == log_filter w h (read_pnT r h)})



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

val frame_log: #i:I.id -> #j:I.id -> w:stream_writer i j -> l:Seq.seq (stream_entry i j) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    Flag.safeId i /\
//    invariant w h0 ->
    wlog w h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)))
  (ensures wlog w h1 == l)


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
      read_pnT r h1 == Seq.empty)
  )



//val rincrementable: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> h:mem -> Type0


val encrypt
  (#i:I.id)
  (#j:I.id)
  (w:stream_writer i j)
  (ad:AEAD.adata)
  (l:plainLen)
  (p:plain i l):
  ST (epn*(cipher i l))
  (requires fun h0 -> wincrementable w h0 /\ invariant w h0)
  (ensures fun h0 (ne,c) h1 ->
    invariant w h1 /\
    wctrT w h1 == wctrT w h0 + 1 /\ 
    (Flag.safeId i ==> (
      exists (n:pn j). (wlog w h1 == Seq.snoc (wlog w h0) (Entry n ad p ne c) /\ wctrT w h0 == pn_as_nat j n))) /\
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
  (ne:epn)
  (l:plainLen)
  (c:cipher i l):
  ST (option (plain i l))
  (requires fun h0 -> rinvariant r h0 /\ invariant w h0)
  (ensures fun h0 res h1 ->
    rinvariant r h1 /\
    modifies (Set.union (rfootprint r) (rshared_footprint r)) h0 h1 /\
    (None? res ==> read_pnT r h1 == read_pnT r h0) /\
    (Flag.safeId i ==> (
      let lg = wlog w h0 in
      match (Seq.find_l (epn_filter i j ne) lg) with
        | None -> res = None
        | Some (Entry pn ad' #l' p _ c') ->
          if ad' = ad && l' = l && c' = c then
            (res = Some p /\ read_pnT r h1 == Seq.snoc (read_pnT r h0) pn)
          else
            res = None)))
