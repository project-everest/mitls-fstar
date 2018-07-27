module StreamAE
module HS = FStar.HyperStack 

module I = Crypto.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128
module Plain = Crypto.Plain


open FStar.Bytes
open FStar.UInt32
open Mem
open Pkg


type plainLen = l:nat{l + v AEAD.taglen < pow2 32 - 1}

type safeid = i:I.id{Flag.safeId i}

let safeId (i:I.id) = AEAD.safeId i

type llbytes (lmax:nat) = b:bytes{length b <= lmax}

val plain: i:I.id -> lmax:plainLen -> t:Type0{hasEq t}

val as_bytes : i:I.id -> lmax:plainLen -> p:plain i lmax -> GTot (llbytes lmax)

val mk_plain: i:I.id -> lmax:plainLen -> b:llbytes lmax -> p:plain i lmax{~(AEAD.safeId i) ==> as_bytes i lmax p == b}

val repr : i:I.id{~(AEAD.safeId i)} -> lmax:plainLen -> p:plain i lmax -> b:llbytes lmax{b == as_bytes i lmax p}

type cipher (i:I.id) (lmax:plainLen) = lbytes (lmax + U32.v (AEAD.taglen) + 1)


let max_ctr = pow2 32 - 1

//val stream_entry : i:I.id -> Type0
type stream_entry (i:I.id) =
  | Entry:
    ad:AEAD.adata ->
    #lmax:plainLen ->
    p:plain i lmax ->
    c:cipher i lmax ->
    stream_entry i

(*
val mk_entry (#i:I.id) :
    ad:AEAD.adata ->
    #lmax:AEAD.plainLen ->
    p:plain i lmax ->
    c:cipher i lmax ->
    stream_entry i
*)

//val stream_state: I.id -> I.rw -> Type0

val stream_writer: (i:I.id) -> Type0
val stream_reader: #i:I.id -> w:stream_writer i -> Type0

val invariant: #i:I.id -> w:stream_writer i -> mem -> Type0
val rinvariant: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> h:mem -> Type0

val wctrT: #i:I.id -> w:stream_writer i -> mem -> GTot nat
val wctr: #i:I.id -> w:stream_writer i -> ST UInt32.t
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\ UInt32.v c = wctrT w h1)

val rctrT: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> h:mem ->
  GTot (n:nat{(rinvariant r h /\ safeId i) ==> n <= wctrT w h})
val rctr: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> ST UInt32.t
  (requires fun h0 -> True)
  (ensures fun h0 c h1 -> h0 == h1 /\ UInt32.v c = rctrT r h1)

val wlog: #i:safeid -> w:stream_writer i -> h:mem -> GTot (s:Seq.seq (stream_entry i)
  {invariant w h ==> wctrT w h == Seq.length s})

let prefix (#i:safeid) (w:stream_writer i) (h:mem{invariant w h}) (k:nat{k <= wctrT w h}) =
  Seq.Base.slice (wlog w h) 0 k

val rlog: #i:safeid -> #w:stream_writer i -> r:stream_reader w -> h:mem{invariant w h /\ rinvariant r h} ->
  GTot (s:Seq.seq (stream_entry i)
    {s == prefix w h (rctrT r h)})



let wincrementable (#i:I.id) (w:stream_writer i) (h:mem) =
  wctrT w h < max_ctr


let rincrementable (#i:I.id) (#w:stream_writer i) (r:stream_reader w) (h:mem) =
  rctrT r h < max_ctr



(*
val ctrT: #i:I.id -> #rw:I.rw -> wr:stream_state i rw -> mem -> GTot UInt32.t

val log: #i:I.id -> #rw:I.rw -> wr:stream_state i rw -> h:mem -> GTot (s:Seq.seq (stream_entry i){UInt32.v (ctrT wr h) == Seq.length s})

let log_inv (#i:I.id) (rw:stream_state i) (h:mem) =
    log (rw Reader) h == prefix (log (rw Writer) h) (ctrT (rw Reader) h) 

val invariant: #i:I.id -> #rw:I.rw -> stream_state i rw -> mem -> Type0
*)


type info' = {
  alg: I.aeadAlg;
  shared: subrgn tls_tables_region;
  local: subrgn tls_tables_region;
  parent: subrgn tls_tables_region;
}

type info (i:I.id) =
  info:info'{I.aeadAlg_of_id i == info.alg}

val shared_footprint: #i:I.id -> w:stream_writer i -> GTot rset

val footprint: #i:I.id -> w:stream_writer i -> GTot (s:rset{Set.disjoint s (shared_footprint w)})

let rshared_footprint (#i:I.id) (#w:stream_writer i) (r:stream_reader w): GTot rset =
  shared_footprint w

val rfootprint: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> GTot (s:rset{Set.disjoint s (rshared_footprint r)})
 

val frame_invariant: #i:I.id -> w:stream_writer i -> h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    (invariant w h0 /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)) /\
    ~(Set.mem ri (shared_footprint w))))
  (ensures invariant w h1)

val rframe_invariant: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    (rinvariant r h0 /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (rfootprint r))) /\
    ~(Set.mem ri (shared_footprint w)))
  (ensures rinvariant r h1)

val frame_log: #i:I.id -> w:stream_writer i -> l:Seq.seq (stream_entry i) ->
  h0:mem -> ri:rid -> h1:mem ->
  Lemma
  (requires
    Flag.safeId i /\
//    invariant w h0 ->
    wlog w h0 == l /\
    modifies_one ri h0 h1 /\
    ~(Set.mem ri (footprint w)))
  (ensures wlog w h1 == l)


val create: i:I.id -> u:info i ->
  ST (stream_writer i)
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

val coerce: i:I.id -> u:info i ->
  ST (stream_writer i)
  (requires fun h0 -> 
    ~ (Flag.safeId i) /\ disjoint u.shared u.local)
  (ensures fun h0 w h1 ->
    invariant w h1 /\
    footprint w == Set.singleton u.local /\
    shared_footprint w == Set.singleton u.shared /\
    modifies_none h0 h1)


val createReader: parent:rgn -> #i:I.id -> w:stream_writer i ->
  ST (stream_reader w)
  (requires fun h0 -> invariant w h0)
  (ensures fun h0 r h1 ->
    invariant w h1 /\
    rinvariant r h1 /\
    modifies_none h0 h1 /\
    Flag.safeId i ==>
      (rlog r h1 == Seq.empty /\
      rctrT r h1 == 0)
  )



//val rincrementable: #i:I.id -> #w:stream_writer i -> r:stream_reader w -> h:mem -> Type0


val encrypt
  (#i:I.id)
  (w:stream_writer i)
  (ad:AEAD.adata)
  (lmax:plainLen)
  (p:plain i lmax):
  ST (cipher i lmax)
  (requires fun h0 -> wincrementable w h0 /\ invariant w h0)
  (ensures fun h0 c h1 ->
    invariant w h1 /\
    wctrT w h1 == wctrT w h0 + 1 /\ 
    (Flag.safeId i ==> (
      wlog w h1 == Seq.snoc (wlog w h0) (Entry ad p c))) /\
    modifies (Set.union (footprint w) (shared_footprint w)) h0 h1)

//val adata_of_entry: #i:I.id -> stream_entry i -> GTot AEAD.adata

//val cipher_of_entry: #i:I.id -> stream_entry i -> GTot //(lmax:AEAD.plainLen & c:cipher i lmax)

//let matches (#i:I.id) (e:stream_entry i) (ad:AEAD.adata) (lmax:AEAD.plainLen) (c:cipher i lmax) : GTot bool =
//  let (|lmax', c'|) = cipher_of_entry e in
 //   adata_of_entry e = ad && lmax' = lmax && c' = c


val decrypt
  (#i:I.id)
  (#w:stream_writer i)
  (r:stream_reader w)
  (ad:AEAD.adata)
  (lmax:plainLen)
  (c:cipher i lmax):
  ST (option (plain i lmax))
  (requires fun h0 -> rinvariant r h0 /\ invariant w h0 /\ rincrementable r h0)
  (ensures fun h0 res h1 ->
    let j = rctrT r h0 in
//    invariant w h1 /\
    rinvariant r h1 /\
    modifies (Set.union (rfootprint r) (rshared_footprint r)) h0 h1 /\
    (Some? res ==> rctrT r h1 == j + 1) /\
    (None? res ==> rctrT r h1 == j) /\
    (Flag.safeId i ==> (
      let lg = wlog w h0 in
      if j < wctrT w h0 then
        (match (Seq.index lg j) with 
          | Entry ad' #lmax' p' c' ->
            if ad' = ad && lmax' = lmax && c' = c then
              res = Some p' 
            else
              res = None)
      else
        res = None))
  ) 
