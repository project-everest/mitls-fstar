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
  
type llbytes (lmax:nat) = b:bytes{length b <= lmax}

val plain: i:I.id -> lmax:AEAD.plainLen -> Type0

type cipher (i:I.id) (lmax:AEAD.plainLen) = llbytes lmax

val stream_entry : i:I.id -> Type0

val mk_entry (#i:I.id) :
    ad:AEAD.adata ->
    #lmax:AEAD.plainLen ->
    p:plain i lmax ->
    c:cipher i lmax ->
    stream_entry i


val stream_state: I.id -> I.rw -> Type0

val ctrT: #i:I.id -> #rw:I.rw -> wr:stream_state i rw -> mem -> GTot UInt32.t

val log: #i:I.id -> #rw:I.rw -> wr:stream_state i rw -> mem -> GTot (Seq.seq (stream_entry i))

val invariant: #i:I.id -> #rw:I.rw -> stream_state i rw -> mem -> Type0

type info' = {
  alg: I.aeadAlg;
  shared: subrgn tls_tables_region;
  local: subrgn tls_tables_region;
}

type info (i:I.id) =
  info:info'{I.aeadAlg_of_id i == info.alg}

val shared_footprint: rset

val footprint: #i:I.id -> #rw:I.rw -> stream_state i rw -> s:rset{Set.disjoint s shared_footprint}

val log_region: #i:I.id -> #rw:I.rw -> stream_state i rw -> subrgn tls_tables_region



val frame_invariant: #i:I.id -> #rw:I.rw -> s:stream_state i rw -> h0:mem -> r:rid -> h1:mem ->
  Lemma
  (requires
    (invariant s h0 /\
    modifies_one r h0 h1 /\
    ~(Set.mem r (footprint s)) /\
    ~(Set.mem r (shared_footprint))))
  (ensures invariant s h1)

val frame_log: #i:I.id -> #rw:I.rw -> s:stream_state i rw -> l:Seq.seq (stream_entry i) ->
  h0:mem -> r:rid -> h1:mem ->
  Lemma
  (requires
    Flag.safeId i /\
    log s h0 == l /\
    modifies_one r h0 h1 /\
    ~(Set.mem r (footprint s)))
  (ensures log s h1 == l)


val create: i:I.id -> u:info i ->
  ST (stream_state i I.Writer)
  (requires fun h0 -> disjoint u.shared u.local)
  (ensures fun h0 s h1 ->
    invariant s h1 /\
    shared_footprint == Set.singleton u.shared /\
    footprint s == Set.singleton u.local /\
    log_region s == u.local /\
    modifies_none h0 h1 /\
    Flag.safeId i ==>
      (log s h1 == Seq.empty /\
      ctrT s h1 == 0ul)
  )

let reader_footprint (#i:I.id) (w:stream_state i I.Writer) : GTot rset =
  shared_footprint
  
val createReader: #i:I.id -> w:stream_state i I.Writer ->
  ST (stream_state i I.Reader)
  (requires fun h0 -> invariant w h0)
  (ensures fun h0 r h1 ->
    invariant r h1 /\
    modifies_none h0 h1 /\
    log_region r == log_region w /\
    footprint r == reader_footprint w /\
    Flag.safeId i ==>
      (log r h1 == Seq.empty /\
      ctrT r h1 == 0ul)
  )

val incrementable : #i:I.id -> #rw:I.rw -> stream_state i rw -> mem -> Type0

val encrypt
  (#i:I.id)
  (s:stream_state i I.Writer)
  (ad:AEAD.adata)
  (lmax:AEAD.plainLen)
  (p:plain i lmax):
  ST (cipher i lmax)
  (requires fun h0 -> incrementable s h0 /\ invariant s h0)
  (ensures fun h0 c h1 ->
    U32.v (ctrT s h1) == U32.v (ctrT s h0) + 1 /\ 
    (Flag.safeId i ==> (
      log s h1 == Seq.cons (mk_entry ad p c) (log s h0))) /\
    invariant s h1 /\
    modifies (Set.union (footprint s) shared_footprint) h0 h1)

val adata_of_entry: #i:I.id -> stream_entry i -> GTot AEAD.adata

val cipher_of_entry: #i:I.id -> stream_entry i -> GTot (lmax:AEAD.plainLen & c:cipher i lmax)

let matches (#i:I.id) (e:stream_entry i) (ad:AEAD.adata) (lmax:AEAD.plainLen) (c:cipher i lmax) : GTot bool =
  let (|lmax', c'|) = cipher_of_entry e in
    adata_of_entry e = ad && lmax' = lmax && c' = c


val decrypt
  (#i:I.id)
  (s:stream_state i I.Reader)
  (ad:AEAD.adata)
  (lmax:AEAD.plainLen)
  (c:cipher i lmax):
  ST (option (plain i lmax))
  (requires fun h0 -> incrementable s h0 /\ invariant s h0)
  (ensures fun h0 res h1 ->
    invariant s h1 /\
    modifies (footprint s) h0 h1 /\
    (Flag.safeId i ==> (
      let j = U32.v (ctrT s h0) in
      let lg = log s h0 in
      if j < Seq.length lg && matches (Seq.index lg j) ad lmax c then
        (Some? res /\
        Seq.index lg j == mk_entry ad (Some?.v res) c /\
        U32.v (ctrT s h1) == j + 1)
      else
        res == None)))
        

