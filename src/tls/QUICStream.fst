module QUICStream

module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack 

module I = Crypto.Indexing
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

open FStar.UInt32
//module Plain = Crypto.Plain

open FStar.HyperStack
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.Error
open FStar.Bytes

open FStar.Mul
open FStar.Bytes
open Mem
open Pkg
open TLSError
open TLSConstants
//open TLSInfo


let plain (i:I.id) (l:plainLen) = lbytes l

let plain_as_bytes (i:I.id) (l:plainLen) (p:plain i l) = p

let mk_plain i l b =
  if AEAD.safeId i then
    Bytes.create (U32.uint_to_t l) (U8.uint_to_t 0)
  else
    b

let plain_repr i l p = p



let nonce (i:I.id) (t:npn_length) : (t:Type0{hasEq t}) = AEAD.iv (I.cipherAlg_of_id i)

let nonce_as_bytes (i:I.id) (t:npn_length) (n:nonce i t) : GTot (AEAD.iv (I.cipherAlg_of_id i)) = n

let nonce_repr (i:I.id{~(safeId i)}) (t:npn_length) (n:nonce i t) :
  Tot (r:AEAD.iv (I.cipherAlg_of_id i){r == nonce_as_bytes i t n}) = n

let nonce_pkg =
  AEAD.NoncePkg npn_length nonce nonce_as_bytes nonce_repr

let pn j = lbytes pnlen

let pn_as_bytes j n = n

let mk_pn j b = b

let pn_repr j n = n

let pn_from_bytes (j:I.id) (b:lbytes pnlen) : GTot (n:pn j{pn_as_bytes j n == b})  =
  b
let pn_abs (j:I.id{~(PNE.safePNE j)}) (b:lbytes pnlen) : Tot (n:pn j{n == pn_from_bytes j b}) =
  mk_pn j b
  
let pn_plain_pkg = PNE.PNPkg pn pn_as_bytes pn_repr pn_from_bytes pn_abs


type aead_plain (i:I.id) (l:plainLen) : t:Type0{hasEq t} = lbytes l
  
let aead_as_bytes (i:I.id) (l:plainLen) (p:aead_plain i l) : GTot (lbytes l) = p

let aead_repr (i:AEAD.unsafeid) (l:plainLen) (p:aead_plain i l) : Tot (b:lbytes l{b == aead_as_bytes i l p}) =
  p

let aead_plain_pkg = AEAD.PlainPkg 0 aead_plain aead_as_bytes aead_repr

type aead_info (i:I.id) = u:(AEAD.info i){u.AEAD.plain == aead_plain_pkg /\ u.AEAD.nonce == nonce_pkg}

  
let plain_of_aead_plain
  (#i:I.id)
  (#l:plainLen)
  (p:aead_plain i l) : plain i l =
  p

let aead_plain_of_plain
  (#i:I.id)
  (#l:plainLen)
  (p:plain i l) : aead_plain i l =
  p


let cipher_of_aead_cipher
  (#i:I.id)
  (#u:aead_info i)
  (#l:plainLen)
  (c:AEAD.cipher i u l) : cipher i l =
  c

let aead_cipher_of_cipher
  (#i:I.id)
  (u:aead_info i)
  (#l:plainLen)
  (c:cipher i l) : AEAD.cipher i u l =
  c


type counter = c:UInt32.t{UInt32.v c <= max_ctr}

let increases_u128 (x:U128.t) (y:U128.t)  = increases (U128.v x) (U128.v y)
let increases_u32 (x:U32.t) (y:U32.t)  = increases (U32.v x) (U32.v y)

let ctr_ref (r:erid) (i:I.id) : Tot Type0 =
  m_rref r counter increases_u32

let pnlog_ref (r:erid) (j:I.id) : Tot Type0 =
  m_rref r (Seq.seq (pn j)) grows


noeq type stream_writer (i:I.id) (j:I.id) =
  | Stream_writer:
    #region: rgn ->
    aead: AEAD.aead_writer i
      {let u:AEAD.info i = AEAD.wgetinfo aead in
      u.AEAD.plain == aead_plain_pkg /\
      u.AEAD.nonce == nonce_pkg /\
        Set.disjoint (Set.singleton region) (AEAD.wfootprint aead) /\
        Set.disjoint (Set.singleton region) (AEAD.shared_footprint)} ->
    pne: PNE.pne_state j pn_plain_pkg ->
    iv: AEAD.iv (I.cipherAlg_of_id i) ->
    ctr: ctr_ref region i ->
    stream_writer i j

noeq type stream_reader (#i:I.id) (#j:I.id) (w:stream_writer i j) =
  | Stream_reader:
    #region: rgn ->
    aead: AEAD.aead_reader (Stream_writer?.aead w)
      {let u:AEAD.info i = AEAD.rgetinfo aead in
        u.AEAD.plain == aead_plain_pkg /\
        u.AEAD.nonce == nonce_pkg /\
        Set.disjoint (Set.singleton region) (AEAD.wfootprint (Stream_writer?.aead w)) /\
        Set.disjoint (Set.singleton region) (AEAD.rfootprint aead) /\
        Set.disjoint (Set.singleton region) (AEAD.shared_footprint) /\
        Set.disjoint (Set.singleton region) (Set.singleton (Stream_writer?.region w)) /\
        Set.disjoint (Set.singleton (Stream_writer?.region w)) (AEAD.rfootprint aead)} ->
    iv: AEAD.iv (I.cipherAlg_of_id i){iv = w.iv} ->
    pne:PNE.pne_state j pn_plain_pkg{pne == w.pne}  ->
    pnlg:pnlog_ref region j ->
    stream_reader w


#reset-options "--z3rlimit 50"

let create_nonce (#i:I.id) (#alg:I.cipherAlg{alg == I.cipherAlg_of_id i}) (iv: AEAD.iv alg) (l:npn_length) (j:counter) : Tot (nonce i l) =
  let ll = v (AEAD.ivlen alg) in  
  let j' = Bytes.bytes_of_int (ll-1) (U32.v j) in
  let l':lbytes 1 =
    match l with
      | OneByte -> Bytes.create 1ul (U8.uint_to_t 0)
      | TwoBytes -> Bytes.create 1ul (U8.uint_to_t 1)
      | FourBytes -> Bytes.create 1ul (U8.uint_to_t 2)
  in
  let lj:lbytes ll = Bytes.append j' l' in  
  assert (Bytes.fits_in_k_bytes (U128.v iv) ll);
  let iv' = Bytes.bytes_of_int ll (U128.v iv) in
  let nn = Bytes.xor (AEAD.ivlen alg) iv' lj in
  let n = Bytes.int_of_bytes nn in
  assert (n < pow2 (8*ll));
  Math.Lemmas.pow2_lt_compat 128 (8*ll);
  assert (pow2 (8*ll) < pow2 128);
  assert (n<pow2 128);
  U128.uint_to_t n


let pne_pn_filter (j:I.id) (n:pn j) (e:PNE.entry j pn_plain_pkg) : bool =
  PNE.Entry?.n e = n

#reset-options "--z3rlimit 50"
let invariant (#i:I.id) (#j:I.id) (w:stream_writer i j) (h:mem) =
  AEAD.winvariant (Stream_writer?.aead w) h /\
  (if safeId i then
    let alg = I.cipherAlg_of_aeadAlg ((AEAD.wgetinfo (Stream_writer?.aead w)).AEAD.alg) in
    let wc = sel h (Stream_writer?.ctr w) in
    let wlg = AEAD.wlog (Stream_writer?.aead w) h in
    let iv = Stream_writer?.iv w in
    let pne = Stream_writer?.pne w in
    let pnelg = PNE.table pne h in
    UInt32.v wc = Seq.length wlg /\
    (forall (k:nat). (k < Seq.length wlg) ==> (exists (l:npn_length). AEAD.Entry?.n (Seq.index wlg k) = create_nonce #i #alg iv l (U32.uint_to_t k))) /\
    (forall (k:nat). (k < Seq.length wlg) ==>
      (let n:pn j = bytes_of_int pnlen k in
       Some? (Seq.find_l (pne_pn_filter j n) pnelg)))
  else
    True)

#reset-options "--z3rlimit 10"
let rinvariant (#i:I.id) (#j:I.id) (#w:stream_writer i j) (r:stream_reader w) (h:mem) =
  let wc = sel h (Stream_writer?.ctr w) in
  let pnlg = sel h (Stream_reader?.pnlg r) in
  AEAD.winvariant (Stream_writer?.aead w) h /\
  (safeId i ==> (forall (n:pn j). Seq.mem n pnlg ==> pn_as_nat j n < v wc))


let wctrT #i #j w h =
  v (sel h (Stream_writer?.ctr w))

let wctr #i #j w =
  !(Stream_writer?.ctr w)


let pnlogT #i #j #w r h =
  sel h (Stream_reader?.pnlg r)
  
let pnlog #i #j #w r =
  !(Stream_reader?.pnlg r)

#reset-options "--z3rlimit 50"
let stream_entry_of_aead_entry (#i:I.id) (#j:I.id) (#u:aead_info i) (pnelg:Seq.seq (PNE.entry j pn_plain_pkg)) (k:nat{k < pow2 32 /\ Some? (Seq.find_l (pne_pn_filter j (bytes_of_int pnlen k)) pnelg)}) (e:AEAD.entry i u) :
  stream_entry i j =
  let n:pn j = bytes_of_int pnlen k in
  match e, Seq.find_l (pne_pn_filter j n) pnelg with
    | AEAD.Entry nonce ad #l p c, Some (PNE.Entry _ ne _) -> 
      Entry n ad (plain_of_aead_plain p) ne (cipher_of_aead_cipher c)

#reset-options "--z3rlimit 50"
(*
let seqmapi (#t:Type) (#t':Type) (f:(n:nat{n<pow2 32}) -> t -> t') (s:seq t) : 
  (s':seq t'
    {Seq.length s = Seq.length s' /\ 
    (forall (i:nat). i < Seq.length s ==> Seq.index s' i == f i (Seq.index s i))})
  =*)
(*)
let wlog #i #j w h =
  let wlg = AEAD.wlog (Stream_writer?.aead w) h in
  let pnelg = PNE.table (Stream_writer?.pne w) h in
  Seq.init (Seq.length wlg)
    (fun k ->    
      //assert(Some? (Seq.find_l (pne_pn_filter j (bytes_of_int pnlen k)) pnelg));
      //assume(k<pow2 32 /\ Some? (Seq.find_l (pne_pn_filter j (bytes_of_int pnlen k)) pnelg)); magic())     
      assert (k < wctrT w h);
      assert (wctrT w h < pow2 32);
      assert (k < pow2 32);
      assert (fits_in_k_bytes k 4);
      let _  =(bytes_of_int pnlen k) in
      magic())
      
      stream_entry_of_aead_entry pnelg k (Seq.index wlg k))



let wlog #i #j w h =
  AEAD.wlog

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
