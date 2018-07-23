(**
Provides authenticated encryption for a stream of variable-length plaintexts;
concretely, we use AES_GCM but any other AEAD algorithm would do.
*)
module StreamAE

module HST = FStar.HyperStack.ST //Added automatically

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
open TLSInfo

#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

type plainLenMin = AEAD.plainLenMin 1
type iplainLenMin = l:AEAD.plainLenMin 1{l + v AEAD.taglen < pow2 32 - 1}

// plain i lmax: stream plaintext of length at most lmax
let plain i lmax = llbytes lmax

//aead_plain i l: aead plain of length exactly l
type aead_plain (i:I.id) (l:plainLenMin) : t:Type0{hasEq t} = lbytes l


type counter = c:UInt32.t{UInt32.v c <= max_ctr}

let increases_u32 (x:U32.t) (y:U32.t)  = increases (v x) (v y)

let ctr_ref (r:erid) (i:I.id) : Tot Type0 =
  m_rref r counter increases_u32



let as_bytes (i:I.id) (l:plainLenMin) (p:aead_plain i l) : GTot (lbytes l) = p

let repr (i:AEAD.unsafeid) (l:plainLenMin) (p:aead_plain i l) : Tot (b:lbytes l{b == as_bytes i l p}) =
  p

//let f ($x: (I.id -> AEAD.plainLen -> t:Type0{hasEq t})) = True

//let _ = f (fun i l -> aead_plain i l)

//let _ = f aead_plain

let aead_plain_pkg = AEAD.PlainPkg 1 aead_plain as_bytes repr

//let aead_plain_pkg = AEAD.PlainPkg (fun i l -> aead_plain i l) as_bytes repr

type aead_info (i:I.id) = u:(AEAD.info i){u.AEAD.plain == aead_plain_pkg}


val pad: lmax:plainLen -> p:llbytes lmax -> lbytes (lmax+1)
let pad lmax p =
  let lz = U32.uint_to_t (lmax - (length p)) in
  let z = Bytes.create lz (U8.uint_to_t 0) in
  let one = Bytes.create 1ul (U8.uint_to_t 1) in
  Bytes.append (Bytes.append p one) z
  

val unpad: #l:plainLenMin -> p:lbytes l -> llbytes (l-1)
let rec unpad #l p =
  let last = U32.uint_to_t (l - 1) in
  let pp = Bytes.slice p 0ul last in
  if Bytes.get p last = U8.uint_to_t 0 && l > 1 then
    let ppp = unpad #(l-1) pp <: bytes in
    ppp
  else
    pp

val unpad_zero (l:plainLenMin{l>=2}) (p:lbytes (l-1)) : Lemma
  (requires True)
  (ensures
    (unpad #l (Bytes.append p (Bytes.create 1ul (U8.uint_to_t 0)))) = 
    (unpad #(l-1) p <: bytes))
let unpad_zero l p =
  let zero = U8.uint_to_t 0 in
  let zerob = Bytes.create 1ul zero in
  let last = U32.uint_to_t (l - 1) in
  let p' = Bytes.append p zerob in
  let pp = Bytes.slice p' 0ul last in
  Seq.Base.lemma_eq_elim (Bytes.reveal p) (Bytes.reveal pp)
  
val unpad_pad (lmax:plainLen) (p:llbytes lmax) : Lemma
  (requires True)
  (ensures
    unpad (pad lmax p) = p)

let rec unpad_pad lmax p = 
  let zero = U8.uint_to_t 0 in
  let zerob = Bytes.create 1ul zero in
  let one = U8.uint_to_t 1 in
  let oneb = Bytes.create 1ul one in 
  let last = U32.uint_to_t lmax in
  let pp = Bytes.slice (pad lmax p) 0ul last in
  if lmax - length p = 0 then
    (//    assert (pad lmax p = Bytes.append p oneb);
//    assert (Bytes.get (pad lmax p) last = one);
    Seq.Base.lemma_eq_elim (Bytes.reveal pp) (Bytes.reveal p))
  else
    (Seq.Base.lemma_eq_elim (Bytes.reveal (pad lmax p)) (Bytes.reveal (Bytes.append (pad (lmax - 1) (p <: bytes)) (zerob)));
 //   assert (length p <= lmax - 1);
//    assert (pad lmax p = Bytes.append (pad (lmax - 1) p) (zerob));
    unpad_zero (lmax+1) (pad (lmax - 1) (p <: bytes));
//    assert (unpad (pad lmax p) = unpad (pad (lmax - 1) (p <: bytes)));
    unpad_pad (lmax - 1) (p <: bytes))

  

  

let plain_of_aead_plain
  (#i:I.id)
  (#l:plainLenMin)
  (p:aead_plain i l) : plain i (l-1) =
  unpad p

let aead_plain_of_plain
  (#i:I.id)
  (#lmax:plainLen)
  (p:plain i lmax) : aead_plain i (lmax+1) =
  pad lmax p


let cipher_of_aead_cipher
  (#i:I.id)
  (#u:aead_info i)
  (#l:plainLenMin)
  (c:AEAD.cipher i u l) : cipher i (l-1) =
  c

let aead_cipher_of_cipher
  (#i:I.id)
  (u:aead_info i)
  (#lmax:plainLen)
  (c:cipher i lmax) : AEAD.cipher i u (lmax+1) =
  c


noeq type stream_writer (i:I.id) =
  | Stream_writer:
    #region: rgn ->
    aead: AEAD.aead_writer i
      {(AEAD.wgetinfo aead).AEAD.plain == aead_plain_pkg /\
        Set.disjoint (Set.singleton region) (AEAD.wfootprint aead) /\
        Set.disjoint (Set.singleton region) (AEAD.shared_footprint)} ->
    iv: AEAD.iv (I.cipherAlg_of_id i) ->
    ctr: ctr_ref region i ->
    stream_writer i

noeq type stream_reader (#i:I.id) (w:stream_writer i) =
  | Stream_reader:
    #region: rgn ->
    aead: AEAD.aead_reader (Stream_writer?.aead w)
      {(AEAD.rgetinfo aead).AEAD.plain == aead_plain_pkg /\
        Set.disjoint (Set.singleton region) (AEAD.wfootprint (Stream_writer?.aead w)) /\
        Set.disjoint (Set.singleton region) (AEAD.rfootprint aead) /\
        Set.disjoint (Set.singleton region) (AEAD.shared_footprint) /\
        Set.disjoint (Set.singleton region) (Set.singleton (Stream_writer?.region w)) /\
        Set.disjoint (Set.singleton (Stream_writer?.region w)) (AEAD.rfootprint aead)} ->
    iv: AEAD.iv (I.cipherAlg_of_id i){iv = w.iv} ->
    ctr: ctr_ref region i ->
    stream_reader w

let uint32_to_uint128 (n:U32.t) : (m:U128.t{U32.v n == U128.v m /\ U128.v m <= pow2 32 - 1}) =
  U128.uint64_to_uint128 (Int.Cast.uint32_to_uint64 n)

assume val lem_xor :
  (n:nat) ->
  (x:U128.t{U128.v x <= pow2 n - 1}) ->
  (y:U128.t{U128.v y <= pow2 n - 1}) ->
  Lemma (requires True) (ensures U128.(v (x ^^ y)) <= pow2 n - 1)

val lem_powivlen : alg:I.cipherAlg -> Lemma (requires True) (ensures pow2 32 <= pow2 (8 * v (AEAD.ivlen alg)))
let lem_powivlen alg = Math.Lemmas.pow2_le_compat (8 * v (AEAD.ivlen alg)) 32

let create_nonce (#i:I.id) (iv: AEAD.iv (I.cipherAlg_of_id i)) (j:U32.t) : Tot (AEAD.nonce i) =
  lem_powivlen (I.cipherAlg_of_id i);
  lem_xor (8 * (v (AEAD.ivlen (I.cipherAlg_of_id i)))) iv (uint32_to_uint128 j);
  U128.(iv ^^ (uint32_to_uint128 j))


let invariant (#i:I.id) (w:stream_writer i) (h:mem) =
  AEAD.winvariant (Stream_writer?.aead w) h /\
  (if safeId i then
    let wc = sel h (Stream_writer?.ctr w) in
    let wlg = AEAD.wlog (Stream_writer?.aead w) h in
    let iv = Stream_writer?.iv w in
    UInt32.v wc = Seq.length wlg /\
    (forall (j:nat). (j < Seq.length wlg) ==> AEAD.Entry?.nonce (Seq.index wlg j) = create_nonce iv (U32.uint_to_t j))
  else
    True)

let pref (#t:Type) (s:Seq.seq t) (k:nat{k <= Seq.length s}) =
  Seq.Base.slice s 0 k

let rinvariant (#i:I.id) (#w:stream_writer i) (r:stream_reader w) (h:mem) =
  let wc = sel h (Stream_writer?.ctr w) in
  let rc = sel h (Stream_reader?.ctr r) in
  AEAD.winvariant (Stream_writer?.aead w) h /\
  (safeId i ==> rc <=^ wc)

let wctrT (#i:I.id) (w:stream_writer i) (h:mem) =
  v (sel h (Stream_writer?.ctr w)) 


let wctr (#i:I.id) (w:stream_writer i) =
  !(Stream_writer?.ctr w)

let rctrT (#i:I.id) (#w:stream_writer i) (r:stream_reader w) (h:mem) =
  v (sel h (Stream_reader?.ctr r)) 

let rctr (#i:I.id) (#w:stream_writer i) (r:stream_reader w) =
  !(Stream_reader?.ctr r)


let stream_entry_of_aead_entry (#i:I.id) (#u:aead_info i) (e:AEAD.entry i u) =
  match e with
    | AEAD.Entry nonce ad #l p c ->
      Entry ad (plain_of_aead_plain p) (cipher_of_aead_cipher c)

let seqmap (#t:Type) (#t':Type) (f:(t -> t')) (s:seq t) : 
  (s':seq t'
    {Seq.length s = Seq.length s' /\ 
    (forall (i:nat). i < Seq.length s ==> Seq.index s' i == f (Seq.index s i))})
  =
  Seq.init (Seq.length s) (fun j -> f (Seq.index s j))

let wlog (#i:safeid) (w:stream_writer i) (h:mem) =
  let wlg = AEAD.wlog (Stream_writer?.aead w) h in
  seqmap stream_entry_of_aead_entry wlg


let rlog (#i:safeid) (#w:stream_writer i) (r:stream_reader w) h =
  pref (wlog w h) (rctrT r h)


let shared_footprint #i w = AEAD.shared_footprint

let footprint #i w =
  assume False;
  Set.union (AEAD.wfootprint (Stream_writer?.aead w)) (Set.singleton (Stream_writer?.region w))
 

let rfootprint #i #w r =
  assume False;
  Set.union (AEAD.rfootprint (Stream_reader?.aead r))
    (Set.union (AEAD.wfootprint (Stream_writer?.aead w))
      (Set.union (Set.singleton (Stream_reader?.region r))
        (Set.singleton (Stream_writer?.region w))))

//#reset-options "--detail_errors"

let frame_invariant (#i:I.id) (w:stream_writer i) (h0:mem) (ri:rid) (h1:mem) =
  let aw = Stream_writer?.aead w in
//  FStar.Set.mem_union ri (AEAD.wfootprint (Stream_writer?.aead w)) (Set.singleton (Stream_writer?.region w));
  assume (ri <> (frameOf (Stream_writer?.ctr w)) ==> sel h0  (Stream_writer?.ctr w) = sel h1 (Stream_writer?.ctr w));
  AEAD.wframe_invariant aw h0 ri h1;
  if safeId i then (AEAD.frame_log aw (AEAD.wlog aw h0) h0 ri h1)


let rframe_invariant #i #w r h0 ri h1 = 
  let aw = Stream_writer?.aead w in
  assume (ri <> (frameOf (Stream_writer?.ctr w)) ==> sel h0  (Stream_writer?.ctr w) = sel h1 (Stream_writer?.ctr w));
  assume (ri <> (frameOf (Stream_reader?.ctr r)) ==> sel h0  (Stream_reader?.ctr r) = sel h1 (Stream_reader?.ctr r));
  AEAD.wframe_invariant aw h0 ri h1
 


let frame_log #i w l h0 ri h1 =
  let aw = Stream_writer?.aead w in
  AEAD.frame_log aw (AEAD.wlog aw h0) h0 ri h1
  

let aead_info_of_info (#i:I.id) (u:info i) : AEAD.info i =
  {AEAD.alg= u.alg; AEAD.prf_rgn=u.shared; AEAD.log_rgn=u.local; AEAD.plain=aead_plain_pkg}

val lem_ivlen : alg:I.cipherAlg -> Lemma (requires True) (ensures (16ul -^ (AEAD.ivlen alg) = 4ul))
let lem_ivlen alg = ()

let rec little_endian (b:bytes) : Tot (n:nat) (decreases (length b)) =
  if length b = 0 then 0
  else
    let b' = slice b 1ul (U32.uint_to_t (length b)) in
    let h = FStar.Bytes.get b 0ul in
    (UInt8.v h) + pow2 8 * little_endian b'

val lemma_euclidean_division: r:nat -> b:nat -> q:pos -> Lemma
  (requires (r < q))
  (ensures  (r + q * b < q * (b+1)))
let lemma_euclidean_division r b q = ()

val lemma_factorise: a:nat -> b:nat -> Lemma (a + a * b == a * (b + 1))
let lemma_factorise a b = ()

val lemma_mult_le_left': a:nat -> b:int -> c:int -> Lemma
  (requires (b <= c))
  (ensures  (a * b <= a * c))
let lemma_mult_le_left' a b c = ()


val lemma_mult_lt_left': a:pos -> b:int -> c:int -> Lemma
  (requires (b < c))
  (ensures  (a * b < a * c))
let lemma_mult_lt_left' a b c = ()

val lemma_little_endian_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures little_endian b < pow2 (8 * length b))
  (decreases (length b))
let rec lemma_little_endian_is_bounded b =
  if length b = 0 then ()
  else
    begin
    let s = slice b 1ul (U32.uint_to_t (length b)) in
    assert(length s = length b - 1);
    lemma_little_endian_is_bounded s;
    assert(UInt8.v (FStar.Bytes.get b 0ul) < pow2 8);
    assert(little_endian s < pow2 (8 * length s));
    lemma_mult_lt_left' (pow2 8) (little_endian s) (pow2 (8 * length s));
    assert(pow2 8 * little_endian s < pow2 8 * pow2 (8 * length s));    
    assert (little_endian b = (UInt8.v (FStar.Bytes.get b 0ul)) + pow2 8 * little_endian s);
    assert(little_endian b < pow2 8 + pow2 8 * pow2 (8 * (length b - 1)));
    lemma_euclidean_division (UInt8.v (FStar.Bytes.get b 0ul)) (little_endian s) (pow2 8);
    assert (little_endian s + 1 <= pow2 (8 * (length b - 1)));
    assert(little_endian b <= pow2 8 * (little_endian s + 1));
    lemma_mult_le_left' (pow2 8) (little_endian s+1) (pow2 (8 * (length b - 1)));
    assert(little_endian b <= pow2 8 * pow2 (8 * (length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (length b - 1));
    lemma_factorise 8 (length b - 1)
    end


val uint8_to_uint128: a:UInt8.t -> Tot (b:UInt128.t{UInt128.v b == UInt8.v a})
let uint8_to_uint128 a = U128.uint64_to_uint128 (FStar.Int.Cast.uint8_to_uint64 a)


val load_uint128:
  alg:I.cipherAlg ->
  len:U32.t {v len <= v (AEAD.ivlen alg)} -> 
  b:lbytes (v len) -> 
  Tot (n:U128.t{U128.v n == little_endian b}) (decreases (v len))



let rec load_uint128 alg len b =
  if len = 0ul then U128.uint64_to_uint128 0UL
  else
    let n' = load_uint128 alg (len -^ 1ul) (slice b 1ul len) in
    let h = FStar.Bytes.get b 0ul in
    lemma_little_endian_is_bounded (slice b 1ul len);
    assert (UInt128.v n' <= pow2 (8 * v len - 8) - 1);
    lemma_mult_le_left' (256) (U128.v n') (pow2 (8 * v len - 8) - 1);
    assert (256 * UInt128.v n' <= 256 * pow2 (8 * v len - 8) - 256);
    assert_norm (256 * pow2 (8 * 16 - 8) - 256 <= pow2 128 - 256);
    Math.Lemmas.pow2_le_compat (8 * 16 - 8) (8 * v len - 8);
    assert (256 * pow2 (8 * v len - 8) - 256 <= pow2 128 - 256);
    Math.Lemmas.modulo_lemma (256 * UInt128.v n') (pow2 128);
    assert_norm (pow2 (UInt32.v 8ul) == 256);
    assert (256 * UInt128.v n' == FStar.UInt128.(v (n' <<^ 8ul)));
    FStar.UInt128.(uint8_to_uint128 h +^ (n' <<^ 8ul))

let random_iv (alg:I.cipherAlg) :
  ST (AEAD.iv alg) (requires fun _ -> True) (ensures fun h0 _ h1 -> h0 == h1) =
  let ivlen = AEAD.ivlen alg in
  let b = CoreCrypto.random32 ivlen in
  let iv = load_uint128 alg ivlen b in
  lemma_little_endian_is_bounded b;
  iv



assume val frame_invariant': #i:I.id -> w:stream_writer i -> h0:mem -> h1:mem ->
  Lemma
  (requires
    (invariant w h0 /\
    modifies_none h0 h1 ))
  (ensures invariant w h1)

assume val aead_frame_invariant': #i:I.id -> w:AEAD.aead_writer i -> h0:mem -> h1:mem ->
  Lemma
  (requires
    (AEAD.winvariant w h0 /\
    modifies_none h0 h1 ))
  (ensures AEAD.winvariant w h1)

assume val aead_frame_log': #i:I.id -> w:AEAD.aead_writer i ->
  h0:mem -> h1:mem ->
  Lemma
    (requires
      safeId i /\
      modifies_none h0 h1)
    (ensures AEAD.wlog w h0 == AEAD.wlog w h1)
  
let create (i:I.id) (u:info i) = 
  let w = AEAD.gen i (aead_info_of_info u) in
  let h0 = get() in
  let rr = new_region u.parent in
  let alg = I.cipherAlg_of_aeadAlg u.alg in
  let iv :AEAD.iv (I.cipherAlg_of_id i) = random_iv alg in
  let ctr :ctr_ref rr i = ralloc #(U32.t) #increases_u32 rr 0ul in
  let h1 = get() in
  aead_frame_invariant' w h0 h1;
  if safeId i then aead_frame_log' w h0 h1;
  let s =   Stream_writer #i #rr w iv ctr in
  if safeId i then Seq.Base.lemma_empty (wlog s h1);
  s
  


let coerce i u = admit()


let createReader (parent:rgn) (#i:I.id) (w:stream_writer i) = //:
  let h0 = get() in
  let aw = Stream_writer?.aead w in
  let r = AEAD.genReader aw in
  let rr = new_region parent in
  let iv = Stream_writer?.iv w in
  let ctr = ralloc #(U32.t) #increases_u32 rr 0ul in
  assume ((Stream_writer?.region w) <> (AEAD.rgetinfo r).AEAD.prf_rgn); 
  assume (~ (Set.mem rr 
    (Set.union 
      (Set.union 
        (Set.union (AEAD.wfootprint aw) (AEAD.rfootprint r))
        (Set.singleton (Stream_writer?.region w)))
      (AEAD.shared_footprint))));
  let h1 = get() in  
  frame_invariant' w h0 h1;
  Stream_reader #i #w #rr r iv ctr



val seqmap_snoc (#t:Type) (#t':Type) (s:Seq.seq t) (f:t -> t') (x:t) :
  Lemma
    (requires True)
    (ensures seqmap f (Seq.snoc s x) == Seq.snoc (seqmap f s) (f x))
let seqmap_snoc #t #t' s f x = 
  Seq.Base.lemma_eq_elim (seqmap f (Seq.snoc s x)) (Seq.snoc (seqmap f s) (f x))

//#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 10"


val create_nonce_inj (#i:I.id) (iv:AEAD.iv (I.cipherAlg_of_id i)) (j:U32.t) (j':U32.t) :
  Lemma
  (requires create_nonce iv j = create_nonce iv j')
  (ensures j = j')
let create_nonce_inj #i iv j j' = 
  FStar.UInt.logxor_associative #128 (U128.v iv) (U128.v iv) (U128.v (uint32_to_uint128 j));
  FStar.UInt.logxor_associative #128 (U128.v iv) (U128.v iv) (U128.v (uint32_to_uint128 j'));
  FStar.UInt.logxor_self #128 (U128.v iv);
  FStar.UInt.logxor_commutative (UInt.zero 128) (U128.v (uint32_to_uint128 j));
  FStar.UInt.logxor_commutative (UInt.zero 128) (U128.v (uint32_to_uint128 j'));
  FStar.UInt.logxor_lemma_1 #128 (U128.v (uint32_to_uint128 j));
  FStar.UInt.logxor_lemma_1 #128 (U128.v (uint32_to_uint128 j'))

let create_nonce_inj' i iv j j' : Lemma ((create_nonce iv j = create_nonce iv j') ==> (j = j')) =
(FStar.Classical.move_requires (create_nonce_inj #i iv j) j')

let create_nonce_inj'' i iv j :
Lemma (forall (j':U32.t). (create_nonce iv j = create_nonce iv j') ==> (j = j')) =  
 FStar.Classical.forall_intro (fun j' -> create_nonce_inj' i iv j j')


val lem_fresh (i:I.id) (w:stream_writer i) (h:mem) :
  Lemma
  (requires safeId i /\ wincrementable w h /\ invariant w h)
  (ensures 
   (let iv = Stream_writer?.iv w in
    let aw = Stream_writer?.aead w in
    AEAD.fresh_nonce (create_nonce iv (U32.uint_to_t (wctrT w h))) aw h))

let lem_fresh i w h =
  let iv = Stream_writer?.iv w in
  let aw = Stream_writer?.aead w in
  let n' = create_nonce iv (U32.uint_to_t (wctrT w h)) in
  let lg = AEAD.wlog aw h in
  match AEAD.wentry_for_nonce n' aw h with
  | None -> ()
  | Some e ->
    lemma_find_l_contains (AEAD.nonce_filter #i #aw n') lg;
    Seq.contains_elim lg e;
    create_nonce_inj'' i iv (U32.uint_to_t (wctrT w h))
//    assert (Seq.contains lg e);
//    assert (AEAD.Entry?.nonce e = n');
//    assert (exists (j:nat). j < Seq.length lg /\ n' = create_nonce iv (U32.uint_to_t j))
  


//#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"

let encrypt
  (#i:I.id) (w:stream_writer i) (ad:AEAD.adata) (lmax:plainLen) (p:plain i lmax) 
=
  let h0 = get() in
  let pp = aead_plain_of_plain p in
  let aw = Stream_writer?.aead w in
  let ctr = Stream_writer?.ctr w in
  let iv = Stream_writer?.iv w in
  let n = create_nonce iv !ctr in
  assert (safeId i ==> (forall (j:nat). (j < wctrT w h0) ==>
    AEAD.Entry?.nonce (Seq.index (AEAD.wlog aw h0) j) = 
    create_nonce iv (U32.uint_to_t j)));
  if safeId i then lem_fresh i w h0;
  let cc = AEAD.encrypt i aw n ad (lmax+1) pp in
  let h05 = get() in
  let c = cipher_of_aead_cipher cc in
  ctr := !ctr +^ 1ul;
  let h1 = get() in
  AEAD.wframe_invariant aw h05 (Stream_writer?.region w) h1;
  if safeId i then
    begin
      AEAD.frame_log aw (AEAD.wlog aw h05) h05 (Stream_writer?.region w) h1;
      //AEAD.frame_log aw (Seq.snoc (AEAD.wlog aw h0) (AEAD.Entry n ad pp cc)) h05 (Stream_writer?.region w) h1;
    //assert (AEAD.wlog aw h1 == 
     // (Seq.snoc (AEAD.wlog aw h0) (AEAD.Entry n ad pp cc)));
     seqmap_snoc (AEAD.wlog aw h0) stream_entry_of_aead_entry (AEAD.Entry n ad pp cc);
    //assert (wlog w h1 == 
      //(Seq.snoc (wlog w h0) (stream_entry_of_aead_entry (AEAD.Entry n ad pp cc))))
    assert (forall (j:nat). (j <= wctrT w h0) ==>
     AEAD.Entry?.nonce (Seq.index (AEAD.wlog aw h1) j) = 
     create_nonce iv (U32.uint_to_t j))
    end;
  unpad_pad lmax p;
//  assert (stream_entry_of_aead_entry (AEAD.Entry n ad pp cc) == Entry ad p c);
  c




assume val aead_frame_log'': #i:I.id -> w:AEAD.aead_writer i ->
  h0:mem -> s:rset -> h1:mem ->
  Lemma
    (requires
      Set.disjoint s (AEAD.wfootprint w) /\
      safeId i /\
      modifies s h0 h1)
    (ensures AEAD.wlog w h0 == AEAD.wlog w h1)
 

val lem_nonce (i:I.id) (w:stream_writer i) (j:nat) (h:mem) :
  Lemma
  (requires safeId i /\ invariant w h /\ j < wctrT w h)
  (ensures
    (let wlg = wlog w h in
    let aw = Stream_writer?.aead w in
    let awlg = AEAD.wlog aw h in
    let n = create_nonce (Stream_writer?.iv w) (U32.uint_to_t j) in
    let u = AEAD.wgetinfo aw in
    match Seq.index wlg j, Seq.index awlg j with
      | Entry ad #lmax p c, AEAD.Entry n' ad' #l p' c' ->
        n' == n /\
        ad' == ad /\
        plain_of_aead_plain #i #l p' == p /\
        cipher_of_aead_cipher c' == c /\
        l = lmax + 1))
let lem_nonce i w j h = 
  let wlg = wlog w h in
  let aw = Stream_writer?.aead w in
  let awlg = AEAD.wlog aw h in
  let n = create_nonce (Stream_writer?.iv w) (U32.uint_to_t j) in
  let u = AEAD.wgetinfo aw in
  assert (stream_entry_of_aead_entry (Seq.index awlg j) == Seq.index wlg j)


val lem_nonce2 (i:I.id) (w:stream_writer i) (j:nat) (h:mem) :
  Lemma
  (requires safeId i /\ invariant w h /\ j < wctrT w h)
  (ensures
    (let wlg = wlog w h in
    let aw = Stream_writer?.aead w in
    let awlg = AEAD.wlog aw h in
    let n = create_nonce (Stream_writer?.iv w) (U32.uint_to_t j) in
    let u = AEAD.wgetinfo aw in
    match AEAD.wentry_for_nonce #i n aw h with
      | Some e -> Seq.index awlg j = e
      | None -> False))
let lem_nonce2 i w j h = 
  let wlg = wlog w h in
  let aw = Stream_writer?.aead w in
  let awlg = AEAD.wlog aw h in
  let iv = Stream_writer?.iv w in
  let n = create_nonce iv (U32.uint_to_t j) in
  let u = AEAD.wgetinfo aw in
  match AEAD.wentry_for_nonce #i n aw h with
    | Some e ->
      lemma_find_l_contains (AEAD.nonce_filter #i #aw n) awlg;
      Seq.contains_elim awlg e;
      create_nonce_inj'' i iv (U32.uint_to_t j)
    | None -> Seq.find_l_none_no_index awlg (AEAD.nonce_filter #i #aw n);
      assert (AEAD.nonce_filter #i #aw n (Seq.index awlg j))

val lem_nonce3 (i:I.id) (w:stream_writer i) (j:nat) (h:mem) :
  Lemma
  (requires safeId i /\ invariant w h)
  (ensures
    j < wctrT w h ==> 
    (let wlg = wlog w h in
    let aw = Stream_writer?.aead w in
    let awlg = AEAD.wlog aw h in
    let n = create_nonce (Stream_writer?.iv w) (U32.uint_to_t j) in
    let u = AEAD.wgetinfo aw in
    match Seq.index wlg j with
      | Entry ad #lmax p c ->
        Some? (AEAD.wentry_for_nonce #i n aw h) /\
       (match Some?.v (AEAD.wentry_for_nonce #i n aw h) with
          | AEAD.Entry n' ad' #l p' c' ->
        n' = n /\
        ad' = ad /\
        plain_of_aead_plain #i #l p' = p /\
        cipher_of_aead_cipher c' = c /\
        l = lmax + 1)))
let lem_nonce3 i w j h = 
  if j < wctrT w h then
  begin
  let wlg = wlog w h in
  let aw = Stream_writer?.aead w in
  let awlg = AEAD.wlog aw h in
  let iv = Stream_writer?.iv w in
  let n = create_nonce iv (U32.uint_to_t j) in
  let u = AEAD.wgetinfo aw in
  lem_nonce2 i w j h; lem_nonce i w j h
  end

val lem_nonce4 (i:I.id) (w:stream_writer i) (j:nat) (h:mem) :
  Lemma
  (requires safeId i /\ invariant w h /\ j <= wctrT w h)
  (ensures
    (let aw = Stream_writer?.aead w in
    let n:AEAD.nonce i = create_nonce #i (Stream_writer?.iv w) (U32.uint_to_t j) in
    Some? (AEAD.wentry_for_nonce #i n aw h) ==>
    j < wctrT w h))
let lem_nonce4 i w j h = 
  let wlg = wlog w h in
  let aw = Stream_writer?.aead w in
  let awlg = AEAD.wlog aw h in
  let iv = Stream_writer?.iv w in
  let n = create_nonce iv (U32.uint_to_t j) in
  let u = AEAD.wgetinfo aw in
  match AEAD.wentry_for_nonce #i n aw h with
    | Some e ->
      lemma_find_l_contains (AEAD.nonce_filter #i #aw n) awlg;
      Seq.contains_elim awlg e;
      create_nonce_inj'' i iv (U32.uint_to_t j)
    | None -> ()


//#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 50"

let decrypt #i (#w:stream_writer i) (r:stream_reader w) ad lmax (c:cipher i lmax) 
=
  let h0 = get() in
  let aw = Stream_writer?.aead w in
  let ar = Stream_reader?.aead r in
  assume (Set.disjoint (Set.singleton (AEAD.rgetinfo ar).AEAD.prf_rgn) (AEAD.wfootprint aw));
  let cc:AEAD.cipher i (AEAD.rgetinfo ar) (lmax+1) = aead_cipher_of_cipher (AEAD.rgetinfo ar) c in
  let ctr = (Stream_reader?.ctr r) in
  let n = create_nonce (Stream_reader?.iv r) !ctr in
  let op = AEAD.decrypt i ar ad n (lmax+1) cc in
  let h05 = get() in
  assume (
    let s = (Set.union (AEAD.rfootprint ar) AEAD.shared_footprint) in
    let ctr' = Stream_writer?.ctr w in
    (~(Set.mem (frameOf ctr') s) /\ modifies s h0 h05) ==>

    sel h0 ctr' == sel h05 ctr');
  assume (
    let s = (Set.union (AEAD.rfootprint ar) AEAD.shared_footprint) in
    let ctr' = Stream_reader?.ctr r in
    (~(Set.mem (frameOf ctr') s) /\ modifies s h0 h05) ==>
    sel h0 ctr' == sel h05 ctr');
//  assert (AEAD.winvariant aw h05);
//  assert (wctrT w h05 == wctrT w h0);
//  assert (rctrT r h05 == rctrT r h0);
  if safeId i then aead_frame_log'' aw h0 (Set.union (AEAD.rfootprint ar) AEAD.shared_footprint) h05;
//  assert (safeId i ==> AEAD.wlog aw h0 == AEAD.wlog aw h05);
//  assert (invariant w h05);
  if safeId i then lem_nonce3 i w (rctrT r h0) h0;
  match op with
    | Some (pp:aead_plain i (lmax+1)) ->
      if safeId i then lem_nonce4 i w (rctrT r h0) h0;
      ctr := !ctr +^ 1ul; 
      let h1 = get() in 
      assert (~ (Set.mem (Stream_reader?.region r) (AEAD.wfootprint aw)));
      assert (~ (Set.mem (Stream_reader?.region r) (Set.singleton (Stream_writer?.region w))));
      assert (~ (Set.mem (Stream_reader?.region r) (Set.union (AEAD.wfootprint aw) (Set.singleton (Stream_writer?.region w)))));
      assert (~(Set.mem (Stream_reader?.region r) (footprint w)));
      AEAD.wframe_invariant aw h05 (Stream_reader?.region r) h1;
      frame_invariant w h05 (Stream_reader?.region r) h1;
      if safeId i then
        AEAD.frame_log aw (AEAD.wlog aw h05) h05 (Stream_reader?.region r) h1;
      Some (unpad pp)
    | None -> None
