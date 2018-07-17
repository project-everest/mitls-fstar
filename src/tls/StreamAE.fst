(**
Provides authenticated encryption for a stream of variable-length plaintexts;
concretely, we use AES_GCM but any other AEAD algorithm would do.
*)
module StreamAE

module HST = FStar.HyperStack.ST //Added automatically

module HS = FStar.HyperStack 

module I = Crypto.Indexing
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

type plainLenMin = AEAD.plainLenMin 1

// plain i lmax: stream plaintext of length at most lmax
let plain i lmax = llbytes lmax

//aead_plain i l: aead plain of length exactly l
type aead_plain (i:I.id) (l:plainLenMin) : t:Type0{hasEq t} = lbytes l


type counter = c:UInt32.t{UInt32.v c <= max_ctr}

let increases_u32 (x:U32.t) (y:U32.t)  = b2t (x <=^ y)

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


assume val pad: lmax:plainLen -> p:llbytes lmax -> lbytes (lmax+1)
assume val unpad: #l:plainLenMin -> p:lbytes l -> llbytes (l-1)

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
      ~ (Set.mem region (Set.union (AEAD.rfootprint aead) (AEAD.shared_footprint)))} ->
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
    (forall (j:U32.t). (v j < v wc) ==> AEAD.Entry?.nonce (Seq.index wlg (v j)) = create_nonce iv j)
  else
    True)

let pref (#t:Type) (s:Seq.seq t) (k:nat{k <= Seq.length s}) =
  Seq.Base.slice s 0 k

let rinvariant (#i:I.id) (#w:stream_writer i) (r:stream_reader w) (h:mem) =
  let wc = sel h (Stream_writer?.ctr w) in
  let rc = sel h (Stream_reader?.ctr r) in
  AEAD.winvariant (Stream_writer?.aead w) h /\
  rc <=^ wc

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

let seqmap (#t:Type) (#t':Type) (f:(t -> t')) (s:seq t) : (s':seq t'{Seq.length s = Seq.length s'}) =
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
    let b' = sub b 1ul (U32.uint_to_t ((length b) - 1)) in
    let h = FStar.Bytes.get b 0ul in
    (UInt8.v h) + pow2 8 * little_endian b'

val lemma_euclidean_division: r:nat -> b:nat -> q:pos -> Lemma
  (requires (r < q))
  (ensures  (r + q * b < q * (b+1)))
let lemma_euclidean_division r b q = ()

val lemma_factorise: a:nat -> b:nat -> Lemma (a + a * b == a * (b + 1))
let lemma_factorise a b = ()

val lemma_little_endian_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (little_endian b < pow2 (8 * length b)))
  (decreases (length b))
let rec lemma_little_endian_is_bounded b =
  if length b = 0 then ()
  else
    admit()

(*
    begin
    let s = slice b 1ul (U32.uint_to_t (length b)) in
    assert(length s = length b - 1);
    lemma_little_endian_is_bounded s;
    assert(UInt8.v (FStar.Bytes.get b 0ul) < pow2 8);
    assert(little_endian s < pow2 (8 * length s));
    assert(little_endian b < pow2 8 + pow2 8 * pow2 (8 * (length b - 1)));
    lemma_euclidean_division (UInt8.v (FStar.Bytes.get b 0ul)) (little_endian s) (pow2 8);
    assert(little_endian b <= pow2 8 * (little_endian s + 1));
    assert(little_endian b <= pow2 8 * pow2 (8 * (length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (length b - 1));
    lemma_factorise 8 (length b - 1)
    end
*)

val uint8_to_uint128: a:UInt8.t -> Tot (b:UInt128.t{UInt128.v b == UInt8.v a})
let uint8_to_uint128 a = U128.uint64_to_uint128 (FStar.Int.Cast.uint8_to_uint64 a)


val load_uint128:
  alg:I.cipherAlg ->
  len:U32.t {len <=^ (AEAD.ivlen alg)} -> 
  b:lbytes (v len) -> 
  Tot (n:U128.t{U128.v n == little_endian b}) (decreases (v len))
  
let rec load_uint128 alg len b =
  if len = 0ul then U128.uint64_to_uint128 0UL
  else
    let n' = load_uint128 alg (len -^ 1ul) (sub b 1ul (len -^ 1ul)) in
    let h = FStar.Bytes.get b 0ul in
    lemma_little_endian_is_bounded
      (sub b 1ul (len -^ 1ul));
     magic()
(*    assert (UInt128.v n' <= pow2 (8 * v len - 8) - 1);
   assert (256 * UInt128.v n' <= 256 * pow2 (8 * v len - 8) - 256);
    assert_norm (256 * pow2 (8 * 16 - 8) - 256 <= pow2 128 - 256);
    Math.Lemmas.pow2_le_compat (8 * 16 - 8) (8 * v len - 8);
    assert (256 * pow2 (8 * v len - 8) - 256 <= pow2 128 - 256);
    Math.Lemmas.modulo_lemma (256 * UInt128.v n') (pow2 128);
    assert_norm (pow2 (UInt32.v 8ul) == 256);
    assert (256 * UInt128.v n' == FStar.UInt128.(v (n' <<^ 8ul)));
    FStar.UInt128.(uint8_to_uint128 h +^ (n' <<^ 8ul))
*)

//parent in the info ?
let create (parent:rgn) (i:I.id) (u:info i) =
  let w = AEAD.gen i (aead_info_of_info u) in
  let rr = new_region parent in
  let alg = I.cipherAlg_of_aeadAlg u.alg in
  let ivlen = AEAD.ivlen alg in
  let b = CoreCrypto.random32 ivlen in
  let iv = load_uint128 alg ivlen b in
  let ctr = ralloc #(U32.t) #increases_u32 rr 0ul in
  admit();
  Stream_writer #i #rr w iv ctr
  

let coerce parent i u = admit()


let createReader (parent:rgn) (#i:I.id) (w:stream_writer i) =
  let aw = Stream_writer?.aead w in
  let r = AEAD.genReader aw in
  let rr = new_region parent in
  let iv = U128.uint_to_t 0 in
  let ctr = ralloc #(U32.t) #increases_u32 rr 0ul in
  admit()//;
//  Stream_reader #i #w #rr r iv ctr 


let encrypt #i (w:stream_writer i) ad lmax (p:plain i lmax) =
  let pp:aead_plain i (lmax+1) = pad lmax p in
  let aw = Stream_writer?.aead w in
  let ctr = Stream_writer?.ctr w in
  let n = create_nonce (Stream_writer?.iv w) !ctr in
 // let cc:AEAD.cipher i (AEAD.wgetinfo aw) (lmax+1) = AEAD.encrypt i aw n ad (lmax+1) pp in
//  let c = cipher_of_aead_cipher cc in
  ctr := !ctr  + 1
  admit() //c


let decrypt #i (#w:stream_writer i) (r:stream_reader w) ad lmax (c:cipher i lmax) =
  let ar = Stream_reader?.aead r in
  let cc:AEAD.cipher i (AEAD.rgetinfo ar) (lmax+1) = aead_cipher_of_cipher (AEAD.rgetinfo ar) c in
  let ctr = (Stream_reader?.ctr r) in
  let n = create_nonce (Stream_reader?.iv r) !ctr in
  let op = AEAD.decrypt i ar ad n (lmax+1) cc in
  admit();
  match op with
    | Some (pp:aead_plain i (lmax+1)) -> ctr := !ctr + 1; Some (unpad pp)
    | None -> None
