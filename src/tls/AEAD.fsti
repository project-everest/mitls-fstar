(**
  This interfaces provides an abstraction for the verified Hacl* Crypto.AEAD.Main module,
  using FStar.Bytes rather than buffers.
*)
module AEAD
module HS = FStar.HyperStack //Added automatically

module I = Crypto.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128
//module Plain = Crypto.Plain

open FStar.Bytes
open FStar.UInt32
open Mem
open Pkg


type safeid = i:I.id{Flag.safeId i}
type unsafeid = i:I.id{~ (Flag.safeId i)}

let safeMac (i:I.id) = Flag.safeHS i && Flag.mac1 i
let safeId  (i:I.id) = Flag.safeId i

let ivlen (alg:I.cipherAlg) = 12ul

let taglen = 16ul

let iv (alg:I.cipherAlg) =
  let open FStar.Mul in
  n:U128.t { U128.v n < pow2 (8 * v (ivlen alg)) }

let aadmax =
  assert_norm (2000 <= pow2 32 - 1);
  2000ul // arbitrary; enough for TLS

type aadlen_32 = l:U32.t {l <=^ aadmax}



type plainLen = l:nat{l + v taglen < pow2 32}

noeq type plain_pkg =
  | PlainPkg:
    plain: (i:I.id -> plainLen -> eqtype) ->
    as_bytes: (i:I.id -> l:plainLen -> plain i l -> GTot (lbytes l)) ->
    repr: (i:unsafeid -> l:plainLen -> p:plain i l -> Tot (b:lbytes l{b == as_bytes i l p})) ->
    plain_pkg

noeq type info' = {
  alg: I.aeadAlg;
  prf_rgn: subrgn tls_tables_region;
  log_rgn: subrgn tls_tables_region;
  plain: plain_pkg;
}

type info (i:I.id) =
  info:info'{I.aeadAlg_of_id i == info.alg}

let plain (#i:I.id) (u:info i) (l:plainLen) =
  (PlainPkg?.plain u.plain) i l
 
let as_bytes (#i:I.id) (#u:info i) (#l:plainLen) (p:plain u l) : GTot (lbytes l) = 
  (PlainPkg?.as_bytes u.plain) i l p
  
let repr (#i:unsafeid) (#u:info i) (#l:plainLen) (p:plain u l) : Tot (r:lbytes l{r == as_bytes p}) =
  (PlainPkg?.repr u.plain) i l p

val keylen   : #i:I.id -> u:info i -> U32.t

val statelen : #i:I.id -> u:info i -> U32.t

type cipher (i:I.id) (l:plainLen) = lbytes (l + (UInt32.v taglen))

type cipher32 (i:I.id) (l:U32.t{UInt.size (v l + 16) 32}) = lbytes32 (l +^ taglen)

type nonce (i:I.id) = iv (I.cipherAlg_of_id i)

type adata = b:bytes{length b <= v aadmax}

type entry (i:I.id) (u:info i) =
  | Entry:
    nonce: nonce i ->
    ad: adata ->
    #l: plainLen ->
//    #u: info i ->
    p: plain u l ->
    c: cipher i l ->
    entry i u

(*
inline_for_extraction
val entry : #i:I.id -> u:info i -> Type0


val mk_entry (#i:I.id) (u:info i):
    nonce:nonce i ->
    ad:adata ->
    #l:plainLen ->
    p:plain u l ->
    c:cipher i (length (as_bytes p)) ->
    entry u

val entry_injective (#i:I.id) (u:info i)
                    (n:nonce i) (n':nonce i)
                    (ad:adata) (ad':adata)
                    (#l:plainLen) (#l':plainLen)
                    (p:plain u l) (p':plain u l')
                    (c:cipher i l) (c':cipher i l')
  : Lemma (let e  = mk_entry u n ad p c in
           let e' = mk_entry u n' ad' p' c' in
           (e == e' <==> (n == n' /\ ad == ad' /\ l == l' /\ p == p' /\ c == c')))

val nonce_of_entry (#i:_) (#u:info i) (e:entry u) : nonce i

val ad_of_entry (#i:_) (#u:info i) (e:entry u) : adata

val plain_of_entry (#i:_) (#u:info i) (e:entry u) : (l:plainLen & p:plain u l)

val cipher_of_entry (#i:_) (#u:info i) (e:entry u) : cipher u
*)

val aead_state: i:I.id -> I.rw -> Type0

val getinfo: #i:I.id -> #rw:I.rw -> aead_state i rw -> Tot (info i)

val log: #i:I.id -> #rw:_ -> s:aead_state i rw{safeMac i} -> mem -> GTot (Seq.seq (entry i (getinfo s)))

let address = nat

let addr_unused_in (rid:rid) (a:address) (m0:mem) =
  Monotonic.Heap.addr_unused_in a (Map.sel (HS.get_hmap m0) rid)

let contains_addr (rid:rid) (a:address) (m:mem) =
  ~(addr_unused_in rid a m)

let fresh_addresses (rid:rid) (addrs:Set.set address) (m0:mem) (m1:mem) =
  forall a. a `Set.mem` addrs ==>
       addr_unused_in rid a m0 /\
       contains_addr  rid a m1

(** Downward closure of [prf_region i] *)
val shared_footprint: rset

(** Downward closure of [log_region i] *)
val footprint: #i:I.id -> #rw:_ -> aead_state i rw -> 
  GTot (s:rset{s `Set.disjoint` shared_footprint})

//Leaving this abstract for now; but it should imply Crypto.AEAD.Invariant.safelen i len (otp_offset i)
val safelen: I.id -> nat -> GTot bool

let ok_plain_len_32 (i:I.id) = l:U32.t{safelen i (v l)}

val invariant : #i:I.id -> #rw:I.rw -> aead_state i rw -> mem -> Type0

val frame_invariant: #i:I.id -> #rw:I.rw -> s:aead_state i rw -> h0:mem -> r:rid -> h1:mem ->
    Lemma (requires (invariant s h0 /\
           modifies_one r h0 h1 /\
           ~(r `Set.mem` footprint s) /\
           ~(r `Set.mem` shared_footprint)))
          (ensures invariant s h1)

val frame_log: #i:I.id -> #rw:I.rw -> s:aead_state i rw -> l:Seq.seq (entry i (getinfo s)) ->
  h0:mem -> r:rid -> h1:mem ->
  Lemma (requires
          safeMac i /\
          log s h0 == l /\
          modifies_one r h0 h1 /\
          ~(r `Set.mem` footprint s))
        (ensures log s h1 == l)

(*** The main stateful API ***)

(** Allocating a writer **)
val gen (i:I.id) (u:info i) : ST (aead_state i I.Writer)
  (requires (fun h -> u.prf_rgn `disjoint` u.log_rgn))
  (ensures  (fun h0 s h1 ->
    getinfo s == u /\
    modifies_none h0 h1 /\ // allocates only
    (exists fresh.
      fresh_addresses u.prf_rgn fresh h0 h1 /\
      footprint s == Set.singleton u.log_rgn /\
      shared_footprint == Set.singleton u.prf_rgn) /\
      (safeId i ==> log s h1 == Seq.empty) /\
        invariant s h1
      ))

(** Building a reader from a writer **)

(* A reader never writes to the log_region, but may write to the prf_region *)
let reader_footprint (#i:I.id) (w:(aead_state i I.Writer)) : GTot rset =
  assume false;
  Set.singleton (getinfo w).prf_rgn
  
//  TSet.filter (fun (r:HS.rid) -> r == prf_region wr)
//                    (footprint wr)

val genReader (#i: I.id) (w: aead_state i I.Writer) : ST (aead_state i I.Reader)
  (requires (fun h -> invariant w h))
  (ensures  (fun h0 r h1 ->
    HS.modifies Set.empty h0 h1 /\
    invariant r h1 /\
    getinfo r == getinfo w /\
    footprint r == reader_footprint w)
  )

(*
(** [coerce]: Only needed for modeling the adversary *)
val coerce
         (i: I.id)
       (rgn: eternal_region)
       (key: lbuffer (v (keylen i)))
      : ST  (aead_state i I.Writer)
  (requires (fun h ->
             ~ (Flag.prf i) /\
             Buffer.live h key))
  (ensures  (fun h0 st h1 ->
               HS.modifies Set.empty h0 h1 /\
               invariant st h1))


(** [leak]: Only needed for modeling the adversary *)
val leak
      (#i: I.id)
      (st: aead_state i I.Writer)
    : ST (lbuffer (v (statelen i)))
  (requires (fun _ -> ~(Flag.prf i)))
  (ensures  (fun h0 _ h1 ->
               HS.modifies Set.empty h0 h1 /\
               invariant st h1))


// enc_dec_separation: Calling AEAD.encrypt/decrypt requires this separation
let enc_dec_separation (#i:_) (#rw:_) (st:aead_state i rw)
                       (#aadlen:nat) (aad: lbuffer aadlen)
                       (#plainlen:nat) (plain: Plain.plainBuffer i plainlen)
                       (#cipherlen: nat) (cipher:lbuffer cipherlen) =
    Buffer.disjoint aad cipher /\
    Buffer.disjoint (Plain.as_buffer plain) aad /\
    Buffer.disjoint (Plain.as_buffer plain) cipher /\
    HS.disjoint_regions (Set.as_set [Buffer.frameOf (Plain.as_buffer plain);
                                     Buffer.frameOf cipher;
                                     Buffer.frameOf aad])
                        (Set.as_set [log_region st;
                                     prf_region st]) /\
    Buffer.frameOf cipher <> HS.root /\
    Buffer.frameOf aad <> HS.root /\
    Buffer.frameOf (Plain.as_buffer plain) <> HS.root
    (* is_eternal_region (Buffer.frameOf cipher) /\ // why? *)
    (* is_eternal_region (Buffer.frameOf (Plain.as_buffer plain)) /\ //why? *)
    (* is_eternal_region (Buffer.frameOf aad) /\ //why? *)

let enc_dec_liveness (#i:_) (#rw:_) (st:aead_state i rw)
                     (#aadlen:nat) (aad: lbuffer aadlen)
                     (#plainlen:nat) (plain: Plain.plainBuffer i plainlen)
                     (#cipherlen: nat) (cipher:lbuffer cipherlen) (h:mem) =
    let open HS in
    Buffer.live h aad /\
    Buffer.live h cipher /\
    Plain.live h plain /\
    log_region st `is_in` h.h /\
    prf_region st `is_in` h.h

let entry_of
          (#i: I.id)
           (n: iv (I.cipherAlg_of_id i))
     (#aadlen: aadlen_32)
         (aad: lbuffer (v aadlen))
   (#plainlen: ok_plain_len_32 i)
       (plain: Plain.plainBuffer i (v plainlen))
  (cipher_tag: lbuffer (v plainlen + v taglen))
           (h: mem) : GTot (entry i) =
  let aad = Buffer.as_seq h aad in
  let p = Plain.sel_plain h plainlen plain in
  let c = Buffer.as_seq h cipher_tag in
  mk_entry n aad p c
*)

let entry_for_nonce (#i:I.id) (#rw:I.rw) (n:nonce i) (s:aead_state i rw) (h:mem)
  : Ghost (option (entry i (getinfo s))) (requires safeId i) (ensures fun _ -> True) =
  Seq.find_l (fun e -> Entry?.nonce e = n) (log s h)

let fresh_nonce (#i:I.id) (#rw:I.rw) (n:nonce i) (s:aead_state i rw) (h:mem)
  : Ghost bool (requires safeId i) (ensures fun _ -> True) =
  None? (entry_for_nonce n s h)

(*let just_one_buffer (#a:Type) (b:Buffer.buffer a) : GTot fp =
   as_set [(Buffer.frameOf b, SomeRefs (as_set [Buffer.as_addr b]))]
*)

val encrypt
  (i: I.id)
  (w: aead_state i I.Writer)
  (n: iv (I.cipherAlg_of_id i))
  (aad: adata)
  (l: plainLen)
  (p: plain (getinfo w) l)
  : ST (cipher i l)
  (requires (fun h0 ->
//    enc_dec_separation st aad plain cipher_tag /\
//    enc_dec_liveness st aad plain cipher_tag h /\
    invariant w h0 /\
    (safeId i ==> fresh_nonce n w h0)))
  (ensures (fun h0 c h1 ->
    modifies (Set.union (footprint w) shared_footprint) h0 h1 /\
//    enc_dec_liveness st aad plain cipher_tag h1 /\
    invariant w h1 /\
    (safeId i ==>
      log w h1 == Seq.snoc (log w h0) (Entry n aad p c))))

val decrypt
  (i: I.id)
  (r: aead_state i I.Reader)
  (aad:adata)
  (n: iv (I.cipherAlg_of_id i))
  (l:plainLen)
  (c:cipher i l)
  : ST (option (plain (getinfo r) l))
  (requires (fun h0 ->
    invariant r h0))
  (ensures fun h0 res h1 ->
    invariant r h1 /\
    modifies (Set.union (footprint r) shared_footprint) h0 h1 /\
    (safeId i ==>
      (match entry_for_nonce n r h0 with
      | None -> None? res
      | Some (Entry _ aad' #l' p' c') ->
        (if aad' = aad && c' = c && l = l' then res = Some p'
        else None? res)
      )
    )
  )

