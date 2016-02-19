module ENC

(* Bulk encryption for TLS record's "MAC-encode-then encrypt", agile,
   possibly with internal state, and assumed conditionally CPA with
   "Encode" for plaintexts *)

(* This module is idealized *)

(* Instead, we could write a well-typed ideal functionality and reduce
   it to its non-agile underlying algorithms, e.g. AES-CBC *)

open FStar.Heap
open FStar.HyperHeap
open FStar.Seq
open FStar.SeqProperties

open Platform.Bytes
open Platform.Error

open TLSError
open TLSConstants
open TLSInfo
open LHAEPlain
open Range

(* Also using Encode; we do not open it so that we can syntactically
   check its usage restrictions *)


type id = i:id { is_MtE i.aeAlg } 
let alg (i:id) = MtE._0 i.aeAlg

type idB = i:id { is_Block (alg i) }

type cipher (i:id) = 
  b:bytes { let l = length b in
            l >= 0 /\ //16-01-13 why explicit?
            l <= max_TLSCipher_fragment_length /\ 
            valid_clen i l }

let explicitIV (i:id) = 
  match alg i, pv_of_id i with 
  | Block _, TLS_1p1 | Block _, TLS_1p2 -> true 
  | _                                   -> false 

//let clen (i:id) (plen:nat) = if explicitIV i then plen + blockSize i else plen


let blockSize (i:idB) = CoreCrypto.blockSize (Block._0 (alg i))
type block (i:idB) = lbytes (blockSize i)
type iv = block

(* Early TLS chains IVs, but this is not secure against adaptive CPA *)
let lblock (bl:nat) (c:bytes { length c >= bl }) : lbytes bl = 
  snd (split c (length c - bl))

//16-01-13 this can't work as bl appears in the inferred result type 
let lastblock (i:idB) = 
  (fun (bl:nat) (c:cipher i { length c >= bl}) -> lblock bl c) 
  (CoreCrypto.blockSize (Block._0 (alg i)))

//let lastblock (i:idB) (c:cipher i { length c >= CoreCrypto.blockSize (Block._0 (alg i))}) : block i =
//  lblock (CoreCrypto.blockSize (Block._0 (alg i))) c 

private type key (i:id) = bytes
// for the reduction to non-agile algorithms, we would use
// private type (i:id) key' = 
//   | GoodKey_A of ideal_A.key 
//   | GoodKey_B of ideal_B.key
//   | BadKey_A 

// JP: disabled for testing purposes
// private
type localState (region:rid): i:id -> Type = 
  | StreamState:   i:id{ is_Stream (alg i) }                         -> s: CoreCrypto.cipher_stream -> localState region i
  | OldBlockState: i:id{ is_Block (alg i) /\ ~(explicitIV i) } -> iv i -> localState region i
  | NewBlockState: i:id{ is_Block (alg i) /\ explicitIV i  }          -> localState region i

// type dplain (i:id) (ad: LHAEPlain.adata i) (c:cipher i) = 
//   Encode.plain i ad (cipherRangeClass i (length c))


type entry (i:id) = | Entry:
  c: cipher i -> p: Encode.dplain i (length c) -> entry i

// JP: disabled for testing purposes
// private
type state (i:id) (rw:rw) = | StateB:
  #region: rid ->
  #peer_region: rid { HyperHeap.disjoint region peer_region } -> 
  k: key i -> // only ghost for stream ciphers
  s: rref region (localState region i) -> 
  log: rref (if rw = Reader then peer_region else region) (seq (entry i)) -> 
  state i rw
                                        
(* does this guarantee type isolation? *)
type encryptor (i:id) = state i Writer
type decryptor (i:id) = state i Reader

(* CF 14-07-17: reuse?

// internal function declarations 
//TODO state should also have a role, but GENOne returns the state for both roles.
//private val GENOne: i:id -> 'a //(;i) state

let GENOne ki : state =
    //#if verify
    failwith "trusted for correctness"
    //#else
    let alg = encAlg_of_id ki in
    match alg with
    | Stream CoreCrypto.RC4_128 ->
        let k = CoreCrypto.random (encKeySize alg) in
        let key = {k = k} in
        StreamCipher({skey = key; sstate = CoreCiphers.rc4create (k)})
    | CBC_Stale(cbc) ->
        let key = {k = CoreCrypto.random (encKeySize alg)}
        let iv = SomeIV(CoreCrypto.random (blockSize cbc))
        BlockCipher ({key = key; iv = iv})
    | CBC_Fresh(_) ->
        let key = {k = CoreCrypto.random (encKeySize alg)}
        let iv = NoIV
        BlockCipher ({key = key; iv = iv})
    //#endif
*)


val gen: 
  reader_parent:rid -> 
  writer_parent:rid -> 
  i:id -> ST (encryptor i * decryptor i) 
  (requires (fun h0 -> HyperHeap.disjoint reader_parent writer_parent))
  (ensures (fun h0 (rw: encryptor i * decryptor i) h1 -> True))
                       
let gen reader_parent writer_parent i =
  let reader_r = new_region reader_parent in
  let writer_r = new_region writer_parent in
  assert(HyperHeap.disjoint reader_r writer_r);
  let log = ralloc writer_r Seq.createEmpty in 
  let alg = encAlg_of_id i in
  let kv, wstate, rstate = 
  match alg with
  | Stream CoreCrypto.RC4_128, _ ->
        let kv = CoreCrypto.random (encKeySize (Stream CoreCrypto.RC4_128)) in
        kv, 
        StreamState #writer_r i (CoreCrypto.stream_encryptor CoreCrypto.RC4_128 kv),
        StreamState #reader_r i (CoreCrypto.stream_encryptor CoreCrypto.RC4_128 kv)

  | Block cbc, Stale ->
        let kv = CoreCrypto.random (encKeySize (Block cbc)) in
        let iv = CoreCrypto.random (CoreCrypto.blockSize cbc) in
        kv, 
        OldBlockState #writer_r i iv, 
        OldBlockState #reader_r i iv

  | Block cbc, Fresh ->
        let kv = CoreCrypto.random (encKeySize (Block cbc)) in
        kv, 
        NewBlockState #writer_r i, 
        NewBlockState #reader_r i  
  in
  let enc: encryptor i = StateB #i #Writer #writer_r #reader_r kv (ralloc writer_r wstate) log in
  let dec: decryptor i = StateB #i #Reader #reader_r #writer_r kv (ralloc reader_r rstate) log in 
  enc, dec


(*
val leak: i:id{not(safeId i)} -> rw:rw -> state i rw -> (*key:*) bytes * (*iv:*) bytes
val coerce: i:id{not(safeId i)} -> rw:rw -> (*key:*) bytes -> (*iv:*) bytes -> state i rw
    
let coerce (ki:id) (rw:rw) k iv =
    let alg = encAlg_of_id ki in
    match alg with
    | Stream CoreCrypto.RC4_128, _ ->
        StreamCipher({skey = k; sstate = CoreCrypto.stream_encryptor CoreCrypto.RC4_128 k})
    | Block _, Stale ->
        blockCipher ki rw ({key = k; iv = SomeIV(iv)})
    | Block _, Fresh ->
        blockCipher ki rw ({key = k; iv = NoIV})

let leak (ki:id) (rw:rw) s =
    match s with
    | BlockCipher (bs) ->
        let bsiv = bs.iv in
        (match bsiv with
            | NoIV -> (bs.key,empty_bytes)
            | SomeIV(ivec) -> (bs.key,ivec))
    | StreamCipher (ss) ->
       (ss.skey,empty_bytes)
*)

(* an abstract event recording all encryption results. *)

(*@assume logic type Encrypted : 
  i:id -> ad:LHAEPlain.adata i -> 
  c:cipher -> Encode.plain i ad (cipherRangeClass i (length c))-> Type*)

let cbcenc = CoreCrypto.block_encrypt

(* Parametric enc/dec functions *)

val enc_int: i:id -> e: encryptor i -> tlen:nat -> bytes -> CoreCrypto.EXT bytes // (cipher i)
let enc_int (i:id) (e:encryptor i) tlen d = // multiplexing concrete encryptions
    let StateB k s _ = e in  
    // let alg,ivm = encAlg_of_id i in
    match !s with
    | StreamState _ ss -> CoreCrypto.stream_process ss d 

(*
        if length cipher <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
        else
        cipher *)

    | OldBlockState _ iv -> 
         let a = (Block._0 (alg i)) in 
         let cipher = cbcenc a k iv d in
         s := OldBlockState i (lastblock i cipher);
         cipher

(* 
            let cl = length cipher in
            if cl <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
            else
*) 

    | NewBlockState _ -> 
         let a = (Block._0 (alg i)) in 
         let iv = CoreCrypto.random (blockSize i) in
         cbcenc a k iv d 

(*
            let res = iv @| cipher in
            if length res <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
            else
                (BlockCipher(s), res)
*)

(*
BlockCipher(s) -> (match alg,ivm with Block alg, Stale -> //workaround for https://github.com/FStarLang/FStar/issues/397
        (match s.iv with
        | NoIV -> unexpected "[enc] Wrong combination of cipher algorithm and state"
        | SomeIV(iv) ->
    //#end-ivStaleEnc
    | BlockCipher(s) -> (match alg,ivm with Block alg, Fresh ->
        (match s.iv with
        | SomeIV(b) -> unexpected "[enc] Wrong combination of cipher algorithm and state"
        | NoIV   ->
    | StreamCipher(s) -> (match alg,ivm with Stream _, _ ->
        let cipher = (CoreCrypto.stream_process s.sstate (d)) in
        if length cipher <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
        else
            (StreamCipher(s),cipher) )
    | _ -> ( match alg,ivm with _ , _ -> unexpected "[enc] Wrong combination of cipher algorithm and state" )
*) 

//TODO: define monotonic property of being in the encryption log. 
// opaque logic type Encrypted (i:id) (ad:LHAEPlain.adata i) (c:cipher) (p:dplain i ad c) (h:heap) =
//   b2t (List.mem (Entry i ad c p) (Heap.sel h log))

val enc: i:id ->
         s: encryptor i ->
         ad: LHAEPlain.adata i ->
         rg: range ->
         data: LHAEPlain.plain i ad rg ->
         mackey: MAC.keyrepr i ->
         bytes
let enc (i:id) s ad rg data mackey =
    let tlen = targetLength i rg in
    let encrypted =
      if safeId i then createBytes tlen 0uy
      else Encode.encode i ad rg data mackey
    in
    // we grow the log in all cases // if authId i then
    let cipher: bytes = enc_int i s tlen encrypted in
    // log := snoc !log (Entry cipher ad data);
    cipher

(*
private val cbcdec: CoreCrypto.block_cipher -> bytes -> bytes -> bytes -> bytes
let cbcdec alg k iv e = CoreCrypto.block_decrypt alg k iv e

private val dec_int: i:id -> s: decryptor i -> c:cipher 
  { 
    (*@length c >= minTlen i /\ *)
    length c <= max_TLSCipher_fragment_length 
    (*@/\ 
    (!enc,mac. i.aeAlg = MtE(CBC_Stale(enc),mac) \/ i.aeAlg = MtE(CBC_Fresh(enc),mac) => Length(c)>=BlockSize(enc)) *)
    } -> 
    decryptor i *
    bytes 
        (*@ lbytes (plainLength i (length c)) *)
    //MK removed: ad:(;ki)LHAEPlain.adata

let dec_int (ki:id) (s:decryptor ki) cipher =
    let alg,ivm = encAlg_of_id ki in 
    match s with
    //#begin-ivStaleDec
    | BlockCipher(s) -> ( match alg,ivm with | Block alg, Stale -> //workaround for https://github.com/FStarLang/FStar/issues/397
        (match s.iv with
        | NoIV -> unexpected "[dec_int] Wrong combination of cipher algorithm and state"
        | SomeIV(iv) ->
            let data = cbcdec alg s.key iv cipher in
            let dlen = length data in
            let clen = length cipher in
            if dlen <> clen then
                unexpected "[dec_int] Core crypto returned wrong plaintext length"
            else
            let lb = lastblock alg cipher in
            let siv = someIV ki lb in
            let s = updateIV ki s siv in
            (BlockCipher(s), data)) )
    //#end-ivStaleDec
    | BlockCipher(s) -> ( match alg,ivm with | Block alg, Fresh ->
        (match s.iv with
        | SomeIV(_) -> unexpected "[dec_int] Wrong combination of cipher algorithm and state"
        | NoIV ->
            let ivL = blockSize alg in
            let (iv,encrypted) = split cipher ivL in
            let data = cbcdec alg s.key iv encrypted in
            let dlen = length data in
            let elen = length encrypted in
            if dlen <> elen then
                unexpected "[dec_int] Core crypto returned wrong plaintext length"
            else
            (BlockCipher(s), data)) )
    | StreamCipher(s) -> (match alg,ivm with | Stream _,  _ ->
        let data = (CoreCrypto.stream_process s.sstate (cipher)) in
        let dlen = length data in
        let clen = length cipher in
        if dlen <> clen then
            unexpected "[dec_int] Core crypto returned wrong plaintext length"
        else
        (StreamCipher(s),data) )
    | _ -> (match alg,ivm with | _,_ -> unexpected "[dec_int] Wrong combination of cipher algorithm and state" )

val dec: i:id -> s: decryptor i-> ad: LHAEPlain.adata i -> c:cipher
  { 
     (*@ (safeId i ==> (exists p'. Encrypted i ad c p')) /\*)
     (*@ length c >= minTlen i /\ *)
     length c <= max_TLSCipher_fragment_length } -> 

  ( (s': decryptor i (* todo?: { stateID i Reader s' = stateID i Reader s + 1 }*) )  *
    (p : Encode.plain i ad (cipherRangeClass i (length c))))
(* todo?: { forall p'. ENCrypted i ad c p' ==> p=p'}*) 

let dec ki s ad cipher =
  #if ideal
    if authId (ki) then
      let (s,p) = dec_int ki s cipher in
      //MK implement different find for plaintext integrity
      let (rg,p') = cfind ki ad cipher !log in
      let p' = Encode.widen ki ad rg p' in
      (s,p')
    else
  #endif
      let (s,p) = dec_int ki s cipher in
      let tlen = length cipher in
      let p' = Encode.mk_plain ki ad tlen p in
      (s,p')
*)

(* TODO: the SPRP game in F#, without indexing so far.
   the adversary gets 
   enc: block -> block
   dec: block -> block 

// two copies of assoc 
let rec findp pcs c = 
  match pcs with 
  | (p,c')::pcs -> if c = c' then Some(p) else findp pcs c
  | [] -> None
let rec findc pcs p = 
  match pcs with 
  | (p',c)::pcs -> if p = p' then Some(c) else findc pcs p
  | [] -> None
   
let k = mkRandom blocksize
let qe = ref 0
let qd = ref 0
#if ideal
let log = ref ([] : list<(block * block)>)
let F p = 
  match findc !pcs p with 
  | Some(c) -> c // non-parametric; 
                 // after CBC-collision avoidance,
                 // we will always use the "None" case
  | None    -> let c = mkfreshc !log blocksize 
               log := (p,c)::!log
               c
let G c = 
  match findp !log c with 
  | Some(p) -> p 
  | None    -> let p = mkfreshp !log blocksize 
               log := (p,c)::!log
               p
#else
let F = AES k
let G = AESminus k
#endif
let enc p = incr qe; F p
let dec c = incr qd; G c
*)
