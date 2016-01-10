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
open Range

type id = i:id { is_MtE i.aeAlg } 
let alg (i:id) = MtE._0 i.aeAlg

type idB = i:id { is_Block (alg i) }

(* Also using Encode; we do not open it so that we can syntactically
   check its usage restrictions *)

type cipher = b:bytes { length b <= max_TLSCipher_fragment_length }

let blockSize (i:idB) = CoreCrypto.blockSize (Block._0 (alg i))
type block (i:idB) = lbytes (blockSize i)
type iv = block

(* Early TLS chains IVs, but this is not secure against adaptive CPA *)
let lastblock a (c:cipher {length c >= CoreCrypto.blockSize a}) : lbytes (CoreCrypto.blockSize a) =
    let ivl = CoreCrypto.blockSize a in
    let (_,b) = split c (length c - ivl) in b

private type key (i:id) = bytes
// for the reduction to non-agile algorithms, we would use
// private type (i:id) key' = 
//   | GoodKey_A of ideal_A.key 
//   | GoodKey_B of ideal_B.key
//   | BadKey_A 

let explicitIV (i:id) = 
  match alg i, pv_of_id i with 
  | Block _, TLS_1p1 | Block _, TLS_1p2 -> true 
  | _                                   -> false 

private type localState (region:rid) : i:id -> Type = 
  | StreamState:   i:id{ is_Stream (alg i) }                         -> s: CoreCrypto.cipher_stream -> localState region i
  | OldBlockState: i:id{ is_Block (alg i) /\ ~(explicitIV i) } -> iv i -> localState region i
  | NewBlockState: i:id{ is_Block (alg i) /\ explicitIV i  }          -> localState region i

// plain here is indexed by length, not range
type dplain (i:id) (c:cipher i) = Encode.plain i (if explicitIV i then length c - blockSize i else length c)

type entry (i:id) = | Entry:
  c: cipher i -> p: dplain i c -> entry i

private type state (i:id) (rw:rw) = | StateB:
  #region: rid ->
  #peer_region: rid { HyperHeap.disjoint region peer_region } -> 
  k: key i -> // only ghost for stream ciphers
  s: rref rid (localState rid i) -> 
  log: rref (if rw = reader then peer_region else region) (seq (entry i)) -> 
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

// We do not use the state, but an abstract ID over it, so that we can link
// encryptor and decryptor states 
assume val stateID: i:id -> rw:rw -> Tot int

val streamCipher: i:id -> r:rw -> streamState i -> state i r 
val blockCipher: i:id -> r:rw -> blockState i -> state i r
                                       
let streamCipher (i:id) (r:rw) (s:streamState i)  = StreamCipher(s)
let blockCipher (i:id) (r:rw) (s:blockState i) = BlockCipher(s)

val gen:  i:id ->
          e: encryptor i { stateID i Writer = 0 } * 
          d: decryptor i { stateID i Reader = 0 } 

val leak: i:id{not(safeId i)} -> rw:rw -> state i rw -> (*key:*) bytes * (*iv:*) bytes
val coerce: i:id{not(safeId i)} -> rw:rw -> (*key:*) bytes -> (*iv:*) bytes -> state i rw
                       
let gen (ki:id) : encryptor ki * decryptor ki = 
    let alg = encAlg_of_id ki in
    match alg with
    | Stream CoreCrypto.RC4_128, _ ->
        let k = CoreCrypto.random (encKeySize (Stream CoreCrypto.RC4_128)) in
        streamCipher ki Writer ({skey = k; sstate = CoreCrypto.stream_encryptor CoreCrypto.RC4_128 k}),
        streamCipher ki Reader ({skey = k; sstate = CoreCrypto.stream_encryptor CoreCrypto.RC4_128 k})
    | Block cbc, Stale ->
        let k = CoreCrypto.random (encKeySize (Block cbc)) in
        let ivRandom = CoreCrypto.random (CoreCrypto.blockSize cbc) in
        let iv = someIV ki ivRandom in
        blockCipher ki Writer ({key = k; iv = iv}),
        blockCipher ki Reader ({key = k; iv = iv})
    | Block cbc, Fresh ->
        let k = CoreCrypto.random (encKeySize (Block cbc)) in
        let iv = noIV ki in
        blockCipher ki Writer ({key = k; iv = iv}) ,
        blockCipher ki Reader ({key = k; iv = iv}) 
    
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

(* an abstract event recording all encryption results. *)

(*@assume logic type Encrypted : 
  i:id -> ad:LHAEPlain.adata i -> 
  c:cipher -> Encode.plain i ad (cipherRangeClass i (length c))-> Type*)

private val cbcenc: CoreCrypto.block_cipher -> bytes -> bytes -> bytes -> bytes 
let cbcenc alg k iv d = CoreCrypto.block_encrypt alg k iv d

(* Parametric enc/dec functions *)
let enc_int (ki:id) (s:encryptor ki) tlen d =
    let alg,ivm = encAlg_of_id ki in
    match s with
    //#begin-ivStaleEnc
    | BlockCipher(s) -> (match alg,ivm with Block alg, Stale -> //workaround for https://github.com/FStarLang/FStar/issues/397
        (match s.iv with
        | NoIV -> unexpected "[enc] Wrong combination of cipher algorithm and state"
        | SomeIV(iv) ->
            let cipher = cbcenc alg s.key iv d in
            let cl = length cipher in
            if cl <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
            else
                let lb = lastblock alg cipher in
                let iv = someIV ki lb in
                let s = updateIV ki s iv in
                (BlockCipher(s), cipher)) )
    //#end-ivStaleEnc
    | BlockCipher(s) -> (match alg,ivm with Block alg, Fresh ->
        (match s.iv with
        | SomeIV(b) -> unexpected "[enc] Wrong combination of cipher algorithm and state"
        | NoIV   ->
            let ivl = blockSize alg in
            let iv = CoreCrypto.random ivl in
            let cipher = cbcenc alg s.key iv d in
            let res = iv @| cipher in
            if length res <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
            else
                (BlockCipher(s), res)) )
    | StreamCipher(s) -> (match alg,ivm with Stream _, _ ->
        let cipher = (CoreCrypto.stream_process s.sstate (d)) in
        if length cipher <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
        else
            (StreamCipher(s),cipher) )
    | _ -> ( match alg,ivm with _ , _ -> unexpected "[enc] Wrong combination of cipher algorithm and state" )

#if ideal
type dplain (i:id) (ad:LHAEPlain.adata i) (c:cipher) =
    LHAEPlain.plain i ad (Range.cipherRangeClass i (length c))
                                                     
type entry =
  | Entry : i:id -> ad:LHAEPlain.adata i -> c:cipher -> p:dplain i ad c -> entry
                    
opaque logic type Encrypted (i:id) (ad:LHAEPlain.adata i) (c:cipher) (p:dplain i ad c) (h:heap) =
    b2t (List.mem (Entry i ad c p) (Heap.sel h log))

let log: ref (list entry) = ref []
#endif

let enc (ki:id) s ad rg data : _ * _ =
    let tlen = targetLength ki rg in
  #if ideal
    let d =
      if safeId ki then //MK Should we use Encode.payload here? CF 14-07-17 ??
        createBytes tlen 0
      else
        Encode.repr ki ad rg data  //MK we may have only plaintext integrity in this case
    in
    if authId ki then
      let (s,c) = enc_int ki s tlen d in
      (*assume (Encrypted(ki,ad,c,data));*)
      log := addtolog (ki, ad, rg, c, data) log;
      (s,c)
    else
  #endif
      let d = Encode.repr ki ad rg data in
      enc_int ki s tlen d


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
    | BlockCipher(s) -> ( match alg,ivm with Block alg, Stale -> //workaround for https://github.com/FStarLang/FStar/issues/397
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
    | BlockCipher(s) -> ( match alg,ivm with Block alg, Fresh ->
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
    | StreamCipher(s) -> (match alg,ivm with Stream _,  _ ->
        let data = (CoreCrypto.stream_process s.sstate (cipher)) in
        let dlen = length data in
        let clen = length cipher in
        if dlen <> clen then
            unexpected "[dec_int] Core crypto returned wrong plaintext length"
        else
        (StreamCipher(s),data) )
    | _ -> (match alg,ivm with _,_ -> unexpected "[dec_int] Wrong combination of cipher algorithm and state" )

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
