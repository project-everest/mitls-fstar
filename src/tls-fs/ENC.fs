(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module ENC
//open Seq
open Bytes
open Error
open TLSError
open TLSConstants
open TLSInfo
open Range

(* We do not open Encode so that we can syntactically check its usage restrictions *) 

type cipher = bytes

(* Early TLS chains IVs but this is not secure against adaptive CPA *)
let lastblock alg cipher =
    let ivl = blockSize alg in
    let (_,b) = split cipher (length cipher - ivl) in b

type key = {k:bytes}

type iv = bytes
type iv3 =
    | SomeIV of iv
    | NoIV

type blockState =
    {key: key;
     iv: iv3}
type streamState = 
    {skey: key; // Ghost: Only stored so that we can LEAK it
     sstate: CoreCiphers.rc4engine}

type state =
    | BlockCipher of blockState
    | StreamCipher of streamState
type encryptor = state
type decryptor = state

(* CF 14-07-17: reuse?
let GENOne ki : state =
    #if verify
    failwith "trusted for correctness"
    #else
    let alg = encAlg_of_id ki in
    match alg with
    | Stream_RC4_128 ->
        let k = Nonce.random (encKeySize alg) in
        let key = {k = k} in
        StreamCipher({skey = key; sstate = CoreCiphers.rc4create (k)})
    | CBC_Stale(cbc) ->
        let key = {k = Nonce.random (encKeySize alg)}
        let iv = SomeIV(Nonce.random (blockSize cbc))
        BlockCipher ({key = key; iv = iv})
    | CBC_Fresh(_) ->
        let key = {k = Nonce.random (encKeySize alg)}
        let iv = NoIV
        BlockCipher ({key = key; iv = iv})
    #endif
*)

let streamCipher (ki:id) (r:rw) (s:streamState)  = StreamCipher(s)
let blockCipher (ki:id) (r:rw) (s:blockState) = BlockCipher(s)

let someIV (ki:id) (iv:iv) = SomeIV(iv)
let noIV (ki:id) = NoIV
let updateIV (i:id) (s:blockState) (iv:iv3) = {s with iv = iv}

let gen (ki:id) : encryptor * decryptor = 
    let alg = encAlg_of_id ki in
    match alg with
    | Stream_RC4_128 ->
        let k = Nonce.random (encKeySize alg) in
        let key = {k = k} in
        streamCipher ki Writer ({skey = key; sstate = CoreCiphers.rc4create (k)}),
        streamCipher ki Reader ({skey = key; sstate = CoreCiphers.rc4create (k)})
    | CBC_Stale(cbc) ->
        let key = {k = Nonce.random (encKeySize alg)} in
        let ivRandom = Nonce.random (blockSize cbc) in
        let iv = someIV ki ivRandom in
        blockCipher ki Writer ({key = key; iv = iv}),
        blockCipher ki Reader ({key = key; iv = iv})
    | CBC_Fresh(_) ->
        let key = {k = Nonce.random (encKeySize alg)} in
        let iv = noIV ki in
        blockCipher ki Writer ({key = key; iv = iv}) ,
        blockCipher ki Reader ({key = key; iv = iv}) 
    
let coerce (ki:id) (rw:rw) k iv =
    let alg = encAlg_of_id ki in
    match alg with
    | Stream_RC4_128 ->
        let key = {k = k} in
        StreamCipher({skey = key; sstate = CoreCiphers.rc4create (k)})
    | CBC_Stale(_) ->
        BlockCipher ({key = {k=k}; iv = SomeIV(iv)})
    | CBC_Fresh(_) ->
        BlockCipher ({key = {k=k}; iv = NoIV})

let leak (ki:id) (rw:rw) s =
    match s with
    | BlockCipher (bs) ->
        let bsiv = bs.iv in
        (match bsiv with
            | NoIV -> (bs.key.k,empty_bytes)
            | SomeIV(ivec) -> (bs.key.k,ivec))
    | StreamCipher (ss) ->
        ss.skey.k,empty_bytes

let cbcenc alg k iv d =
    match alg with
    | TDES_EDE -> (CoreCiphers.des3_cbc_encrypt k iv d)
    | AES_128 | AES_256  -> (CoreCiphers.aes_cbc_encrypt  k iv d)

(* Parametric enc/dec functions *)
let enc_int ki s tlen d =
    let alg = ki.aeAlg in
    match s,alg with
    //#begin-ivStaleEnc
    | BlockCipher(s), MtE((CBC_Stale alg) ,_) ->
        (match s.iv with
        | NoIV -> unexpected "[enc] Wrong combination of cipher algorithm and state"
        | SomeIV(iv) ->
            let cipher = cbcenc alg s.key.k iv d in
            let cl = length cipher in
            if cl <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
            else
                let lb = lastblock alg cipher in
                let iv = someIV ki lb in
                let s = updateIV ki s iv in
                (BlockCipher(s), cipher))
    //#end-ivStaleEnc
    | BlockCipher(s), MtE((CBC_Fresh alg), _) ->
        (match s.iv with
        | SomeIV(b) -> unexpected "[enc] Wrong combination of cipher algorithm and state"
        | NoIV   ->
            let ivl = blockSize alg in
            let iv = Nonce.random ivl in
            let cipher = cbcenc alg s.key.k iv d in
            let res = iv @| cipher in
            if length res <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
            else
                (BlockCipher(s), res))
    | StreamCipher(s), MtE (Stream_RC4_128, _) ->
        let cipher = (CoreCiphers.rc4process s.sstate (d)) in
        if length cipher <> tlen || tlen > max_TLSCipher_fragment_length then
                // unexpected, because it is enforced statically by the
                // CompatibleLength predicate
                unexpected "[enc] Length of encrypted data do not match expected length"
        else
            (StreamCipher(s),cipher)
    | _, _ -> unexpected "[enc] Wrong combination of cipher algorithm and state"

#if ideal
type event =
  | ENCrypted of id * LHAEPlain.adata * cipher * Encode.plain
type entry = id * LHAEPlain.adata * range * cipher * Encode.plain
let log: ref<list<entry>> = ref []
let rec cfind (e:id) (ad:LHAEPlain.adata) (c:cipher) (xs: list<entry>) : (range * Encode.plain) =
  //let (ad,rg,text) = 
  match xs with
    | [] -> failwith "not found"
    | entry::res -> 
        let (e',ad',rg, c',text) = entry in
        if e = e' && c = c' && ad = ad' then
            (rg,text)
        else cfind e ad c res

let addtolog (e:entry) (l: ref<list<entry>>) =
    e::!l
#endif


let enc (ki:id) s ad rg data =
    let tlen = targetLength ki rg in
  #if ideal
    let d =
      if safeId(ki) then //MK Should we use Encode.payload here? CF 14-07-17 ??
        createBytes tlen 0
      else
        Encode.repr ki ad rg data  //MK we may have only plaintext integrity in this case
    in
    if authId (ki) then
      let (s,c) = enc_int ki s tlen d in
      Pi.assume (ENCrypted(ki,ad,c,data));
      log := addtolog (ki, ad, rg, c, data) log;
      (s,c)
    else
  #endif
      let d = Encode.repr ki ad rg data in
      enc_int ki s tlen d

let cbcdec alg k iv e =
    match alg with
    | TDES_EDE          -> CoreCiphers.des3_cbc_decrypt k iv e
    | AES_128 | AES_256 -> CoreCiphers.aes_cbc_decrypt  k iv e

let dec_int (ki:id) (s:decryptor) cipher =
    let alg = ki.aeAlg in
    match s, alg with
    //#begin-ivStaleDec
    | BlockCipher(s), MtE((CBC_Stale alg), _) ->
        (match s.iv with
        | NoIV -> unexpected "[dec_int] Wrong combination of cipher algorithm and state"
        | SomeIV(iv) ->
            let data = cbcdec alg s.key.k iv cipher in
            let dlen = length data in
            let clen = length cipher in
            if dlen <> clen then
                unexpected "[dec_int] Core crypto returned wrong plaintext length"
            else
            let lb = lastblock alg cipher in
            let siv = someIV ki lb in
            let s = updateIV ki s siv in
            (BlockCipher(s), data))
    //#end-ivStaleDec
    | BlockCipher(s), MtE((CBC_Fresh alg) ,_) ->
        (match s.iv with
        | SomeIV(_) -> unexpected "[dec_int] Wrong combination of cipher algorithm and state"
        | NoIV ->
            let ivL = blockSize alg in
            let (iv,encrypted) = split cipher ivL in
            let data = cbcdec alg s.key.k iv encrypted in
            let dlen = length data in
            let elen = length encrypted in
            if dlen <> elen then
                unexpected "[dec_int] Core crypto returned wrong plaintext length"
            else
            (BlockCipher(s), data))
    | StreamCipher(s), MtE (Stream_RC4_128, _) ->
        let data = (CoreCiphers.rc4process s.sstate (cipher)) in
        let dlen = length data in
        let clen = length cipher in
        if dlen <> clen then
            unexpected "[dec_int] Core crypto returned wrong plaintext length"
        else
        (StreamCipher(s),data)
    | _,_ -> unexpected "[dec_int] Wrong combination of cipher algorithm and state"

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
