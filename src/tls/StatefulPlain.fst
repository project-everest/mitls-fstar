module StatefulPlain

open FStar.Seq
open Platform.Bytes
open Platform.Error

open TLSError
open TLSConstants
open TLSInfo
open Range
open Content

let ad_Length i = match pv_of_id i with
    | SSL_3p0 -> 1
    | TLS_1p3 -> 0 // implicitly authenticated
    | _       -> 3 // ContentType[1] + Version[2]

val makeAD: i:id -> ct:ContentType -> Tot (lbytes (ad_Length i))
let makeAD i ct =
    let pv   = pv_of_id i in
    if pv = TLS_1p3 then empty_bytes
    else 
      let bct  = ctBytes ct in
      if pv = SSL_3p0
      then bct
      else bct @| versionBytes pv

// StatefulLHAE should be parametric in this type (or its refinement), but that'd be heavy
// here, the refinement ensures we never fail parsing indexes to retrieve ct
// that said, we should entirely avoid parsing it.
type adata (i:id) = b:bytes { exists ct. b = makeAD i ct }

val parseAD: i:id -> ad:adata i -> Tot ContentType
let parseAD i ad =
    let pv = pv_of_id i in
//    if pv = TLS_1p3 then 
//      Application_data // fake
//    else 
    if pv = SSL_3p0 then
      match parseCT ad with
      | Correct ct -> ct
    else
      let bct, bver = Platform.Bytes.split ad 1 in
      match parseCT bct, parseVersion bver with
      | Correct ct, Correct ver -> assert (ver = pv); ct

val lemma_makeAD_parseAD: i:id -> ct:ContentType -> Lemma
  (requires (True))
  (ensures (parseAD i (makeAD i ct) = ct))
  [SMTPat (makeAD i ct)]
let lemma_makeAD_parseAD i ct = () //cut (Seq.Eq ad (parseAD i (makeAD i n ad)))

// naming: we switch from fragment to plain as we are no longer TLS-specific
type plain (i:id) (ad:adata i) (rg:range) = f:fragment i
//  { (parseAD i ad, rg) = Content.ct_rg i f }
  { fst (ct_rg i f) = parseAD i ad /\ Wider rg (snd (ct_rg i f)) }

val ghost_repr: #i:id -> #ad:adata i -> #rg:range -> plain i ad rg -> GTot (rbytes rg)
let ghost_repr i ad rg pf = Content.ghost_repr #i pf

val repr: i:id{ ~(safeId i)} -> ad:adata i -> rg:range -> p:plain i ad rg -> Tot (b:rbytes rg {b = ghost_repr #i #ad #rg p})
let repr i ad rg f = Content.repr i f

logic type wf_ad_rg i ad rg = 
  Wider fragment_range rg  /\ 
  (parseAD i ad = Change_cipher_spec ==> rg = zero)

val mk_plain: i:id{ ~(authId i)} -> ad:adata i -> rg:frange i { wf_ad_rg i ad rg } ->
  b:rbytes rg  ->
  Tot (p:plain i ad rg {b = ghost_repr #i #ad #rg p})
let mk_plain i ad rg b =
  //mk_ct_rg i (parseAD i ad) rg b;
  Content.mk_fragment i (parseAD i ad) rg b


// ---------------------------------------------------------


// type cipherbytes = b:bytes { length b <= max_TLSCipher_fragment_length }

type cipher (i:id) = b:bytes {valid_clen i (length b)}

(*
let reprFragment (i:id) (ad:adata) (r:range) (f:plain) =
    let ct = parseAD i ad in
    let x = f.contents in
    Content.reprFragment i ct r x

let makeExtPad (i:id) (ad:adata) (r:range) f =
    let ct = parseAD i ad in
    let p = f.contents in
    let p = Content.makeExtPad i ct r p in
    {contents = p}

let parseExtPad (i:id) (ad:adata) (r:range) f =
    let ct = parseAD i ad in
    let p = f.contents in
    match Content.parseExtPad i ct r p with
    | Error(x) -> Error(x)
    | Correct(p) -> correct ({contents = p})

#if ideal
let widen i ad r f =
    let ct = parseAD i ad in
    let f1 = Content.widen i ct r f.contents in
    {contents = f1}
#endif

let recordPlainToStAEPlain (e:epoch) (ct:ContentType) (ad:adata) (h:Content.history) (sh:history) (rg:range) f = {contents = f}
let stAEPlainToRecordPlain (e:epoch) (ct:ContentType) (ad:adata) (h:Content.history) (sh:history) (rg:range) f = f.contents
*)
