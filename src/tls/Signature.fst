module Signature

open FStar.Monotonic.RRef
open FStar.HyperHeap
open Platform.Bytes

open MonotoneSeq
open TLSConstants
open CoreCrypto


(* ------------------------------------------------------------------------ *)
type text = bytes

type alg =
  | Use: info:(text -> Type0)
       -> core: sigAlg
       -> digest: list hashAlg
       -> keyEncipher: bool // can encrypt e.g. PMS in TLS_RSA_WITH_...
       -> keyExchange: bool // can be used to establish a Diffie-Hellman secret e.g. in TLS_DH_... SZ: Do we care about static (EC)DH?
       -> alg

type signed (a:alg) = t:text{a.info t}

// Could be finer, but we lack lengths in CoreCrypto signature functions
type sigv (a:alg) = bytes

// controls idealization of Sig
let ideal = IdealFlags.ideal_Sig

// Encodes agile INT-CMA assumption
assume type int_cma: a:alg -> h:hashAlg{List.Tot.mem h a.digest} -> Tot bool

type public_repr = 
  | PK_RSA   of rsa_key
  | PK_DSA   of dsa_key
  | PK_ECDSA of ec_key

type secret_repr =
  | SK_RSA   of rsa_key
  | SK_DSA   of dsa_key
  | SK_ECDSA of ec_key

let sigAlg_of_secret_repr sk =
  match sk with
  | SK_RSA k -> RSASIG // Ignore RSA-PSS
  | SK_DSA k -> DSA
  | SK_ECDSA k -> ECDSA

let sigAlg_of_public_repr pk =
  match pk with
  | PK_RSA k   -> RSASIG // Ignore RSA-PSS
  | PK_DSA k   -> DSA
  | PK_ECDSA k -> ECDSA

private val sig_digest: hashAlg -> bytes -> Tot (option hash_alg * bytes)
let sig_digest h t =
  match h with
  | NULL    -> None, t
  | MD5SHA1 -> None, HASH.hash h t
  | Hash h  -> Some h, t


(* ------------------------------------------------------------------------ *)
type state (a:alg) =
  | Signed: log:Seq.seq (signed a) -> state a
  | Corrupt

(* 
  Allowed state transitions:
  Corrupt  -> Corrupt
  Signed l -> Corrupt
  Signed l -> Signed l++l'
*)
abstract let evolves (#a:alg) (s1:state a) (s2:state a) =
  is_Corrupt s2 \/ 
  (is_Signed s1 /\ is_Signed s2 /\ grows (Signed.log s1) (Signed.log s2))

let lemma_evolves_monotone (#a:alg): Lemma (monotonic (state a) (evolves #a)) = 
  forall_intro (seq_extension_reflexive #(signed a));
  forall_intro_3 (grows_transitive #(signed a))

private val st_update: #a:alg 
  -> s1:state a 
  -> signed a 
  -> Tot (s2:state a{evolves s1 s2})
let st_update #a st t =
  match st with
  | Signed ts -> lemma_snoc_extends ts t; Signed (snoc ts t)
  | Corrupt   -> Corrupt


(* ------------------------------------------------------------------------ *)
assume val keyRegion: rid

type log_t (a:alg) = m_rref keyRegion (state a) evolves

type pubkey (a:alg) =
  | PK: log:log_t a -> repr:public_repr{sigAlg_of_public_repr repr = a.core} -> pubkey a

type pkey = (a:alg & pubkey a)

val pkey_repr: pkey -> Tot public_repr
let pkey_repr (| a,  p |) = PK.repr p

type skey (a:alg) = 
  k:(pubkey a * secret_repr){let _,sk = k in sigAlg_of_secret_repr sk = a.core}

val alloc_pubkey: #a:alg
  -> s:state a 
  -> r:public_repr{sigAlg_of_public_repr r = a.core}
  -> ST (pubkey a)
    (requires (fun h0 -> True))
    (ensures  (fun h0 p h1 -> ralloc_post keyRegion s h0 (as_rref (PK.log p)) h1
                           /\ PK.repr p = r
                           /\ m_fresh (PK.log p) h0 h1))
let alloc_pubkey #a s r =
  lemma_evolves_monotone #a;
  let log = m_alloc keyRegion s in 
  PK log r


(* ------------------------------------------------------------------------ *)
(* We rely on key-generation producing pairwise-distinct public keys
  with overwhelming probability. This follows from any crypto
  security assumptions, and most reasonable generation algorithms;
  we might not record keys generated with hopeless algorithms.

  We maintain this property as a stateful invariaint in rkeys *)

type kset = s:list pkey{ forall x y. (List.Tot.mem x s /\ List.Tot.mem y s /\ pkey_repr x = pkey_repr y) ==> x = y }

val find_key: r:public_repr -> ks: kset 
  -> Tot (o:option (k:pkey {pkey_repr k = r && List.Tot.mem k ks})
        { is_None o ==> (forall k. List.Tot.mem k ks ==> pkey_repr k <> r) })
let rec find_key r ks = match ks with
  | []   -> None
  | k::ks -> if pkey_repr k = r then Some k else find_key r ks

val add_key: ks:kset 
  -> k:pkey { forall k'. List.Tot.mem k' ks ==> pkey_repr k <> pkey_repr k' } 
  -> Tot kset
let add_key ks k = k::ks

unfoldable logic type mon_pkey (xs:kset) (xs':kset) =
  forall x. List.Tot.mem x xs ==> List.Tot.mem x xs'

// FIXME: top-level effect
val rkeys: m_rref keyRegion kset (mon_pkey)
let rkeys = m_alloc keyRegion []

type generated (k:pkey) (h:HyperHeap.t) : Type0 = List.Tot.mem k (m_sel h rkeys)


(* ------------------------------------------------------------------------ *)
val sign: #a:alg
  -> h:hashAlg{List.Tot.mem h (a.digest)} 
  -> s:skey a 
  -> t:signed a 
  -> ST (sigv a)
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 ->
      if ideal then
        let (pk,sk) = s in 
        let log = PK.log pk in
        modifies (Set.singleton keyRegion) h0 h1 /\
        m_sel h1 log == st_update (m_sel h0 log) t 
      else modifies Set.empty h0 h1))

let sign #a h s t =
  let (pk,sk) = s in
  begin
  if ideal then
    let log = PK.log pk in
    let s0 = m_read log in
    m_write log (st_update s0 t)
  end;
  let ho,t' = sig_digest h t in
  let signature =
    match sk with
    | SK_RSA k   -> rsa_sign ho k t'
    | SK_DSA k   -> dsa_sign ho k t'
    | SK_ECDSA k -> ecdsa_sign ho k t'
  in
  signature


(* ------------------------------------------------------------------------ *)
val verify: #a:alg 
  -> h:hashAlg{List.Tot.mem h (a.digest)} 
  -> pk:pubkey a 
  -> t:text
  -> sigv a
  -> ST bool
    (requires (fun h -> True))
    (ensures  (fun h0 b h1 -> 
	           modifies Set.empty h0 h1
		 /\ (b /\ ideal
		    /\ List.Tot.existsb (fun (k:pkey) -> let (|_,pk'|) = k in pk = pk') (m_sel h0 rkeys)
		    /\ int_cma a h
		    /\ is_Signed (m_sel h0 (PK.log pk))) ==>
		    a.info t))

let verify #a h pk t s =
  let verified =
    let ho,t' = sig_digest h t in
    match PK.repr pk with
    | PK_RSA k   -> rsa_verify ho k t' s
    | PK_DSA k   -> dsa_verify ho k t' s
    | PK_ECDSA k -> ecdsa_verify ho k t' s
  in
  if ideal then
    let signed =
      let log = m_read (PK.log pk) in
      match log with
      | Signed ts -> is_Some (SeqProperties.seq_find (fun (t':signed a) -> t = t') (Signed.log log))
      | Corrupt   -> true
    in
    let honest =
      let kset = m_read rkeys in
      List.Tot.existsb (fun (k:pkey) -> let (|_,pk'|) = k in pk = pk') kset
    in
    verified && (signed || not (honest && int_cma a h))
  else
    verified


(* ------------------------------------------------------------------------ *)
val genrepr: a:alg 
  -> All (public_repr * secret_repr)
    (requires (fun h -> True))
    (ensures  (fun h0 k h1 -> 
      	is_V k ==>
	(let (pk,sk) = V.v k in
        modifies Set.empty h0 h1
	/\ sigAlg_of_public_repr pk = sigAlg_of_secret_repr sk
	/\ sigAlg_of_public_repr pk = a.core)))
let genrepr a =
  match a.core with
  | RSASIG -> let k = rsa_gen_key 2048 in (PK_RSA k, SK_RSA k)
  | DSA    -> let k = dsa_gen_key 1024 in (PK_DSA k, SK_DSA k)
  | ECDSA  -> let k = ec_gen_key ({curve = ECC_P256; point_compression = false}) in (PK_ECDSA k, SK_ECDSA k)
  | RSAPSS -> failwith "Signature.genrepr: RSA-PSS unsupported"

val gen: a:alg -> All (skey a)
                     (requires (fun h -> m_contains rkeys h))
                     (ensures  (fun h0 (s:result (skey a)) h1 ->
			       modifies_one keyRegion h0 h1
                               /\ modifies_rref keyRegion !{as_ref (as_rref rkeys)} h0 h1
                               /\ m_contains rkeys h1
			       /\ (is_V s ==>
				 witnessed (generated (|a, fst (V.v s) |))
				 /\ m_fresh (PK.log (fst (V.v s))) h0 h1 )))

let rec gen a =
  let pkr,skr = genrepr a in // Could be inlined
  let keys = m_read rkeys in
  match find_key pkr keys with
  | Some _ -> gen a // retry until distinct. SZ: why not just throw an exception?
  | None ->
     let p = alloc_pubkey (Signed Seq.createEmpty) pkr in
     let k = (| a, p |) in
     let keys' = add_key keys k in
     m_write rkeys keys';
     witness rkeys (generated (|a, p|));
     p, skr


(* ------------------------------------------------------------------------ *)
val leak: #a:alg -> s:skey a -> ST (public_repr * secret_repr)
  (requires (fun _ -> True))
  (ensures  (fun h0 r h1 ->
	      modifies_one keyRegion h0 h1
	      /\ modifies_rref keyRegion !{as_ref (as_rref (PK.log (fst s)))} h0 h1
	      /\ is_Corrupt (m_sel h1 (PK.log (fst s)))
	      /\ fst r = PK.repr (fst s)))     
let leak #a (PK log pkr, skr) =
  m_write log Corrupt; 
  pkr, skr


(* ------------------------------------------------------------------------ *)
val coerce: #a:alg -> pkr:public_repr{sigAlg_of_public_repr pkr = a.core} -> skr:secret_repr{sigAlg_of_secret_repr skr = a.core} -> ST (skey a)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
           is_Corrupt (m_sel h1 (PK.log (fst s)))
           /\ PK.repr (fst s) = pkr
	   /\ snd s = skr))
let coerce #a pkr skr =
  alloc_pubkey Corrupt pkr, skr


(* ------------------------------------------------------------------------ *)
val endorse: #a:alg -> pkr:public_repr{sigAlg_of_public_repr pkr = a.core} -> ST pkey
  (requires (fun _ -> True))
  (ensures  (fun h0 k h1 -> 
	     pkey_repr k = pkr
             /\ (forall k'. generated k' h1 /\ pkey_repr k' = pkr ==> k = k')))
let endorse #a pkr =
  let keys = m_read rkeys in
  match find_key pkr keys with
  | Some k -> k
  | None   -> (| a, alloc_pubkey Corrupt pkr |)


#reset-options 
#set-options "--initial_fuel 2 --max_fuel 2 --detail_errors"

val test: bytes -> bytes -> All unit
      (requires (fun h -> m_contains rkeys h))
      (ensures (fun h0 _ h1 -> modifies (Set.singleton keyRegion) h0 h1))
let test t0 t1 =
  let a = Use (fun t -> True)
	      RSASIG
              [Hash SHA256; Hash SHA384]
              false
              false in
  let a' = Use (fun t -> t = t1)
              RSASIG
              [Hash SHA256]
              false
              false in
  let s = gen a in
  let s' = gen a' in
  let sigv0 = sign (Hash SHA256) s t0 in
  let sigv1 = sign (Hash SHA256) s t1 in
  //let sigv2 = sign (Hash SHA256) s' t0 in // should fail, can only sign t1
  ()
