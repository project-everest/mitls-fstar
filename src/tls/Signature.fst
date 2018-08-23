module Signature

open FStar.HyperStack.All
open FStar.Monotonic.Seq
open FStar.Bytes

open Mem
open CoreCrypto
open Hashing.Spec // masking CoreCrypto's hashAlg
open TLSConstants
open Cert

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(* ------------------------------------------------------------------------ *)
type text = bytes

(** REMARK: this needs to be in Type0 because `ref a : Type0` and we build a ref to
    a set of `pkey a = (a:alg & pubkey a)`
*)
noeq type alg: Type0 =
  | Use: info:(text -> GTot bool)
       -> core: sigAlg
       -> digest: list hashAlg
       -> keyEncipher: bool // can encrypt e.g. PMS in TLS_RSA_WITH_...
       -> keyExchange: bool // can be used to establish a DH secret e.g. in TLS_DH_...
       -> alg

type signed (a:alg) = t:text{a.info t}

// Could be finer, but we lack lengths in CoreCrypto signature functions
type sigv (a:alg) = bytes

// Encodes agile INT-CMA assumption
assume type int_cma_assumption: a:alg -> h:hashAlg{List.Tot.mem h a.digest} -> Tot bool

// Erase CMA assumption at extraction
inline_for_extraction let int_cma (a:alg) (h:hashAlg{List.Tot.mem h a.digest}) : Tot bool =
  if Flags.ideal_Sig then int_cma_assumption a h
  else false

type public_repr =
  | PK_RSA: rsa_key -> bool -> public_repr
  | PK_DSA of dsa_key
  | PK_ECDSA of ec_key

type secret_repr =
  | SK_RSA: k:rsa_key{has_priv (KeyRSA k)} -> bool -> secret_repr
  | SK_DSA   of k:dsa_key{has_priv (KeyDSA k)}
  | SK_ECDSA of k:ec_key{has_priv (KeyECDSA k)}

let sigAlg_of_secret_repr sk =
  match sk with
  | SK_RSA _ true  -> RSAPSS
  | SK_RSA _ false -> RSASIG
  | SK_DSA _       -> DSA
  | SK_ECDSA _     -> ECDSA

let sigAlg_of_public_repr pk =
  match pk with
  | PK_RSA _ true  -> RSAPSS
  | PK_RSA _ false -> RSASIG
  | PK_DSA _       -> DSA
  | PK_ECDSA _     -> ECDSA

private val sig_digest: hashAlg -> bytes -> ST (option CoreCrypto.hash_alg * bytes)
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies Set.empty h0 h1))
let sig_digest h t =
  match h with
  | NULL    -> None, t
  | MD5SHA1 -> None, Hashing.compute_MD5SHA1 t
  | Hash h  -> Some (Hashing.OpenSSL.toCC h), t  // CF: ugly conversion between hashAlgs.


(* ------------------------------------------------------------------------ *)
noeq type state (a:alg) =
  | Signed: log:Seq.seq (signed a) -> state a
  | Corrupt

(**
  Allowed state transitions:
  Corrupt  -> Corrupt
  Signed l -> Corrupt
  Signed l -> Signed l++l'
*)
abstract let evolves (#a:alg) (s1:state a) (s2:state a) =
  Corrupt? s2 \/
  (Signed? s1 /\ Signed? s2 /\ grows (Signed?.log s1) (Signed?.log s2))

(*18-02-10 
let lemma_evolves_monotone (#a:alg): Lemma (monotonic (state a) (evolves #a)) =
  FStar.Classical.forall_intro (seq_extension_reflexive #(signed a));
  FStar.Classical.forall_intro_3 (grows_transitive #(signed a))
*)
 
private val st_update: #a:alg
  -> s1:state a
  -> signed a
  -> Tot (s2:state a{evolves s1 s2})
let st_update #a st t =
  match st with
  | Signed ts -> lemma_snoc_extends ts t; Signed (snoc ts t)
  | Corrupt   -> Corrupt


(* ------------------------------------------------------------------------ *)

let keyRegion:rgn = new_region tls_region

type log_t (a:alg) = m_rref keyRegion (state a) evolves

noeq type pubkey (a:alg) =
  | PK: log:log_t a
      -> repr:public_repr{sigAlg_of_public_repr repr == a.core}
      -> pubkey a

type pkey = (a:alg & pubkey a)

val pkey_repr: pkey -> Tot public_repr
let pkey_repr (|a,p|) = PK?.repr p

val pkey_alg: pkey -> Tot alg
let pkey_alg (|a,_|) = a

type skey (a:alg) =
  k:(pubkey a * secret_repr){let _,sk = k in sigAlg_of_secret_repr sk == a.core}

val alloc_pubkey: #a:alg
  -> s:state a
  -> r:public_repr{sigAlg_of_public_repr r == a.core}
  -> ST (pubkey a)
    (requires (fun h0 -> True))
    (ensures  (fun h0 p h1 -> ralloc_post keyRegion s h0 (PK?.log p) h1
                           /\ PK?.repr p == r
                           ))
let alloc_pubkey #a s r =
  // lemma_evolves_monotone #a;
  let log = HST.ralloc keyRegion s in
  PK log r


(* ------------------------------------------------------------------------ *)
(* We rely on key-generation producing pairwise-distinct public keys
  with overwhelming probability. This follows from any crypto
  security assumptions, and most reasonable generation algorithms;
  we might not record keys generated with hopeless algorithms.

  We maintain this property as a stateful invariaint in rkeys *)

type kset =
  s:list pkey{ forall x y. (List.Tot.memP x s /\ List.Tot.memP y s /\ pkey_repr x == pkey_repr y) ==> x == y }

val find_key: r:public_repr -> ks:kset
  -> Tot (o:option pkey{
         match o with
         | None   -> forall k. List.Tot.memP k ks ==> ~(pkey_repr k == r)
         | Some k -> pkey_repr k == r /\ List.Tot.memP k ks})
let rec find_key r ks = match ks with
  | []   -> None
  | k::ks -> if pkey_repr k = r then Some k else find_key r ks


type mon_pkey (xs:kset) (xs':kset) =
  forall x. List.Tot.memP x xs ==> List.Tot.memP x xs'

val add_key: ks:kset
  -> k:pkey { forall k'. List.Tot.memP k' ks ==> ~(pkey_repr k == pkey_repr k') }
  -> Tot (ks':kset{ks' == k::ks /\ ks `mon_pkey` ks' /\ List.Tot.memP k ks'})
let add_key ks k = k::ks

// FIXME: top-level effect
val rkeys: m_rref keyRegion kset (mon_pkey)
let rkeys = HST.ralloc keyRegion []

type generated (k:pkey) (h:mem) : Type0 = List.Tot.memP k (sel h rkeys)


(* ------------------------------------------------------------------------ *)

val sign: #a:alg
  -> h:hashAlg{List.Tot.mem h (a.digest)}
  -> s:skey a
  -> t:signed a
  -> ST (sigv a)
    (requires (fun h0 -> True))
    (ensures  (fun h0 _ h1 ->
      let pk,sk = s in
      if int_cma a h then
        let log = PK?.log pk in
        modifies_one keyRegion h0 h1 /\
        HS.modifies_ref keyRegion (Set.singleton (Heap.addr_of (as_ref log))) h0 h1 /\
        sel h1 log == st_update (sel h0 log) t
      else modifies Set.empty h0 h1))

let sign #a h s t =
  let pk,sk = s in
  begin
  if int_cma a h then
    let log = PK?.log pk in
    let s0 = HST.op_Bang log in
    HST.recall log;
    HST.op_Colon_Equals log (st_update s0 t)
  end;
  let ho,t' = sig_digest h t in
  match sk with
  | SK_RSA k b -> rsa_sign ho k b t'
  | SK_DSA k   -> dsa_sign ho k t'
  | SK_ECDSA k -> ecdsa_sign ho k t'


(* ------------------------------------------------------------------------ *)
val verify: #a:alg
  -> h:hashAlg{List.Tot.mem h (a.digest)}
  -> pk:pubkey a
  -> t:text
  -> sigv a
  -> ST bool
    (requires (fun h0 -> True))
    (ensures  (fun h0 b h1 ->
         modifies Set.empty h0 h1
       /\ ((b /\ int_cma a h /\ generated (|a,pk|) h0
       /\ Signed? (sel h0 (PK?.log pk))) ==> a.info t)))

let verify #a h pk t s =
  let h0 = get() in
  let log = PK?.log pk in
  HST.recall log;
  let verified =
    let ho,t' = sig_digest h t in
    match PK?.repr pk with
    | PK_RSA k b -> rsa_verify ho k b t' s
    | PK_DSA k   -> dsa_verify ho k t' s
    | PK_ECDSA k -> ecdsa_verify ho k t' s
  in
  let h1 = get() in
  if int_cma a h then
    begin
    match HST.op_Bang (PK?.log pk) with
    | Signed ts ->
      begin
      let keys = HST.op_Bang rkeys in
      let signed = Some? (Seq.seq_find (fun (t':signed a) -> t = t') ts) in
      let find_pk pk' = pkey_repr pk' = PK?.repr pk in
      let honest = List.Tot.existsb find_pk keys in
      List.Tot.memP_existsb find_pk keys;
      if honest then verified && signed
      else
        begin
        assert (find_pk (|a, pk|));
        assert (~(List.Tot.memP (|a,pk|) keys));
        verified
        end
      end
    | Corrupt -> verified
    end
  else verified


(* ------------------------------------------------------------------------ *)
val genrepr: a:alg
  -> HyperStack.All.All (public_repr * secret_repr)
    (requires (fun h -> True))
    (ensures  (fun h0 k h1 ->
      modifies Set.empty h0 h1 /\
      (V? k ==>
        (let (pk,sk) = V?.v k in
   	    sigAlg_of_public_repr pk == sigAlg_of_secret_repr sk
	  /\ sigAlg_of_public_repr pk == a.core))))

let genrepr a =
  match a.core with
  | RSAPSS -> let k = rsa_gen_key 2048 in (PK_RSA k true, SK_RSA k true)
  | RSASIG -> let k = rsa_gen_key 2048 in (PK_RSA k false, SK_RSA k false)
  | DSA    -> let k = dsa_gen_key 1024 in (PK_DSA k, SK_DSA k)
  | ECDSA  -> let k = ec_gen_key ({curve = ECC_P256; point_compression = false}) in (PK_ECDSA k, SK_ECDSA k)

val gen: a:alg -> All (skey a)
  (requires (fun h -> h `contains` rkeys))
  (ensures  (fun h0 (s:result (skey a)) h1 ->
	         modifies_one keyRegion h0 h1
               /\ HS.modifies_ref keyRegion (Set.singleton (Heap.addr_of (as_ref rkeys))) h0 h1
               /\ h1 `contains` rkeys
	       /\ (V? s ==>   witnessed (generated (| a, fst (V?.v s) |))
			   /\ Signed? (sel h1 (PK?.log (fst (V?.v s)))))))

#set-options "--z3rlimit 40"

let rec gen a =
  let pkr,skr = genrepr a in // Could be inlined
  let keys = HST.op_Bang rkeys in
  match find_key pkr keys with
  | Some _ -> gen a // retry until distinct. SZ: why not just throw an exception?
  | None ->
    let p = alloc_pubkey (Signed Seq.empty) pkr in
    let k = (| a, p |) in
    let keys' = add_key keys k in
    HST.op_Colon_Equals rkeys keys';
    mr_witness rkeys (generated (| a, p |));
    p, skr

#set-options "--z3rlimit 20"


(* ------------------------------------------------------------------------ *)
val leak: #a:alg -> s:skey a -> ST (public_repr * secret_repr)
  (requires (fun _ -> True))
  (ensures  (fun h0 r h1 ->
	      modifies_one keyRegion h0 h1
	      /\ HS.modifies_ref keyRegion (Set.singleton (Heap.addr_of (as_ref (PK?.log (fst s))))) h0 h1
	      /\ Corrupt? (sel h1 (PK?.log (fst s)))
	      /\ fst r == PK?.repr (fst s)))
let leak #a (PK log pkr, skr) =
  HST.recall log;
  HST.op_Colon_Equals log Corrupt;
  pkr, skr


(* ------------------------------------------------------------------------ *)
val coerce: #a:alg -> pkr:public_repr{sigAlg_of_public_repr pkr == a.core} -> skr:secret_repr{sigAlg_of_secret_repr skr == a.core} -> ST (skey a)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
           Corrupt? (sel h1 (PK?.log (fst s)))
           /\ PK?.repr (fst s) == pkr
	   /\ snd s == skr))
let coerce #a pkr skr =
  alloc_pubkey Corrupt pkr, skr


val endorse: #a:alg -> pkr:public_repr{sigAlg_of_public_repr pkr == a.core} -> ST pkey
  (requires (fun _ -> True))
  (ensures  (fun h0 k h1 ->
	     pkey_alg k == a
	     /\ pkey_repr k = pkr
             /\ (forall k'. generated k' h1 /\ pkey_repr k' = pkr /\ pkey_alg k' == a ==> (dfst k == dfst k' /\
	                                                                            PK?.repr (dsnd k) == PK?.repr (dsnd k'))))) //AR: 04/27: we don't get equality of refs anymore, we can get their addresses are equal, if we can show that one of them is contained in the heap
let endorse #a pkr =
  let keys = HST.op_Bang rkeys in
  match find_key pkr keys with
  | Some k ->
    if (pkey_alg k).core = a.core then begin
      assume (pkey_alg k == a);  //AR: 05/10: adding it to ensure postcondition, the code below relies on it
      k
    end
    else (| a, alloc_pubkey Corrupt pkr |)
  | None   -> (| a, alloc_pubkey Corrupt pkr |)


(* ------------------------------------------------------------------------ *)
val get_chain_public_key: #a:alg -> list Cert.cert -> St (option (pubkey a))
let get_chain_public_key #a c =
  let sa = a.core in
  match c with
  | cert::_ ->
    begin
    match sa, CoreCrypto.get_key_from_cert cert with
    | RSAPSS, Some (KeyRSA k)   ->
      let (|_,pk|) = endorse #a (PK_RSA k true) in
      Some pk
    | RSASIG, Some (KeyRSA k)   ->
      let (|_,pk|) = endorse #a (PK_RSA k false) in
      Some pk
    | DSA,    Some (KeyDSA k)   ->
      let (|_,pk|) = endorse #a (PK_DSA k) in
      Some pk
    | ECDSA,  Some (KeyECDSA k) ->
      let (|_,pk|) = endorse #a (PK_ECDSA k) in
      Some pk
    | _, _ -> None
    end
  | _ -> None


(* ------------------------------------------------------------------------ *)
// FIXME: use unique public-key representation

private val foo: o:option (k:CoreCrypto.key{has_priv k}) -> Tot (option CoreCrypto.key)
let foo o = match o with | None -> None | Some k -> Some k

#reset-options "--z3rlimit 100"
val lookup_key: #a:alg -> string -> ST (option (skey a))
  (requires (fun _ -> True))
  (ensures  (fun h0 o h1 ->
    match o with
    | Some (p, skr) ->
      modifies_one keyRegion h0 h1 /\
      HS.modifies_ref keyRegion (Set.singleton (Heap.addr_of (as_ref rkeys))) h0 h1 /\
      witnessed (generated (|a,p|))
    | None -> h0 == h1))
let lookup_key #a keyfile =
  let keys = HST.op_Bang rkeys in
  let sa = a.core in
  let key =
    match sa, foo (CoreCrypto.load_key keyfile) with
    | RSAPSS, Some (KeyRSA k)   -> Some (PK_RSA k true, SK_RSA k true)
    | RSASIG, Some (KeyRSA k)   -> Some (PK_RSA k false, SK_RSA k false)
    | DSA,    Some (KeyDSA k)   -> Some (PK_DSA k, SK_DSA k)
    | ECDSA,  Some (KeyECDSA k) -> Some (PK_ECDSA k, SK_ECDSA k)
    | _, _ -> None
  in
  match key with
  | Some (pkr, skr) ->
    begin
    match find_key pkr keys with
    | Some (| a', p |) ->
      if a'.core = a.core then // if a' = a then // Not computable in extracted code
      begin
        assume (a == a');  //AR: 05/10: relying on equality of alg
        mr_witness rkeys (generated (|a, p|));
        Some (p, skr)
      end
      else
        None
    | None ->
      begin
      let p = alloc_pubkey (Signed Seq.empty) pkr in
      let k = (| a, p |) in
      let keys' = add_key keys k in
      HST.recall rkeys;
      HST.op_Colon_Equals rkeys keys';
      mr_witness rkeys (generated k);
      Some (p, skr)
      end
    end
  | None -> None


#reset-options
#set-options "--initial_fuel 2 --max_fuel 2"

noextract // why?
val test: bytes -> bytes -> All unit
  (requires (fun h -> h `contains` rkeys))
  (ensures  (fun h0 _ h1 -> modifies_one keyRegion h0 h1))
let test t0 t1 =
  let a = Use (fun t -> true)
	      RSASIG
              [Hash SHA256; Hash SHA384]
              false
              false in
  let a' = Use (fun t -> t = t1)
              RSASIG
              [Hash SHA256]
              false
              false in
  let s  = gen a in
  let s' = gen a' in
  let sigv0 = sign (Hash SHA256) s t0 in
  let sigv1 = sign (Hash SHA256) s t1 in
  //let sigv2 = sign (Hash SHA256) s' t0 in // should fail, can only sign t1
  ()
