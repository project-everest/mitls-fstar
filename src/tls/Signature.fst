module Signature

open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open FStar.Monotonic.Seq

open Platform.Bytes
open CoreCrypto

open TLSConstants
open Cert

(* ------------------------------------------------------------------------ *)
type text = bytes

// ADL(31/10/16): changing info from text -> Type0 to text -> GTot bool
// to ensure that alg is in universe 0
// (this is needed because ref a now requires a to be in universe 0)
noeq type alg : Type0 =
  | Use: info:(text -> GTot bool)
       -> core: sigAlg
       -> digest: list hashAlg
       -> keyEncipher: bool // can encrypt e.g. PMS in TLS_RSA_WITH_...
       -> keyExchange: bool // can be used to establish a Diffie-Hellman secret e.g. in TLS_DH_... SZ: Do we care about static (EC)DH?
       -> alg

type signed (a:alg) = t:text{a.info t}

// Could be finer, but we lack lengths in CoreCrypto signature functions
type sigv (a:alg) = bytes

// Encodes agile INT-CMA assumption
assume type int_cma: a:alg -> h:hashAlg{List.Tot.mem h a.digest} -> Tot bool

type public_repr =
  | PK_RSA   of rsa_key
  | PK_DSA   of dsa_key
  | PK_ECDSA of ec_key

type secret_repr =
  | SK_RSA   of k:rsa_key{has_priv (KeyRSA k)}
  | SK_DSA   of k:dsa_key{has_priv (KeyDSA k)}
  | SK_ECDSA of k:ec_key{has_priv (KeyECDSA k)}

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
  | MD5SHA1 -> None, Hashing.hash h t
  | Hash h  -> Some h, t


(* ------------------------------------------------------------------------ *)
noeq type state (a:alg) =
  | Signed: log:Seq.seq (signed a) -> state a
  | Corrupt

(*
  Allowed state transitions:
  Corrupt  -> Corrupt
  Signed l -> Corrupt
  Signed l -> Signed l++l'
*)
abstract let evolves (#a:alg) (s1:state a) (s2:state a) =
  Corrupt? s2 \/
  (Signed? s1 /\ Signed? s2 /\ grows (Signed?.log s1) (Signed?.log s2))

let lemma_evolves_monotone (#a:alg): Lemma (monotonic (state a) (evolves #a)) =
  FStar.Classical.forall_intro (seq_extension_reflexive #(signed a));
  FStar.Classical.forall_intro_3 (grows_transitive #(signed a))

private val st_update: #a:alg
  -> s1:state a
  -> signed a
  -> Tot (s2:state a{evolves s1 s2})
let st_update #a st t =
  match st with
  | Signed ts -> lemma_snoc_extends ts t; Signed (snoc ts t)
  | Corrupt   -> Corrupt


(* ------------------------------------------------------------------------ *)

(*
 * AR: this was rid, is TLSConstants.rgn ok ?
 *)
assume val keyRegion: TLSConstants.rgn

type log_t (a:alg) = m_rref keyRegion (state a) evolves

type pubkey (a:alg) =
  | PK: log:log_t a -> repr:public_repr{sigAlg_of_public_repr repr = a.core} -> pubkey a

type pkey = (a:alg & pubkey a)

val pkey_repr: pkey -> Tot public_repr
let pkey_repr (| a,  p |) = PK?.repr p

val pkey_alg: pkey -> Tot alg
let pkey_alg (| a,  _ |) = a

type skey (a:alg) =
  k:(pubkey a * secret_repr){let _,sk = k in sigAlg_of_secret_repr sk = a.core}

val alloc_pubkey: #a:alg
  -> s:state a
  -> r:public_repr{sigAlg_of_public_repr r = a.core}
  -> ST (pubkey a)
    (requires (fun h0 -> True))
    (ensures  (fun h0 p h1 -> ralloc_post keyRegion s h0 (as_hsref (PK?.log p)) h1
                           /\ PK?.repr p = r
                           /\ m_fresh (PK?.log p) h0 h1))
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

// ADL(31/10/16): I am a bit concerned by pkey_repr x = pkey_repr y in kset;
// after extraction this becomes pointer equality on wrapped OpenSSL pointers
// we should export a normalized, hasEq representation of keys in CoreCrypto.

// AD(31/10/16): Commenting out the hasEq assumption on alg; instead we use memT
(* AR: this needs to be fixed, alg should not have hasEq because of info *)
// FIXME in CoreCrypto!
assume HasEq_public_repr: hasEq public_repr

(** ADL: FIXME XXX relies on StrongExcludedMiddle! *)
assume val strong_excluded_middle : p:Type0 -> GTot (b:bool{b = true <==> p})
private let rec memT (#a:Type0) (v:a) (l:list a) : GTot bool =
  match l with
  | [] -> false
  | h::t -> if strong_excluded_middle (h == v) then true else memT v t

type kset = s:list pkey{ forall x y. (memT x s /\ memT y s /\ pkey_repr x = pkey_repr y) ==> x == y }

val find_key: r:public_repr -> ks: kset
  -> Tot (o:option (k:pkey {pkey_repr k = r && memT k ks})
        { None? o ==> (forall k. memT k ks ==> pkey_repr k <> r) })
let rec find_key r ks = match ks with
  | []   -> None
  | k::ks -> if pkey_repr k = r then Some k else find_key r ks

val add_key: ks:kset
  -> k:pkey { forall k'. memT k' ks ==> pkey_repr k <> pkey_repr k' }
  -> Tot kset
let add_key ks k = k::ks

logic type mon_pkey (xs:kset) (xs':kset) =
  forall x. memT x xs ==> memT x xs'

// FIXME: top-level effect
val rkeys: m_rref keyRegion kset (mon_pkey)
let rkeys = m_alloc keyRegion []

type generated (k:pkey) (h:mem) : Type0 = memT k (m_sel h rkeys)

let honestKey (#a:alg) (k:pubkey a) (ks:kset) =
  let PK _ pk = k in
  Some? (find_key pk ks)

(* ------------------------------------------------------------------------ *)

(*
 * AR: adding m_recall to satify the precondition of m_write.
 *)
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
	let log_ashsref = as_hsref log in
        modifies_one keyRegion h0 h1 /\
        modifies_rref keyRegion !{as_ref log_ashsref} h0.h h1.h /\
        m_sel h1 log == st_update (m_sel h0 log) t
      else modifies Set.empty h0 h1))

let sign #a h s t =
  let pk,sk = s in
  begin
  if int_cma a h then
    let log = PK?.log pk in
    let s0 = m_read log in
    m_recall log;
    m_write log (st_update s0 t)
  end;
  let ho,t' = sig_digest h t in
  match sk with
  | SK_RSA k   -> rsa_sign ho k t'
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
	   /\ Signed? (m_sel h0 (PK?.log pk))) ==> a.info t)))

let verify #a h pk t s =
  let verified =
    let ho,t' = sig_digest h t in
    match PK?.repr pk with
    | PK_RSA k   -> rsa_verify ho k t' s
    | PK_DSA k   -> dsa_verify ho k t' s
    | PK_ECDSA k -> ecdsa_verify ho k t' s
  in
  if int_cma a h then
    begin
    assume False;
    match m_read (PK?.log pk) with
    | Signed ts ->
      let signed = Some? (Seq.seq_find (fun (t':signed a) -> t = t') ts) in
      let honest = honestKey pk (m_read rkeys) in
      verified && (signed || not honest)
    | Corrupt -> verified
    end
  else verified


(* ------------------------------------------------------------------------ *)
val genrepr: a:alg
  -> All (public_repr * secret_repr)
    (requires (fun h -> True))
    (ensures  (fun h0 k h1 ->
      V? k ==>
      (let (pk,sk) = V?.v k in
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
               /\ modifies_rref keyRegion !{as_ref (as_hsref rkeys)} h0.h h1.h
               /\ m_contains rkeys h1
	       /\ (V? s ==>   witnessed (generated (| a, fst (V?.v s) |))
			     /\ m_fresh (PK?.log (fst (V?.v s))) h0 h1
			     /\ Signed? (m_sel h1 (PK?.log (fst (V?.v s)))))))

#set-options "--z3rlimit 40"

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
    witness rkeys (generated (| a, p |));
    p, skr

#set-options "--z3rlimit 20"

(* ------------------------------------------------------------------------ *)

(*
 * AR: adding m_recall for log to satisfy the precondition of m_write.
 *)
val leak: #a:alg -> s:skey a -> ST (public_repr * secret_repr)
  (requires (fun _ -> True))
  (ensures  (fun h0 r h1 ->
	      modifies_one keyRegion h0 h1
	      /\ modifies_rref keyRegion !{as_ref (as_hsref (PK?.log (fst s)))} h0.h h1.h
	      /\ Corrupt? (m_sel h1 (PK?.log (fst s)))
	      /\ fst r = PK?.repr (fst s)))
let leak #a (PK log pkr, skr) =
  m_recall log;
  m_write log Corrupt;
  pkr, skr


(* ------------------------------------------------------------------------ *)
val coerce: #a:alg -> pkr:public_repr{sigAlg_of_public_repr pkr = a.core} -> skr:secret_repr{sigAlg_of_secret_repr skr = a.core} -> ST (skey a)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
           Corrupt? (m_sel h1 (PK?.log (fst s)))
           /\ PK?.repr (fst s) = pkr
	   /\ snd s = skr))
let coerce #a pkr skr =
  alloc_pubkey Corrupt pkr, skr


(* ------------------------------------------------------------------------ *)

// ADL: FIXME XXX unsound because of info
assume HasEq_alg_unsound: hasEq alg

val endorse: #a:alg -> pkr:public_repr{sigAlg_of_public_repr pkr = a.core} -> ST pkey
  (requires (fun _ -> True))
  (ensures  (fun h0 k h1 ->
	     pkey_alg k == a
	     /\ pkey_repr k = pkr
             /\ (forall k'. generated k' h1 /\ pkey_repr k' = pkr /\ pkey_alg k' == a ==> k = k')))
let endorse #a pkr =
  let keys = m_read rkeys in
  match find_key pkr keys with
  | Some k ->
    if pkey_alg k = a then k
    else (| a, alloc_pubkey Corrupt pkr |)
  | None   -> (| a, alloc_pubkey Corrupt pkr |)


(* ------------------------------------------------------------------------ *)
val get_chain_public_key: #a:alg -> chain -> St (option (pubkey a))
let get_chain_public_key #a c =
  let sa = a.core in
  match c with
  | cert::_ ->
    begin
    match sa, CoreCrypto.get_key_from_cert cert with
    | RSASIG, Some (KeyRSA k)   ->
      let (|_,pk|) = endorse #a (PK_RSA k) in
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
//FIXME: use unique public-key representation

val foo: o:option (k:CoreCrypto.key{has_priv k}) -> Tot (option CoreCrypto.key)
let foo o = match o with | None -> None | Some k -> Some k

(*
 * AR: adding recall for rkeys to satisfy the precondition of m_write.
 *)
val lookup_key: #a:alg -> string -> St (option (skey a))
let lookup_key #a keyfile =
  let keys = m_read rkeys in
  let sa = a.core in
  let key =
    match sa, foo (CoreCrypto.load_key keyfile) with
    | RSASIG, Some (KeyRSA k)   -> Some (PK_RSA k, SK_RSA k)
    | DSA,    Some (KeyDSA k)   -> Some (PK_DSA k, SK_DSA k)
    | ECDSA,  Some (KeyECDSA k) -> Some (PK_ECDSA k, SK_ECDSA k)
    | _, _ -> None
  in
  match key with
  | Some (pkr, skr) ->
    begin
    match find_key pkr keys with
    | Some (| a', p |) -> if a' = a then Some (p, skr) else None
    | None ->
      let p = alloc_pubkey (Signed Seq.createEmpty) pkr in
      let k = (| a, p |) in
      let keys' = add_key keys k in
      m_recall rkeys;
      m_write rkeys keys';
      witness rkeys (generated (|a, p|));
      Some (p, skr)
    end
  | None -> None

(*
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
*)
