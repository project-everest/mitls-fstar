(*--build-config
    options:--admit_fsi Set --admit_fsi Seq --admit_fsi CoreSig --admit_fsi CoreKeys --verify_module Key;
    variables:LIB=../../../../FStar/lib
              PLATFORM=../../../libs/fst/Platform
              CORECRYPTO=../../../libs/fs/CoreCrypto;
    other-files:$LIB/FStar.String.fst $LIB/FStar.Classical.fst $LIB/FStar.List.fst $LIB/FStar.FunctionalExtensionality.fst
                $LIB/FStar.Set.fsi $LIB/FStar.Heap.fst $LIB/FStar.ST.fst $LIB/FStar.MRef.fst
                $LIB/seq.fsi $LIB/FStar.SeqProperties.fst $PLATFORM/Bytes.fst
                $CORECRYPTO/CoreKeys.fsi $CORECRYPTO/CoreSig.fsi hash.fst
--*)
(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
(* an agile library for asymmetric keys covering their usage in PKI
   for signing (with various hashes), encrypting, and DH key
   exchanging, with dynamic key compromise.  *)

module Key

open Platform.Bytes
open Heap
open ST

(*** Key usage ***)

type group =
 | NamedIntMod of string
 | NamedCurve of string

type core =
 | RSA            // for signing & keyEncipher; the "size" is read off the keys.
 | Prime of group // for signing & keyExchange, covering both DSA and ECDSA

/// key algorithms & usage, from the secret owners' viewpoint (signing, decrypting, exponentiating)
type alg =
 | Use: info   : (bytes -> Type) // ``logical payload'' for signing; should be a type
     -> core   : core            // core algorithm
     -> digest : list Hash.alg   // can sign texts hashed by those algorithms
     -> keyEncipher: bool        // can encrypt e.g. PMS in TLS_RSA_WITH_...
     -> keyExchange: bool        // can be used to establish a Diffie-Hellman secret e.g. in TLS_DH...
     -> alg
 (* add some well-formedness refinement based on the algorithm, e.g. keyEncipher only with RSA? *)

val alg_group: a:alg { is_Prime (Use.core a) } -> g:group { Use.core a = Prime g }
let alg_group a =
 match Use.core a with
 | Prime g -> g


(*** Key representations ***)

type public_repr = CoreSig.sigpkey
(*
 | PK_RSA  of CoreKeys.rsapkey
 | PK_DSA  of CoreKeys.dsapkey
 | PK_ECDH of CoreKeys.ecdhpkey *)

type secret_repr = CoreSig.sigskey
(*  | SK_RSA  of CoreKeys.rsaskey
 | SK_DSA  of CoreKeys.dsaskey
 | SK_ECDH of CoreKeys.ecdhskey *)

type signed (a:alg) = t:bytes { Use.info a t }

(* TODO make key state an MRef? *)

type state (a:alg) =
// to support encryption and trusted keys, we will need an extra flag
//    { signed: list (signed a); (* all messages signed so far *)
//      honest: option bool;     (* None goes to either Some true or Some false *)
//    }
 | Signed of list (signed a)
 | Corrupt

val st_update: #a:alg -> state a -> signed a -> Tot (state a)
let st_update a st t =
 match st with
 | Signed ts -> Signed (t::ts)
 | Corrupt   -> Corrupt

(* precisely indexed public keys, with a partially-abstract type: the
  representation PK.repr is accessible; the private state PK.log is
  not. *)

type pubkey (a:alg) =
 | PK: log: ref (state a) -> repr: public_repr -> pubkey a

(* "packaged" public keys; functional, but
  but we need to know about a:alg to infer that it is secure *)

type pkey = ( a:alg & pubkey a ) //Use & for dependent tuple types
val pkey_repr: pkey -> Tot public_repr
let pkey_repr (| a,  p |) = PK.repr p

val honest: #a:alg -> state a -> GTot bool (* usable only in ghost code *)
let honest a = function
 | Signed _ -> true
 | Corrupt -> false

(* private keys, with an abstract type to keep their representation
  secret_repr private and bound to the indexed public key *)

type secret (a:alg) = pubkey a * secret_repr

val pk: #a:alg -> secret a -> Tot (pubkey a)
let pk a (p,s) = p

(* concrete key generation, currently provided by CoreSig to TLS;
  we could also inline & typecheck the multiplexing in CoreSig.gen *)

val genrepr: a:alg -> All (public_repr * secret_repr)
                         (requires (fun h -> True))
                         (ensures (fun h0 _ h1 -> h0=h1))
let genrepr a =
 CoreSig.gen
   (match Use.core a with
    | RSA                       -> CoreSig.CORE_SA_RSA (* implicitly 2048 bits *)
    | Prime(NamedIntMod "2048") -> CoreSig.CORE_SA_RSA (* implicitly 2048 bits *)
    | Prime(NamedCurve "p256")  -> CoreSig.CORE_SA_ECDSA
    | _                         -> failwith "unsupported algorithm") //this is in ML

(* we'll need the freshness of newly-generated logs within public keys,
  in order to show that operations do not modify the log of other keys *)

type fresh : #a:Type -> heap -> ref a -> heap -> Type =
 fun (a:Type) (h0:heap) (r:ref a) (h1:heap) ->
    (forall x. contains h0 x ==> r <> x) /\ contains h1 r

(* We rely on key-generation producing pairwise-distinct public keys
  with overwhelming probability. This follows from any crypto
  security assumptions, and most reasonable generation algorithm;
  we might not record keys generated with hopeless algorithms.

  We maintain this property as a stateful invariaint in rkeys *)

type kset = s: list pkey { forall x y. (List.mem x s /\ List.mem y s /\ pkey_repr x = pkey_repr y ==> x = y) }

val find_key: r:public_repr -> ks: kset ->
 Tot (o: (option (k:pkey {pkey_repr k = r && List.mem k ks}))
         { o = None ==> (forall k. List.mem k ks ==> not (pkey_repr k = r)) })
let rec find_key r ks = match ks with
 | []    -> None
 | k::ks -> if pkey_repr k = r then Some k else find_key r ks

val add_key: ks:kset -> k:pkey {forall k'. List.mem k' ks ==> ~ (pkey_repr k = pkey_repr k')} -> Tot kset
let add_key ks k = k::ks

// avoidable?
opaque logic type Mem (a:Type) (x:a) (xs:list a) = b2t (List.mem x xs)

opaque logic type mon_pkey (xs: kset) (xs':kset) =
 (forall x. List.mem x xs ==> List.mem x xs')

val rkeys: MRef.mref kset (mon_pkey)
let rkeys = MRef.alloc []

val alloc_pubkey:
 #a:alg -> s:state a -> r:public_repr -> ST (pubkey a)
 (requires (fun h0 -> True))
 (ensures (fun h0 p h1 -> sel h1 (PK.log p) = s
                       /\ PK.repr p = r
                       /\ fresh h0 (PK.log p) h1))
 (modifies no_refs)
let alloc_pubkey a s r = let log = ref s in PK log r

type generated (k:pkey) = MRef.token rkeys (Mem pkey k)

val gen: a:alg -> All (secret a)
                     (requires (fun h -> MRef.contains h rkeys))
                     (ensures (fun h0 (s:result (secret a)) h1 ->
                               Modifies (a_ref (MRef.as_ref rkeys)) h0 h1
                               /\ MRef.contains h1 rkeys
                               /\ (is_V s ==>
                                     generated (|a, pk (V.v s) |)
                                     /\ fresh h0 (PK.log (pk (V.v s))) h1
                                   )))
let rec gen a =
 let (pkr,skr) = genrepr a in
 let keys = MRef.read rkeys in
 match find_key pkr keys with
 | Some _ -> gen a (* retry until we pick a fresh public_repr *)
 | None ->
    let p = alloc_pubkey (Signed []) pkr in
    let k = (| a, p |) in
    let keys' = add_key keys k in
    MRef.write rkeys keys';
    MRef.witness rkeys (Mem pkey k);
    (p, skr)

val leak: #a:alg -> s:secret a -> ST (public_repr * secret_repr)
 (requires (fun _ -> True))
 (ensures (fun h0 r h1 -> sel h1 (PK.log (pk s)) = Corrupt && fst r = PK.repr (pk s)))
 (modifies (a_ref (PK.log (pk s))))
let leak a s =
 match s with
 | PK log pkr, skr -> log := Corrupt; (pkr, skr)

val coerce: #a:alg -> pkr:public_repr -> secret_repr -> ST (secret a)
 (requires (fun _ -> True))
 (ensures (fun h0 (s:secret a) h1 ->  //NS: Seem to need to annotate s ... not sure why. Investigate.
           sel h1 (PK.log (pk s)) = Corrupt
           && PK.repr (pk s) = pkr))
 (modifies no_refs)
let coerce a pkr skr = (alloc_pubkey Corrupt pkr, skr)

(* The adversary may coerce the representation of an honest public
  key, with the same index or not, but the resulting "fake" secret
  key will always be deemed Corrupt. *)

(* no need to provide functions for parsing and serializing public
  keys, as they are already available in CoreSig, CoreKeys, etc, but
  we still need to restore abstraction for "good", authenticated
  public keys, using some global lookup table.

  "endorse" guarantees that we retrieve any honestly-generated key
  from its representation; the first argument is just a default usage;
  in general one does not know the a:algo for an endorsed key.

  For serializing, we just use PK.repr then concrete code *)

val endorse: a:alg -> r:public_repr -> ST (pkey)
 (requires (fun _ -> True))
 (ensures (fun h0 k h1 -> pkey_repr k = r
      /\  (forall k'. Mem pkey k' (MRef.sel h1 rkeys) /\ pkey_repr k' = r ==> k = k'))) //NS: Do you expect this to be provable?
 (modifies no_refs)
let endorse a r =
 let keys = MRef.read rkeys in (* moving the read into "match ... with" causes a type error *)
 match find_key r keys with
 | Some k -> k
 | None   ->
  let k =  (| a, alloc_pubkey Corrupt r |) in
  let h1 = get () in //NS:admitting it for now, since the rest of the development requires it
  admitP  (forall k'. Mem pkey k' (MRef.sel h1 rkeys) /\ pkey_repr k' = r ==> k = k'); //NS: Do you expect this to be provable?
  k

(* ---------- basic testing ---------- *)

val test: unit -> All unit (requires (fun h -> MRef.contains h rkeys))
                          (ensures (fun h0 _ h1 -> Modifies (a_ref (MRef.as_ref rkeys)) h0 h1))
let test u =
 let a = Use (fun t -> True)
             (Prime(NamedCurve "p256"))
             [Hash.SHA256;Hash.SHA384]
             false
             false in

 let sk0 = gen a in
 let k0 =  (| a, pk sk0 |) in
 let sk1 = gen a in
 let r0 = PK.repr (pk sk0) in
 assert(generated k0);

 (* both r0 and this ghost property can be communicated,
    e.g. using a signed certificate that embeds r0 *)

 (* TODO can't make a closure here; related to abstraction loss? *)
 let k = endorse a r0 in
 MRef.recall rkeys (Mem pkey k0);
 let keys = MRef.read rkeys in
 assert(Mem pkey k0 keys);
 assert (k = k0)

(* How is this supposed to work? We know that gen registered the key
  in the past, that registration is stable, and that endorse returns
  the registered key with matching representation, if any. *)



               (* --------- comments and prior attempts ---------*)

(* witness/recall attempt; migrate to sample code *)

(*
// avoidable?
type Mem (a:Type) (x:a) (xs:list a) = b2t (List.mem x xs)

type mon (a:Type) (xs: list a) (xs':list a) =
   (forall x. (List.mem x xs ==> List.mem x xs'))

val r: mref (list int) (mon int)
let r = alloc []

val add: x:int -> u:unit { token r (Mem int x) }
let add x =
 write r (x::read r);
 witness r (Mem int x);
 ()

val test: unit -> St unit
                    (requires (fun _ -> True))
                    (ensures (fun _ _ h1 -> List.mem 1 (sel h1 r)))
let test_recall =
 let t1 = add 1 in
 (fun () -> recall (list int) (mon int) (Mem int 1) r)  (* failing with implicit args *)
*)

(* Plan B if recallable statetul properties are awkward to callers:

  We have a specification-only function that maps public key
  representations to their "generated" public key, if any

  We define this function pointwise; to guarantee
  its consistency, we maintain its already-defined domain
  in a table, with a "not-defined-before" precondition. *)

(* A variant we considered:

  - the cert log stores tokens, rather than formulas;
  - Use.info is any stable heap-based property,
    required for signing, ensured by verification

  For it to work in general, we'd need tokens for the heap
  (or a part of the heap), not a particular ref. *)
