(*--build-config
    options:--admit_fsi Set --admit_fsi Seq --admit_fsi CoreSig --admit_fsi CoreKeys --verify_module Hash --verify_module Key --verify_module Sig;
    variables:LIB=../../../../FStar/lib
              PLATFORM=../../../libs/fst/Platform
              CORECRYPTO=../../../libs/fs/CoreCrypto;
    other-files:$LIB/FStar.String.fst $LIB/FStar.Classical.fst $LIB/FStar.List.fst $LIB/FStar.FunctionalExtensionality.fst
                $LIB/FStar.Set.fsi $LIB/FStar.Heap.fst $LIB/FStar.ST.fst $LIB/FStar.MRef.fst
                $LIB/seq.fsi $LIB/FStar.SeqProperties.fst $PLATFORM/Bytes.fst
                $CORECRYPTO/CoreKeys.fsi $CORECRYPTO/CoreSig.fsi hash.fst key.fst
--*)
(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)
module Sig

open Bytes
open Heap
open ST
open Key

(* we might also reconcile CoreSig.sighash with alg *)
(* private *)
val coreSig_digest: h:Hash.alg -> t:bytes -> Tot (option CoreSig.sighash * bytes)
let coreSig_digest h t =
  match h with
  | Hash.NULL    -> None, t                   (* broken for large texts *)
  | Hash.MD5SHA1 -> None, Hash.compute Hash.MD5SHA1 t (* TLS-specific *)
  | Hash.MD5     -> Some CoreSig.SH_MD5, t
  | Hash.SHA     -> Some CoreSig.SH_SHA1, t
  | Hash.SHA256  -> Some CoreSig.SH_SHA256, t
  | Hash.SHA384  -> Some CoreSig.SH_SHA384, t

assume val taglength: alg -> Tot nat
type tag (a:alg) = bytes
// should be lbytes (taglength a) (* needs to move to CoreSig? *)

// modelling our crypto-agile security assumptions
assume val int_cma: a:alg -> h:Hash.alg -> Tot bool

val sign: #a:alg -> h:Hash.alg { List.mem h (Use.digest a) } ->
  s:secret a -> text:signed a -> ST (tag a)
    (requires (fun h -> true))
    (ensures (fun h0 _ h1 -> let log = PK.log (pk s) in
              Heap.sel h1 log = st_update (Heap.sel h0 log) text))
    (modifies (a_ref (PK.log (pk s))))

let sign a h s t =
  let log = PK.log (pk s) in
  log := st_update !log t;
  let (h', t') = coreSig_digest h t in
  CoreSig.sign h' (snd s) t'
  (* arguably this call should be inlined & precisely typechecked here. *)

val verify: #a:alg -> h:Hash.alg ->
  p:pubkey a -> text:bytes -> tag a ->
  ST bool
     (requires (fun h -> true))
     (ensures (fun h0 b h1 -> (b && int_cma a h && honest (Heap.sel h0 (PK.log p))) ==> Use.info a text))
     (modifies no_refs)

val finder: a:alg -> t:bytes -> t':signed a -> Tot bool
let finder a t t' = (t = t')

let verify a h p t v =
  let verified =
    let (h', t') = coreSig_digest h t in
    (* arguably this call should be inlined & typechecked here. *)
    CoreSig.verify h' (PK.repr p) t' v in
  let signed =
    match !(PK.log p) with
    | Signed ts -> is_Some (List.find (finder a t) ts)
    | Corrupt   -> true in
  verified && (signed || not (int_cma a h))

opaque logic type trivial (t:bytes) = True
opaque logic type eq_bytes (t:bytes) (t':bytes) = t=t'

val test: bytes -> bytes -> All unit
      (requires (fun h -> MRef.contains h rkeys))
      (ensures (fun h0 _ h1 -> Modifies (a_ref (MRef.as_ref rkeys)) h0 h1))
let test t0 t1 =
  let a = Use trivial //NS: ... silly; will fix. the inlined function is not interpreted as a predicate ... (fun t -> True) // b2t(t = t0))
              (Prime(NamedCurve "p256"))
              [Hash.SHA256;Hash.SHA384]
              false
              false in
  let a' = Use (eq_bytes t1) //NS: silly; will fix. inlined function not a predicate yet ... (fun t -> b2t(t = t1)) //
              (Prime(NamedCurve "p256"))
              [Hash.SHA256]
              false
              false in
  let s = gen a in

  cut(Use.info a t0);
  let tag0 = sign Hash.SHA256 s t0 in (* should succeed?? *)
  let tag1 = sign Hash.SHA256 s t1 in (* should fail ... NS: why? it succeeds*)
//  let tag2 = sign #a' Hash.SHA256 s t0 in (* should fail ... NS: yes, it does *)
  ()


(* for convenience in TLS, we may define
   functions specialized to TLSConstants/Info, e.g.

let rsa (info: bytes -> Type) =
  RSA *
    { info = info;
      digest = [ SHA; SHA256; SHA384 ];
      keyEncipher = false;
      keyExchange = false }

let rsa_sign info h (s: Key.secret (rsa info)) text = sign h s text
 *)

(*
module RSAPMS

open Bytes
// todo: TLS-specific assumption

type index
type pms: #a:alg -> p:pubkey a -> index -> Type
type cipher = bytes

val encrypt: #a:alg -> p:pubkey a -> i:index -> pms p i * cipher
val decrypt: #a:alg -> s:secret a -> i:index -> cipher -> pms p i


module DiffieHellman

open Bytes
// todo: n-ary decisional Diffie-Hellman assumption

val share: #a:alg { is_Prime a.core && a.usage.keyExchange } -> pubkey a -> element (alg_group a)

 *)
