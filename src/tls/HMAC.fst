module HMAC

open Hashing.Spec // for the algorithm names, instead of CoreCrypt
open Mem

open FStar.HyperStack.ST
module B = FStar.Bytes
module LB = LowStar.Buffer

let ha = EverCrypt.HMAC.ha 

(* Parametric keyed HMAC; could be coded up from two HASH calls. *)

val hmac:
  a:ha -> 
  k:hkey a -> 
  m: macable a -> 
  ST (tag a)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> 
    modifies_none h0 h1 /\ // FIXME this is now wrong
    t = Hashing.Spec.hmac a k m)

#set-options "--z3rlimit 20"
let hmac a k m = 
  let h00 = get() in 
  push_frame(); 
  let lt = EverCrypt.Hash.tagLen a in
  let lk = B.len k in
  let bk = LB.alloca 0uy lk in 
  B.store_bytes k bk;
  let bt = LB.alloca 0uy lt in
  let lm = B.len m in 

  if lm = 0ul then (
    B.empty_unique m;
    EverCrypt.HMAC.compute a bt bk lk LB.null lm;
    let h1 = get() in
    assume(LB.as_seq h1 bt == B.reveal (Hashing.Spec.hmac a k m))
  ) else (
    push_frame();
    let bm = LB.alloca 0uy lm in 
    B.store_bytes m bm;
    EverCrypt.HMAC.compute a bt bk lk bm lm;
    pop_frame()
  );

  let h2 = get() in
  assert(LB.as_seq h2 bt == B.reveal (Hashing.Spec.hmac a k m));
  let t = B.of_buffer lt bt in
  pop_frame();
  let h11 = get() in
  assume(modifies_none h00 h11); // FIXME
  t

//18-09-02 TODO lower code to avoid bytes-allocating the tag. 

val hmacVerify: a:ha -> k:hkey a -> m:macable a -> t: tag a -> ST (b:bool {b <==> (t == Hashing.Spec.hmac a k m)})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let hmacVerify a k p t =
  let result = hmac a k p in
  result = t

/// Historical constructions from SSL, still used in TLS 1.0, actually
/// just HMAC. Disable in this version of the code.
(*
(* SSL/TLS constants *)

private let ssl_pad1_md5  = create 48ul 0x36z
private let ssl_pad2_md5  = create 48ul 0x5cz
private let ssl_pad1_sha1 = create 40ul 0x36z
private let ssl_pad2_sha1 = create 40ul 0x5cz

(* SSL3 keyed hash *)
type sslHashAlg = h:tls_alg { h = Hash MD5 \/ h = Hash SHA1 }
val sslKeyedHashPads: sslHashAlg -> Tot(bytes * bytes)
let sslKeyedHashPads = function
    | Hash MD5 -> (ssl_pad1_md5, ssl_pad2_md5)
    | Hash SHA1 -> (ssl_pad1_sha1, ssl_pad2_sha1)

private val sslKeyedHash: 
  a:alg {a=MD5 \/ a=SHA1} -> 
  k:hkey a -> text a -> ST (tag a)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> modifies_none h0 h1)
let sslKeyedHash a k p =
    let (inner, outer) = 
      match a with 
      | MD5 -> ssl_pad1_md5, ssl_pad2_md5
      | SHA1 -> ssl_pad1_sha1, ssl_pad2_sha1 in

    //18-08-31 TODO 4x hashable bounds
    assume(False);
    let h = Hashing.compute a (k @| inner @| p) in
    Hashing.compute a (k @| outer @| h)

private val sslKeyedHashVerify: 
  a:alg {a=MD5 \/ a=SHA1} -> 
  k:hkey a -> text a -> t:tag a -> ST bool 
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> modifies Set.empty h0 h1)
let sslKeyedHashVerify a k p t =
    let res = sslKeyedHash a k p in
    res=t
*)

(*** Old TLS 1.2 HMAC ***)

/// Agile bytes-friendly MAC function

type macable = b:B.bytes {B.length b + 128 < pow2 32} // [==> pre of hmac for all algorithms]

val tls_mac: a: 
  tls_macAlg -> 
  k: hkey a  -> 
  msg:macable -> 
  ST (tag a)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1)
let tls_mac a k msg  = hmac a k msg

val tls_macVerify: 
  a:tls_macAlg -> 
  k: hkey a  -> 
  msg:macable -> 
  tag a -> 
  ST bool
  (requires fun h0 -> True)
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
let tls_macVerify a k d t = hmacVerify a k d t

