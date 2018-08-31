module HMAC

open Hashing.Spec // for the algorithm names, instead of CoreCrypt
open Mem

open FStar.HyperStack.ST
open FStar.Bytes

open TLSConstants

type key = bytes
type mac (a:macAlg) = lbytes32 (macSize a)
//18-02-25 should instead be derived from Hashing

type text (a:alg) = macable a

(* Parametric keyed HMAC; could be coded up from two HASH calls. *)

val hmac: a:EverCrypt.HMAC.ha -> k:hkey a -> m: macable a -> 
  Stack (t:tag a {t == Hashing.Spec.hmac a k m})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
  // TODO add functional spec to crypto proof 

let hmac a k m = 
  let h00 = HyperStack.ST.get() in 
  push_frame(); 
  let lt = EverCrypt.Hash.tagLen a in
  let bk = LowStar.Buffer.alloca 0uy lt in 
  store_bytes k bk;
  assert_norm(EverCrypt.HMAC.keysized a (tagLength a));

  let bt = LowStar.Buffer.alloca 0uy lt in
  let lm = Bytes.len m in 

  if lm = 0ul then (
    let bm = LowStar.Buffer.null in 
    EverCrypt.HMAC.compute a bt bk lt bm lm
  )
  else (
    push_frame();
    let bm = LowStar.Buffer.alloca 0uy lm in 
    store_bytes m bm;
    EverCrypt.HMAC.compute a bt bk lt bm lm;
    pop_frame()
    );
  assume False;//18-09-01 not sure what's broken
    
  let t = of_buffer lt bt in
  pop_frame();
  let h11 = HyperStack.ST.get() in 
  //18-09-01 todo, as in Hashing.compute
  assume(HyperStack.modifies Set.empty h00 h11);
  t

//#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

// consider providing it only in UFCMA
val hmacVerify: a:alg -> k:hkey a -> m:macable a -> t: tag a -> ST (b:bool {b <==> (t == Hashing.Spec.hmac a k m)})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))

let hmacVerify a k p t =
  let result = hmac a k p in
  result = t


(* Historical constructions from SSL, still used in TLS 1.0, not that different from HMAC *)

(* SSL/TLS constants *)

private let ssl_pad1_md5  = create 48ul 0x36z
private let ssl_pad2_md5  = create 48ul 0x5cz
private let ssl_pad1_sha1 = create 40ul 0x36z
private let ssl_pad2_sha1 = create 40ul 0x5cz

(* SSL3 keyed hash *)
type sslHashAlg = h:hashAlg { h = Hash MD5 \/ h = Hash SHA1 }
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


(* Agile MAC function *)

val tls_mac: a: macAlg -> k:lbytes32 (macKeySize a) -> msg:bytes -> ST (mac a)
  (requires fun h0 -> match a with HMac a | SSLKHash a -> length msg + blockLength a <= maxLength a)
  (ensures fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1)
let tls_mac a k msg  =
    match a with
    | HMac     a -> hmac a k msg
    | SSLKHash a -> sslKeyedHash a k msg

val tls_macVerify: a:macAlg -> k:lbytes32 (macKeySize a) -> msg:bytes -> mac a -> ST bool
  (requires fun h0 -> match a with HMac a | SSLKHash a -> length msg + blockLength a <= maxLength a)
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
let tls_macVerify a k d t =
    match a with
    | HMac alg -> hmacVerify alg k d t
    | SSLKHash alg -> sslKeyedHashVerify alg k d t
