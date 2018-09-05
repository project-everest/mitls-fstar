module HMAC

open Hashing.Spec // for the algorithm names, instead of CoreCrypt
open Mem

open FStar.HyperStack.ST
open FStar.Bytes

let ha = EverCrypt.HMAC.ha 

type key = bytes
// type mac (a:macAlg) = lbytes32 (macSize a)
//18-02-25 should instead be derived from Hashing

type text (a:alg) = macable a

(* Parametric keyed HMAC; could be coded up from two HASH calls. *)

(*
// bytes input but uses a buffer for the resulting tag
private val hmac0:
  a:ha -> 
  k:hkey a -> 
  m: macable a -> 
  bt: LowStar.Buffer.buffer UInt8.t {LowStar.Buffer.length bt = tagLength a} -> 
  Stack unit
  (requires fun h0 -> LowStar.Buffer.live h0 bt)
  (ensures fun h0 () h1 -> 
    LowStar.Buffer.as_seq h1 bt == Bytes.reveal (Hashing.Spec.hmac a k m) /\
    LowStar.Modifies.(modifies (loc_buffer bt) h0 h1))

let hmac0 a k m bt = 
  let h00 = HyperStack.ST.get() in 
  push_frame(); 
  let h0 =  HyperStack.ST.get() in 
  let lt = EverCrypt.Hash.tagLen a in
  let bk = LowStar.Buffer.alloca 0uy lt in 
  store_bytes k bk;
  assert_norm(EverCrypt.HMAC.keysized a (tagLength a));

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
  pop_frame();
  assume False

val hmac: 
  a:ha -> 
  k:hkey a -> 
  m: macable a -> 
  Stack (t:tag a {t == Hashing.Spec.hmac a k m})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
  // TODO add functional spec to crypto proof 
  
let hmac a k m = 
  let h00 = HyperStack.ST.get() in 
  push_frame(); 
  let lt = EverCrypt.Hash.tagLen a in
  let bt = LowStar.Buffer.alloca 0uy lt in
  hmac0 a k m bt; 
  let t = of_buffer lt bt in
  pop_frame();
  let h11 = HyperStack.ST.get() in 
  assume(HyperStack.modifies Set.empty h00 h11);
  // assume(t = Hashing.Spec.hmac a k m);
  t

val hmac_verify: 
  a:ha -> 
  k:hkey a -> 
  m: macable a -> 
  t:tag a -> 
  Stack (b:bool {b = (t = Hashing.Spec.hmac a k m)})
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
*)

val hmac:
  a:ha -> 
  k:hkey a -> 
  m: macable a -> 
  Stack (tag a)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> 
    modifies Set.empty h0 h1 /\
    t = Hashing.Spec.hmac a k m)

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
  //assume(HyperStack.modifies Set.empty h00 h11);
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


/// Agile bytes-friendly MAC function

type macable = b:bytes {length b + 128 < pow2 32} // [==> pre of hmac for all algorithms]

val tls_mac: a: 
  tls_macAlg -> 
  k: tag a  -> 
  msg:macable -> 
  ST (tag a)
  (requires fun h0 -> True)
  (ensures fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1)
let tls_mac a k msg  = hmac a k msg

val tls_macVerify: 
  a:tls_macAlg -> 
  k: tag a  -> 
  msg:macable -> 
  tag a -> 
  ST bool
  (requires fun h0 -> True)
  (ensures (fun h0 t h1 -> FStar.HyperStack.modifies Set.empty h0 h1))
let tls_macVerify a k d t = hmacVerify a k d t

