﻿module MiTLS.HMAC

open MiTLS.Hashing.Spec // for the algorithm names, instead of CoreCrypt
open MiTLS.Mem
friend Lib.IntTypes

open FStar.HyperStack.ST

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

(* Parametric keyed HMAC; could be coded up from two HASH calls. *)

let hmac a k m =
  let h00 = get() in
  push_frame();
  let lt = Hacl.Hash.Definitions.hash_len a in
  let lk = Bytes.len k in
  let bk = LowStar.Buffer.alloca 0uy lk in
  Bytes.store_bytes k bk;
  let bt = LowStar.Buffer.alloca 0uy lt in
  let lm = Bytes.len m in

  if lm = 0ul then (
    let bm = LowStar.Buffer.null in
    let h0 = get() in
    Seq.lemma_eq_intro (Bytes.reveal m) (LowStar.Buffer.as_seq h0 bm);
    EverCrypt.HMAC.compute a bt bk lk bm lm
  )
  else (
    let h0 = get() in
    push_frame();
    let bm = LowStar.Buffer.alloca 0uy lm in
    Bytes.store_bytes m bm;
    EverCrypt.HMAC.compute a bt bk lk bm lm;
    pop_frame();
    let h1 = get() in
    assert(LowStar.Modifies.(modifies (loc_buffer bt) h0 h1))
    );

  let t = Bytes.of_buffer lt bt in
  Hacl.HMAC.key_and_data_fits a;
  assert(Bytes.reveal t == Spec.Agile.HMAC.hmac a (Bytes.reveal k) (Bytes.reveal m));
  assert(t = Hashing.Spec.hmac a k m);
  pop_frame();
  let h11 = HyperStack.ST.get() in
  //18-09-01 todo, as in Hashing.compute
  assert(LowStar.Modifies.(modifies loc_none h00 h11));
  assume(modifies_none h00 h11); //18-09-12 missing compatibility lemma?
  t

//18-09-02 TODO lower code to avoid bytes-allocating the tag.

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
