module IV

open Mem
open Pkg

module B = FStar.Bytes
module M = LowStar.Modifies
module DT = DefineTable
module U32 = FStar.UInt32

/// A sample functionality for fresh, public initialization vectors,
/// with the length of the byte vector as a basic agility
/// parameter. We use this functionality e.g. for generating the
/// static IV for TLS AEAD as part of the TLS key schedule.
///
/// There is no need for an idealization flag: the main (unconditional)
/// property is that the vector is a function of the index; this
/// vector is fresh whenever create is called instead of coerce.

type idealRaw = b2t Flags.flag_Raw
type valid_len (ip:ipkg) = i:ip.t -> keylen -> Type

type info (#ip:ipkg) (lid:valid_len ip) (i:ip.t) =
  len:keylen{lid i len}

type raw (#ip:ipkg) (lid:valid_len ip) (i:regid ip) =
  b:B.bytes{let l = B.len b in
  0 < U32.v l /\ U32.v l <= 255 /\ lid i l}

noextract inline_for_extraction
let create_raw (#ip:ipkg) (lid:valid_len ip) (i:regid ip) (len:info lid i)
  : ST (raw lid i)
  (requires fun h0 -> model)
  (ensures fun h0 p h1 -> B.len p == len /\
    M.modifies M.loc_none h0 h1 /\
    fresh_loc M.loc_none h0 h1)
  = Random.sample32 len

noextract
let coerceT_raw (#ip:ipkg) (lid:valid_len ip)
  (i: regid ip{idealRaw ==> ~(ip.honest i)})
  (len:info lid i) (r:Bytes.lbytes32 len)
  : GTot (raw lid i) 
  = r

inline_for_extraction
let coerce_raw (#ip: ipkg) (lid:valid_len ip)
  (i: regid ip{idealRaw ==> ~(ip.honest i)})
  (len: info lid i) (r: Bytes.lbytes32 len):
  ST (raw lid i)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> B.len k == len /\
    k == coerceT_raw lid i len r /\
    M.modifies M.loc_none h0 h1)
  = r

inline_for_extraction noextract
let local_raw_pkg (#ip:ipkg) (lid:valid_len ip)
  : Pure (local_pkg ip)
  (requires True) (ensures fun p -> LocalPkg?.key p == raw lid)
  =
  LocalPkg
    (raw lid)
    (info lid)
    (fun #i k -> B.len k)
    (fun #i a -> a)
    idealRaw
    (DT.empty_fp (raw lid))
    (fun #_ _ _ -> True) // no invariant
    (fun #_ _ _ _ _ -> ())
    (create_raw lid)
    (coerceT_raw lid)
    (coerce_raw lid)

inline_for_extraction noextract
let rp (ip:ipkg) (lid:valid_len ip)
  : ST (pkg ip)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 ->
    Pkg?.key p == raw lid /\
    p == memoization (local_raw_pkg lid) p.define_table /\
    p.package_invariant h1 /\
    fresh_loc (DT.loc p.define_table) h0 h1)
  =
  memoization_ST (local_raw_pkg lid)

val discard: bool -> ST unit
  (requires (fun _ -> True))  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s : ST unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> h0 == h1)
  = discard (IO.debug_print_string ("IV | "^s^"\n"))

private type id = n:nat {n < 256}

inline_for_extraction noextract
private let ip : ipkg = Pkg.Idx id (fun _ -> True) (fun _ -> True) (fun _ -> true)

inline_for_extraction noextract
private let id_len (i:id) (a:keylen) =
  if i > 0 && i < 32 then U32.v a == i else a == 32ul

let test() : ST unit
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)
  =
  assume (model == false);
  let kl : keylen = 12ul in
  let k = Bytes.create 12ul 0uy in
  print (Bytes.hex_of_bytes k);

  [@inline_let] let p = local_raw_pkg #ip id_len in
  let v0 = LocalPkg?.coerce p 12 kl k in
  print (Bytes.hex_of_bytes v0);

  let dt = DT.alloc p.key in
  let h = get() in
  [@inline_let] let q = memoization p dt in
  DT.lemma_footprint_empty dt p.local_footprint h;
  DT.lemma_forall_empty dt p.inv h;
  let v1 = Pkg?.coerce q 12 kl k in
  print (Bytes.hex_of_bytes v1);
  ()
