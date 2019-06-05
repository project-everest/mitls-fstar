module IV

open Mem
open Pkg

module M = LowStar.Modifies
module DT = DefineTable

/// A sample functionality for fresh, public initialization vectors,
/// with the length of the byte vector as a basic agility
/// parameter. We use this functionality e.g. for generating the
/// static IV for TLS AEAD as part of the TLS key schedule.
///
/// There is no need for an idealization flag: the main (unconditional)
/// property is that the vector is a function of the index; this
/// vector is fresh whenever create is called instead of coerce.

type idealRaw = b2t Flags.flag_Raw
type len_of_id (ip:ipkg) = i:ip.t{model} -> keylen

// SZ: [len_of_i] was implicit, but it can't be inferred from [i]. Made it explicit
type rawlen (#ip:ipkg) (lid:len_of_id ip) (i:ip.t) = len:keylen {model ==> len == lid i}
type raw (#ip:ipkg) (lid:len_of_id ip) (i:ip.t{ip.registered i}) = Bytes.bytes
//  b:Bytes.bytes{model ==> Bytes.len b == lid i}

noextract inline_for_extraction
let create_raw (#ip:ipkg) (lid:len_of_id ip)
  (i:ip.t{ip.registered i}) (len:rawlen lid i):
  ST (raw lid i)
  (requires fun h0 -> model /\ lid i == len)
  (ensures fun h0 p h1 -> M.modifies M.loc_none h0 h1 /\
    fresh_loc M.loc_none h0 h1)
  = Random.sample32 len

let coerceT_raw (#ip:ipkg) (lid:len_of_id ip)
  (i: ip.t {ip.registered i /\ (idealRaw ==> ~(ip.honest i))})
  (len:rawlen lid i) (r:Bytes.lbytes32 len)
  : GTot (raw lid i) 
  = r

inline_for_extraction
let coerce_raw (#ip: ipkg) (lid:len_of_id ip)
  (i: ip.t {ip.registered i /\ (idealRaw ==> ~(ip.honest i))})
  (len:rawlen lid i) (r: Bytes.lbytes32 len):
  ST (raw lid i)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> k == coerceT_raw lid i len r /\
    M.modifies M.loc_none h0 h1)
  = r

noextract
inline_for_extraction
let local_raw_pkg (#ip:ipkg) (lid:len_of_id ip)
  : Pure (local_pkg ip)
  (requires True) (ensures fun p -> LocalPkg?.key p == raw lid)
  =
  LocalPkg
    (raw lid)
    (rawlen lid)
    (fun (i:ip.t{model}) -> lid i)
    (fun #i (n:rawlen lid i) -> n)
    idealRaw
    (DT.empty_fp (raw lid))
    (fun #_ _ _ -> True) // no invariant
    (fun #_ _ _ _ _ -> ())
    (create_raw lid)
    (coerceT_raw lid)
    (coerce_raw lid)

noextract inline_for_extraction
let rp (ip:ipkg) (lid:len_of_id ip): ST (pkg ip)
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

inline_for_extraction
noextract
private let ip : ipkg = Pkg.Idx id (fun _ -> True) (fun _ -> True) (fun _ -> true)

private let len_of_i  (i:id): keylen =
  if i > 0 && i < 32 then UInt32.uint_to_t i
  else 32ul

let test() : ST unit
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)
  =
  assume (model == false);
  let kl : keylen = 12ul in
  let k = Bytes.create 12ul 0uy in
  print (Bytes.hex_of_bytes k);

  [@inline_let]
  let p = local_raw_pkg #ip len_of_i in
  let v0 = LocalPkg?.coerce p 12 kl k in
  print (Bytes.hex_of_bytes v0);
  
  let q = rp ip len_of_i in
  let v1 = Pkg?.coerce q 12 kl k in
  print (Bytes.hex_of_bytes v1);
  ()
