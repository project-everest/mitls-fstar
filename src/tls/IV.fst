module IV

open Mem
open Pkg



/// A sample functionality for fresh, public initialization vectors,
/// with the length of the byte vector as a basic agility
/// parameter. We use this functionality e.g. for generating the
/// static IV for TLS AEAD as part of the TLS key schedule.
///
/// There is no need for an idealization flag: the main (unconditional)
/// property is that the vector is a function of the index; this
/// vector is fresh whenever create is called instead of coerce.
type idealRaw = b2t Flags.flag_Raw

// SZ: [len_of_i] was implicit, but it can't be inferred from [i]. Made it explicit
type rawlen (#ip:ipkg) (len_of_i:ip.t -> keylen) (i:ip.t) = len:keylen {len == len_of_i i}

type raw (ip:ipkg) (len_of_i:ip.t -> keylen) (i:ip.t{ip.registered i}) = Bytes.lbytes32 (len_of_i i)

noextract
let shared_footprint_raw (ip:ipkg) (len_of_i:ip.t -> keylen): rset = Set.empty

noextract
let footprint_raw (ip:ipkg) (len_of_i:ip.t -> keylen)
  (#i:ip.t {ip.registered i}) (k:raw ip len_of_i i)
  : GTot (s:rset{s `Set.disjoint` shared_footprint_raw ip len_of_i})
  =
  let fp = Set.empty in
  let sfp = shared_footprint_raw ip len_of_i in
  Set.lemma_equal_elim (fp `Set.intersect` sfp) Set.empty;
  fp

inline_for_extraction
let create_raw (ip:ipkg) (len_of_i:ip.t -> keylen)
  (i:ip.t{ip.registered i}) (len:keylen {len = len_of_i i}):
  ST (raw ip len_of_i i)
  (requires fun h0 -> model)
  (ensures fun h0 p h1 -> modifies_none h0 h1)
  = Random.sample32 len

let coerceT_raw (ip:ipkg) (len_of_i:ip.t -> keylen)
  (i: ip.t {ip.registered i /\ (idealRaw ==> ~(ip.honest i))})
  (len:keylen{len == len_of_i i}) (r: Bytes.lbytes32 len):
  GTot (raw ip len_of_i i) = r

inline_for_extraction
let coerce_raw (ip: ipkg) (len_of_i: ip.t -> keylen)
  (i: ip.t {ip.registered i /\ (idealRaw ==> ~(ip.honest i))})
  (len:keylen {len == len_of_i i}) (r: Bytes.lbytes32 len):
  ST (raw ip len_of_i i)
  (requires fun h0 -> True)
  (ensures fun h0 k h1 -> k == coerceT_raw ip len_of_i i len r /\ modifies_none h0 h1)
  = r

noextract
inline_for_extraction
let local_raw_pkg (ip:ipkg) (len_of_i:ip.t -> keylen) : local_pkg ip =
  LocalPkg
    (raw ip len_of_i)
    (rawlen #ip len_of_i)
    (fun #i (n:rawlen len_of_i i) -> n)
    idealRaw
    (shared_footprint_raw ip len_of_i)
    (footprint_raw ip len_of_i)
    (fun #_ _ _ -> True) // no invariant
    (fun _ _ _ _ _ -> ())
    (fun #_ _ _ _ -> True) // no post-condition
    (fun #_ _ _ _ _ _ -> ())
    (create_raw ip len_of_i)
    (coerceT_raw ip len_of_i)
    (coerce_raw ip len_of_i)

noextract inline_for_extraction
let rp (ip:ipkg) (len_of_i:ip.t -> keylen): ST (pkg ip)
  (requires fun h0 -> True)
  (ensures fun h0 p h1 -> modifies_one tls_define_region h0 h1 /\ p.package_invariant h1)
  =
  memoization_ST (local_raw_pkg ip len_of_i)

// does this extract? 18-09-24 no

val discard: bool -> ST unit
  (requires (fun _ -> True))  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s : ST unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> h0 == h1)
  = discard (IO.debug_print_string ("IV | "^s^"\n"))

private type id = n:nat {n < 256}

inline_for_extraction
noextract
private let ip : ipkg = Pkg.Idx id (fun _ -> True) (fun _ -> True) (fun _ -> true)

private let len_of_i (i:id): keylen = UInt32.uint_to_t i

let test() : ST unit
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> True)
  =
  assume (model == false);
  let kl : keylen = 12ul in
  let k = Bytes.create 12ul 0uy in
  print (Bytes.hex_of_bytes k);

  [@inline_let]
  let p = local_raw_pkg ip len_of_i in
  let v0 = LocalPkg?.coerce p 12 kl k in
  print (Bytes.hex_of_bytes v0);

  let table = mem_alloc (fun n -> Bytes.lbytes n) in
  [@inline_let]
  let q = Pkg.memoization p table in
  let v1 = Pkg?.coerce q 12 kl k in
  print (Bytes.hex_of_bytes v1);
  ()
