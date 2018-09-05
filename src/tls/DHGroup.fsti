module DHGroup

module B = FStar.Bytes
module HST = FStar.HyperStack.ST

type ffdhe =
  | FFDHE2048
  | FFDHE3072
  | FFDHE4096
  | FFDHE6144
  | FFDHE8192

type params = {
  dh_p : b:B.bytes{B.length b < 65536};
  dh_g : b:B.bytes{B.length b < 65536};
  dh_q : option (b:B.bytes{B.length b < 65536});
  safe_prime : bool;
}

type group =
  | Named    of ffdhe
  | Explicit of params

val params_of_group: group -> Tot params

type share (g:group) = b:B.bytes{
  1 <= B.length b /\ B.length b < 65536 /\
  (let dhp = params_of_group g in B.length b <= B.length dhp.dh_p)}

val keyshare: group -> eqtype

type secret (g:group) = B.bytes

val pubshare: #g:group -> keyshare g -> Tot (share g)

val keygen: g:group -> HST.ST (keyshare g)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> HST.modifies_none h0 h1))

val dh_initiator: #g:group -> keyshare g -> share g -> HST.ST (secret g)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> HST.modifies_none h0 h1))

val serialize: #g:group -> share g -> Tot B.bytes

val serialize_public: #g:group -> s:share g -> l:nat{l < 65536 /\ B.length s <= l} -> Tot (B.lbytes l)

val parse_partial: FStar.Bytes.bytes -> Tot (TLSError.result ((g:group & share g) * B.bytes))
