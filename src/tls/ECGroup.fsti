module ECGroup

module B = FStar.Bytes
module HST = FStar.HyperStack.ST

type group = EverCrypt.ec_curve

let bytelen (g:group) : n:nat{n <= 127} =
  match g with
  | EverCrypt.ECC_P256 -> 32
  | EverCrypt.ECC_P384 -> 48
  | EverCrypt.ECC_P521 -> 66
  | EverCrypt.ECC_X25519 -> 32
  | EverCrypt.ECC_X448 -> 56

type point (g:group) = {
  ecx : B.lbytes (bytelen g);
  ecy : B.lbytes (bytelen g);
}

private val _key: group -> eqtype

private type pre_keyshare g =
  | KS_CC: point g -> _key g -> pre_keyshare g
  | KS_X25519 of TLS.Curve25519.keyshare
  | KS_X448: pub:B.lbytes 56 -> priv:B.lbytes 56 -> pre_keyshare g

type keyshare (g:group) =
  s:pre_keyshare g{(
    match g with
    | EverCrypt.ECC_X25519 -> KS_X25519? s
    | EverCrypt.ECC_X448   -> KS_X448? s
    | _ -> KS_CC? s)}

private type pre_share g =
  | S_CC of point g
  | S_X25519 of TLS.Curve25519.point
  | S_X448 of B.lbytes 56

type share (g:group) =
  s:pre_share g{(match g with
    | EverCrypt.ECC_X25519 -> S_X25519? s
    | EverCrypt.ECC_X448 -> S_X448? s
    | _ -> S_CC? s)}

type secret (g:group) = B.lbytes (bytelen g)

val pubshare: #g:group -> keyshare g -> Tot (share g)

val keygen: g:group -> HST.ST (keyshare g)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> HST.modifies_none h0 h1))

val dh_initiator: #g:group -> gx:keyshare g -> gy:share g -> HST.ST (secret g)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> HST.modifies_none h0 h1))

val parse_point: g:group -> B.bytes -> Tot (option (share g))

val parse_partial: B.bytes -> Tot (TLSError.result ((g:group & share g) * B.bytes))

val serialize_point: #g:group -> e:share g -> Tot (r:B.bytes{1 <= B.length r /\ B.length r <= 255})

val serialize: #g:group -> e:share g -> Tot B.bytes
