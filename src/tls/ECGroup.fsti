module ECGroup

open CoreCrypto

module B = FStar.Bytes
module HST = FStar.HyperStack.ST

type group = ec_curve

private type pre_keyshare g =
  | KS_CC of k:ec_key {
    Some? k.ec_priv /\ k.ec_params.curve = g /\
    B.length k.ec_point.ecx = ec_bytelen g /\
    B.length k.ec_point.ecy = ec_bytelen g }
  | KS_X25519 of TLS.Curve25519.keyshare
  | KS_X448 of (pub:B.lbytes 56 * priv:B.lbytes 56)

// ADL do not use untagged union here!
// The ML Obj.t type is not compatible with CC extracted as --codegen-lib
type keyshare (g:group) =
  s:pre_keyshare g{(
    match g with
    | ECC_X25519 -> KS_X25519? s
    | ECC_X448   -> KS_X448? s
    | _             -> KS_CC? s)}

private type pre_share g =
  | S_CC of p:ec_point{
     B.length p.ecx = ec_bytelen g /\
     B.length p.ecy = ec_bytelen g}
  | S_X25519 of TLS.Curve25519.point
  | S_X448 of B.lbytes 56

type share (g:group) =
  s:pre_share g{(match g with
    | ECC_X25519 -> S_X25519? s
    | ECC_X448 -> S_X448? s
    | _ -> S_CC? s)}

type secret (g:group) = B.bytes

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
