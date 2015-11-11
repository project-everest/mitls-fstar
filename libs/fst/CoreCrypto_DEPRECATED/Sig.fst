module CoreCrypto.Sig
(* -------------------------------------------------------------------- *)
open Platform.Bytes

(* -------------------------------------------------------------------- *)
type sighash =
| SH_MD5
| SH_SHA1
| SH_SHA256
| SH_SHA384

type sigalg =
| CORE_SA_RSA
| CORE_SA_DSA

(* -------------------------------------------------------------------- *)
type sigskey =
| SK_RSA of CoreCrypto.Keys.rsaskey
| SK_DSA of CoreCrypto.Keys.dsaskey
| SK_ECDH of CoreCrypto.Keys.ecdhskey

type sigpkey =
| PK_RSA of CoreCrypto.Keys.rsapkey
| PK_DSA of CoreCrypto.Keys.dsapkey
| PK_ECDH of CoreCrypto.Keys.ecdhpkey

assume val sigalg_of_skey : sigskey -> sigalg
assume val sigalg_of_pkey : sigpkey -> sigalg

(* -------------------------------------------------------------------- *)
type text = bytes
type sigv = bytes

assume val gen    : sigalg -> sigpkey * sigskey
assume val sign   : option sighash -> sigskey -> text -> sigv
assume val verify : option sighash -> sigpkey -> text -> sigv -> bool
