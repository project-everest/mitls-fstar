(* -------------------------------------------------------------------- *)
open Bytes

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
| SK_RSA of CoreKeys.rsaskey
| SK_DSA of CoreKeys.dsaskey

type sigpkey =
| PK_RSA of CoreKeys.rsapkey
| PK_DSA of CoreKeys.dsapkey

val sigalg_of_skey : sigskey -> sigalg
val sigalg_of_pkey : sigpkey -> sigalg

(* -------------------------------------------------------------------- *)
type text = bytes
type sigv = bytes

val gen    : sigalg -> sigpkey * sigskey
val sign   : sighash option -> sigskey -> text -> sigv
val verify : sighash option -> sigpkey -> text -> sigv -> bool
