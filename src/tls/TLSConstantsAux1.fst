module TLSConstantsAux1

(* Start Hacks *)
// assume val empty_bytes : FStar.Bytes.lbytes 0
(* End Hacks *)
open FStar.String
open FStar.Seq
open FStar.Date
open FStar.Bytes
open FStar.Error
open TLSError
//open CoreCrypto // avoid?!

(** Protocol version negotiated values *)
type protocolVersion' =
  | SSL_3p0 // supported, with no security guarantees
  | TLS_1p0
  | TLS_1p1
  | TLS_1p2
  | TLS_1p3
  | UnknownVersion: a:byte -> b:byte{a <> 3z \/ (b <> 0z /\ b <> 1z /\ b <> 2z /\ b <> 3z /\ b <> 4z)} -> protocolVersion'

type protocolVersion = pv:protocolVersion'{~(UnknownVersion? pv)}
